const express = require('express');
const https = require('https');
const http = require('http');
const fs = require('fs');
const dns = require('dns');
const { URL } = require('url');

const app = express();

// Parse bodies (tolerante)
app.use(express.json({ limit: '5mb' }));
app.use(express.text({ type: 'text/*', limit: '5mb' }));
app.use(express.raw({ type: 'application/octet-stream', limit: '5mb' }));
app.use(express.urlencoded({ extended: true, limit: '5mb' }));

// Env vars
const SERVICE_TOKEN = process.env.SERVICE_TOKEN || '';
const TARGET_URL = process.env.NFE_TARGET_URL || '';
const CERT_PATH = process.env.CERT_PATH || '/certs/client.crt';
const KEY_PATH = process.env.KEY_PATH || '/certs/client.key';
const CA_PATH = process.env.CA_PATH || '';
const PORT = process.env.PORT || 8080;
const TIMEOUT_MS = parseInt(process.env.TIMEOUT_MS || '30000', 10);
const ALLOWED_HOSTS = process.env.ALLOWED_HOSTS || '';

// Block non-http(s) protocols
function isHttpProtocol(urlObj) {
  return urlObj.protocol === 'http:' || urlObj.protocol === 'https:';
}

// Headers to remove (hop-by-hop + our auth header)
const HOP_BY_HOP_HEADERS = [
  'connection',
  'keep-alive',
  'proxy-authenticate',
  'proxy-authorization',
  'proxy-connection',
  'te',
  'trailer',
  'transfer-encoding',
  'upgrade',
  'host',
  'content-length',
  'x-service-token',
];

// Helper: clean headers
function cleanHeaders(headers) {
  const cleaned = {};
  for (const [key, value] of Object.entries(headers || {})) {
    const lowerKey = key.toLowerCase();
    if (!HOP_BY_HOP_HEADERS.includes(lowerKey)) cleaned[key] = value;
  }
  return cleaned;
}

// Prepare body for forwarding (Buffer / string / JSON)
function prepareBody(body) {
  if (body == null) return null;

  // Buffers
  if (Buffer.isBuffer(body)) return body;

  // ArrayBuffer / Uint8Array
  if (body instanceof ArrayBuffer) return Buffer.from(body);
  if (ArrayBuffer.isView(body)) return Buffer.from(body.buffer, body.byteOffset, body.byteLength);

  if (typeof body === 'string') return body;

  if (typeof body === 'object') {
    if (Object.keys(body).length === 0) return null;
    return JSON.stringify(body);
  }

  return null;
}

// Allowed hosts
function getAllowedHosts() {
  if (!ALLOWED_HOSTS) return null;
  return ALLOWED_HOSTS
    .split(',')
    .map(h => h.trim().toLowerCase())
    .filter(Boolean);
}

function isHostAllowed(hostname) {
  const allowedHosts = getAllowedHosts();
  if (!allowedHosts) return false;

  const normalized = String(hostname || '').toLowerCase();
  return allowedHosts.some(allowed => {
    if (normalized === allowed) return true;
    if (allowed.startsWith('*.')) {
      const base = allowed.slice(2);
      return normalized === base || normalized.endsWith('.' + base);
    }
    return false;
  });
}

// --- Private IP checks (fail-closed) ---
function ipv4ToNumber(ip) {
  const parts = ip.split('.').map(Number);
  if (parts.length !== 4 || parts.some(p => Number.isNaN(p) || p < 0 || p > 255)) return null;
  return ((parts[0] << 24) + (parts[1] << 16) + (parts[2] << 8) + parts[3]) >>> 0;
}

const PRIVATE_IPV4_RANGES = [
  { start: ipv4ToNumber('10.0.0.0'), end: ipv4ToNumber('10.255.255.255') },
  { start: ipv4ToNumber('172.16.0.0'), end: ipv4ToNumber('172.31.255.255') },
  { start: ipv4ToNumber('192.168.0.0'), end: ipv4ToNumber('192.168.255.255') },
  { start: ipv4ToNumber('127.0.0.0'), end: ipv4ToNumber('127.255.255.255') },
  { start: ipv4ToNumber('169.254.0.0'), end: ipv4ToNumber('169.254.255.255') },
  { start: ipv4ToNumber('0.0.0.0'), end: ipv4ToNumber('0.255.255.255') },
];

function isPrivateIPv4(ip) {
  const ipNum = ipv4ToNumber(ip);
  if (ipNum === null) return true;
  return PRIVATE_IPV4_RANGES.some(r => ipNum >= r.start && ipNum <= r.end);
}

function parseIPv6(ip) {
  let expanded = ip;
  if (ip.includes('::')) {
    const parts = ip.split('::');
    const left = parts[0] ? parts[0].split(':') : [];
    const right = parts[1] ? parts[1].split(':') : [];
    const missing = 8 - left.length - right.length;
    if (missing < 0) return null;
    expanded = [...left, ...Array(missing).fill('0'), ...right].join(':');
  }
  const groups = expanded.split(':');
  if (groups.length !== 8) return null;
  const nums = groups.map(g => parseInt(g || '0', 16));
  if (nums.some(n => Number.isNaN(n) || n < 0 || n > 0xffff)) return null;
  return nums;
}

function isPrivateIPv6(ip) {
  const normalized = ip.toLowerCase();

  if (normalized === '::1') return true; // loopback
  if (normalized === '::') return true; // unspecified

  // IPv4-mapped ::ffff:x.x.x.x
  const v4Mapped = normalized.match(/^::ffff:(\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3})$/);
  if (v4Mapped) return isPrivateIPv4(v4Mapped[1]);

  // IPv4-mapped hex ::ffff:xxxx:xxxx
  const v4Hex = normalized.match(/^::ffff:([0-9a-f]{1,4}):([0-9a-f]{1,4})$/);
  if (v4Hex) {
    const high = parseInt(v4Hex[1], 16);
    const low = parseInt(v4Hex[2], 16);
    const ipv4 = `${(high >> 8) & 0xff}.${high & 0xff}.${(low >> 8) & 0xff}.${low & 0xff}`;
    return isPrivateIPv4(ipv4);
  }

  const groups = parseIPv6(normalized);
  if (!groups) return true; // fail closed

  const first = groups[0];

  // fc00::/7 (fc00-fdff)
  if (first >= 0xfc00 && first <= 0xfdff) return true;

  // fe80::/10 (fe80-febf)
  if (first >= 0xfe80 && first <= 0xfebf) return true;

  // ff00::/8 multicast
  if (first >= 0xff00 && first <= 0xffff) return true;

  return false;
}

function isPrivateIP(ip) {
  if (!ip || typeof ip !== 'string') return true;
  const trimmed = ip.trim();
  if (/^\d{1,3}(\.\d{1,3}){3}$/.test(trimmed)) return isPrivateIPv4(trimmed);
  return isPrivateIPv6(trimmed);
}

// DNS lookup all IPs and block if any are private
async function checkHostSafety(hostname) {
  return new Promise(resolve => {
    dns.lookup(hostname, { all: true }, (err, addresses) => {
      if (err) return resolve({ safe: false, error: `DNS lookup failed: ${err.message}` });
      if (!addresses || addresses.length === 0) return resolve({ safe: false, error: 'No DNS records found' });

      for (const a of addresses) {
        if (isPrivateIP(a.address)) {
          return resolve({ safe: false, error: `Resolved to private/local IP: ${a.address}`, blockedIP: a.address });
        }
      }

      resolve({ safe: true, addresses: addresses.map(a => a.address) });
    });
  });
}

// Load certs (optional)
let certOptions = {};
try {
  if (fs.existsSync(CERT_PATH) && fs.existsSync(KEY_PATH)) {
    certOptions.cert = fs.readFileSync(CERT_PATH);
    certOptions.key = fs.readFileSync(KEY_PATH);
    console.log('[mTLS] Client certificate loaded');
  } else {
    console.log('[mTLS] No client certificate found, running without mTLS');
  }
  if (CA_PATH && fs.existsSync(CA_PATH)) {
    certOptions.ca = fs.readFileSync(CA_PATH);
    console.log('[mTLS] CA certificate loaded');
  }
} catch (err) {
  console.error('[mTLS] Error loading certificates:', err.message);
}

// Auth middleware
function authMiddleware(req, res, next) {
  const token = req.headers['x-service-token'];

  if (!SERVICE_TOKEN) {
    return res.status(500).json({ ok: false, code: 'CONFIG_ERROR', message: 'Service token not configured' });
  }

  if (!token || token !== SERVICE_TOKEN) {
    return res.status(401).json({ ok: false, code: 'UNAUTHORIZED', message: 'Invalid or missing service token' });
  }

  next();
}

// Health (no auth)
app.get('/health', (_req, res) => {
  res.json({
    status: 'healthy',
    timestamp: new Date().toISOString(),
    certsLoaded: !!certOptions.cert,
    targetConfigured: !!TARGET_URL,
  });
});

// Proxy
app.all('/proxy', authMiddleware, async (req, res) => {
  const urlParam = req.query.url;
  let targetUrl = TARGET_URL;

  // Validate ?url= only if allowlist exists
  if (urlParam) {
    const allowedHosts = getAllowedHosts();
    if (!allowedHosts) {
      return res.status(403).json({
        ok: false,
        code: 'FORBIDDEN',
        message: 'Dynamic URLs not allowed. Configure ALLOWED_HOSTS or use NFE_TARGET_URL.',
      });
    }

    let parsedUrl;
    try {
      parsedUrl = new URL(String(urlParam));
    } catch {
      return res.status(400).json({ ok: false, code: 'INVALID_URL', message: 'Invalid URL format' });
    }

    if (!isHttpProtocol(parsedUrl)) {
      return res.status(400).json({ ok: false, code: 'INVALID_PROTOCOL', message: 'Only http/https are allowed' });
    }

    if (!isHostAllowed(parsedUrl.hostname)) {
      return res.status(403).json({ ok: false, code: 'FORBIDDEN', message: `Host not allowed: ${parsedUrl.hostname}` });
    }

    const safety = await checkHostSafety(parsedUrl.hostname);
    if (!safety.safe) {
      return res.status(403).json({ ok: false, code: 'FORBIDDEN', message: 'Access to private/local networks is not allowed' });
    }

    targetUrl = String(urlParam);
  }

  if (!targetUrl) {
    return res.status(400).json({
      ok: false,
      code: 'MISSING_URL',
      message: 'Target URL not configured. Set NFE_TARGET_URL or provide ?url= with ALLOWED_HOSTS.',
    });
  }

  let url;
  try {
    url = new URL(String(targetUrl));
  } catch {
    return res.status(400).json({ ok: false, code: 'INVALID_URL', message: 'Invalid target URL' });
  }

  if (!isHttpProtocol(url)) {
    return res.status(400).json({ ok: false, code: 'INVALID_PROTOCOL', message: 'Only http/https are allowed' });
  }

  const isHttps = url.protocol === 'https:';
  const mod = isHttps ? https : http;

  const agentOptions = isHttps
    ? { ...certOptions, keepAlive: true, rejectUnauthorized: true }
    : { keepAlive: true };

  const agent = isHttps ? new https.Agent(agentOptions) : new http.Agent(agentOptions);

  const bodyContent = prepareBody(req.body);
  const forwardHeaders = cleanHeaders(req.headers);
  forwardHeaders['host'] = url.host;

  if (bodyContent) forwardHeaders['content-length'] = Buffer.byteLength(bodyContent).toString();

  const options = {
    hostname: url.hostname,
    port: url.port || (isHttps ? 443 : 80),
    path: url.pathname + url.search,
    method: req.method,
    agent,
    headers: forwardHeaders,
    timeout: TIMEOUT_MS,
  };

  const proxyReq = mod.request(options, proxyRes => {
    const chunks = [];
    proxyRes.on('data', c => chunks.push(c));
    proxyRes.on('end', () => {
      const out = Buffer.concat(chunks);
      const responseHeaders = cleanHeaders(proxyRes.headers);
      for (const [k, v] of Object.entries(responseHeaders)) res.setHeader(k, v);
      res.status(proxyRes.statusCode || 200).send(out);
    });
  });

  proxyReq.on('error', err => {
    const msg = err?.message || 'Proxy error';
    const isCertError =
      msg.toLowerCase().includes('certificate') ||
      msg.toLowerCase().includes('ssl') ||
      String(err?.code || '').toUpperCase().includes('SSL') ||
      String(err?.code || '').toUpperCase().includes('CERT');

    res.status(502).json({ ok: false, code: isCertError ? 'CERTIFICATE_ERROR' : 'PROXY_ERROR', message: msg });
  });

  proxyReq.on('timeout', () => {
    proxyReq.destroy();
    res.status(504).json({ ok: false, code: 'TIMEOUT', message: `Request timed out after ${TIMEOUT_MS}ms` });
  });

  if (bodyContent) proxyReq.write(bodyContent);
  proxyReq.end();
});

app.listen(PORT, () => {
  console.log(`[Server] mTLS Proxy running on port ${PORT}`);
});
