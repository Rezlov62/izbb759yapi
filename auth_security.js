/**
 * İzmir KentVizyon - AES-256-CTR + HMAC-SHA256 + PBKDF2 Güvenlik Katmanı
 * ve Kalıcı Veri/PDF Depolama Servisi (StorageService: IndexedDB + LocalStorage + JSON Yedekleme)
 * Hem yerel (file://) hem de web (http/https) ortamında sıfır dış bağımlılıkla çalışır.
 */
(function (global) {
    'use strict';

    const SESSION_KEY = 'KENTVIZYON_AUTH_SESSION_V1';
    const DELTA_STORAGE_KEY = 'KENTVIZYON_DELTA_STATE_V1';
    const IDB_NAME = 'KentVizyonStorageDB';
    const IDB_VERSION = 1;
    const IDB_PDF_STORE = 'pdfs';

    // --- Yardımcı Dönüşüm Fonksiyonları ---
    function hexToBytes(hex) {
        const len = hex.length >>> 1;
        const out = new Uint8Array(len);
        for (let i = 0; i < len; i++) {
            out[i] = parseInt(hex.substr(i * 2, 2), 16);
        }
        return out;
    }

    function bytesToHex(bytes) {
        let s = '';
        for (let i = 0; i < bytes.length; i++) {
            s += (bytes[i] < 16 ? '0' : '') + bytes[i].toString(16);
        }
        return s;
    }

    function base64ToBytes(b64) {
        if (typeof atob === 'function') {
            const bin = atob(b64);
            const out = new Uint8Array(bin.length);
            for (let i = 0; i < bin.length; i++) out[i] = bin.charCodeAt(i);
            return out;
        }
        const chars = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/';
        const lookup = new Uint8Array(256);
        for (let i = 0; i < chars.length; i++) lookup[chars.charCodeAt(i)] = i;
        b64 = b64.replace(/[\r\n\s]/g, '');
        let pad = 0;
        if (b64.endsWith('==')) pad = 2;
        else if (b64.endsWith('=')) pad = 1;
        const outLen = ((b64.length * 3) >>> 2) - pad;
        const out = new Uint8Array(outLen);
        let p = 0;
        for (let i = 0; i < b64.length; i += 4) {
            const c1 = lookup[b64.charCodeAt(i)];
            const c2 = lookup[b64.charCodeAt(i + 1)];
            const c3 = lookup[b64.charCodeAt(i + 2)];
            const c4 = lookup[b64.charCodeAt(i + 3)];
            const triplet = (c1 << 18) | (c2 << 12) | (c3 << 6) | c4;
            if (p < outLen) out[p++] = (triplet >>> 16) & 0xff;
            if (p < outLen) out[p++] = (triplet >>> 8) & 0xff;
            if (p < outLen) out[p++] = triplet & 0xff;
        }
        return out;
    }

    function utf8ToBytes(str) {
        if (typeof TextEncoder !== 'undefined') {
            return new TextEncoder().encode(str);
        }
        const utf8 = unescape(encodeURIComponent(str));
        const out = new Uint8Array(utf8.length);
        for (let i = 0; i < utf8.length; i++) out[i] = utf8.charCodeAt(i);
        return out;
    }

    function bytesToUtf8(bytes) {
        if (typeof TextDecoder !== 'undefined') {
            return new TextDecoder('utf-8').decode(bytes);
        }
        let bin = '';
        const chunk = 8192;
        for (let i = 0; i < bytes.length; i += chunk) {
            bin += String.fromCharCode.apply(null, bytes.subarray(i, i + chunk));
        }
        return decodeURIComponent(escape(bin));
    }

    // --- SHA-256 & HMAC-SHA256 & PBKDF2-HMAC-SHA256 ---
    const SHA256_K = new Uint32Array([
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
        0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
        0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
        0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
        0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
        0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
        0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
        0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
    ]);

    function sha256(msgBytes) {
        let h0 = 0x6a09e667, h1 = 0xbb67ae85, h2 = 0x3c6ef372, h3 = 0xa54ff53a;
        let h4 = 0x510e527f, h5 = 0x9b05688c, h6 = 0x1f83d9ab, h7 = 0x5be0cd19;

        const len = msgBytes.length;
        const bitLenHi = Math.floor((len * 8) / 0x100000000);
        const bitLenLo = (len * 8) >>> 0;
        const padLen = ((len + 9 + 63) & ~63);
        const padded = new Uint8Array(padLen);
        padded.set(msgBytes);
        padded[len] = 0x80;
        const dv = new DataView(padded.buffer);
        dv.setUint32(padLen - 8, bitLenHi, false);
        dv.setUint32(padLen - 4, bitLenLo, false);

        const w = new Uint32Array(64);
        for (let off = 0; off < padLen; off += 64) {
            for (let i = 0; i < 16; i++) w[i] = dv.getUint32(off + i * 4, false);
            for (let i = 16; i < 64; i++) {
                const v1 = w[i - 15];
                const s0 = ((v1 >>> 7) | (v1 << 25)) ^ ((v1 >>> 18) | (v1 << 14)) ^ (v1 >>> 3);
                const v2 = w[i - 2];
                const s1 = ((v2 >>> 17) | (v2 << 15)) ^ ((v2 >>> 19) | (v2 << 13)) ^ (v2 >>> 10);
                w[i] = (w[i - 16] + s0 + w[i - 7] + s1) >>> 0;
            }
            let a = h0, b = h1, c = h2, d = h3, e = h4, f = h5, g = h6, h = h7;
            for (let i = 0; i < 64; i++) {
                const S1 = ((e >>> 6) | (e << 26)) ^ ((e >>> 11) | (e << 21)) ^ ((e >>> 25) | (e << 7));
                const ch = (e & f) ^ (~e & g);
                const temp1 = (h + S1 + ch + SHA256_K[i] + w[i]) >>> 0;
                const S0 = ((a >>> 2) | (a << 30)) ^ ((a >>> 13) | (a << 19)) ^ ((a >>> 22) | (a << 10));
                const maj = (a & b) ^ (a & c) ^ (b & c);
                const temp2 = (S0 + maj) >>> 0;
                h = g; g = f; f = e; e = (d + temp1) >>> 0;
                d = c; c = b; b = a; a = (temp1 + temp2) >>> 0;
            }
            h0 = (h0 + a) >>> 0; h1 = (h1 + b) >>> 0; h2 = (h2 + c) >>> 0; h3 = (h3 + d) >>> 0;
            h4 = (h4 + e) >>> 0; h5 = (h5 + f) >>> 0; h6 = (h6 + g) >>> 0; h7 = (h7 + h) >>> 0;
        }
        const out = new Uint8Array(32);
        const outDv = new DataView(out.buffer);
        outDv.setUint32(0, h0, false); outDv.setUint32(4, h1, false);
        outDv.setUint32(8, h2, false); outDv.setUint32(12, h3, false);
        outDv.setUint32(16, h4, false); outDv.setUint32(20, h5, false);
        outDv.setUint32(24, h6, false); outDv.setUint32(28, h7, false);
        return out;
    }

    function hmacSha256(keyBytes, dataBytes) {
        let k = keyBytes;
        if (k.length > 64) k = sha256(k);
        const ipad = new Uint8Array(64);
        const opad = new Uint8Array(64);
        for (let i = 0; i < 64; i++) {
            const b = i < k.length ? k[i] : 0;
            ipad[i] = b ^ 0x36;
            opad[i] = b ^ 0x5c;
        }
        const inner = new Uint8Array(64 + dataBytes.length);
        inner.set(ipad, 0);
        inner.set(dataBytes, 64);
        const innerHash = sha256(inner);
        const outer = new Uint8Array(64 + 32);
        outer.set(opad, 0);
        outer.set(innerHash, 64);
        return sha256(outer);
    }

    function pbkdf2Sha256(passwordStr, saltBytes, iterations, dkLen) {
        const pwdBytes = utf8ToBytes(passwordStr);
        const blocks = Math.ceil(dkLen / 32);
        const out = new Uint8Array(blocks * 32);
        const saltBlock = new Uint8Array(saltBytes.length + 4);
        saltBlock.set(saltBytes, 0);

        for (let b = 1; b <= blocks; b++) {
            saltBlock[saltBytes.length] = (b >>> 24) & 0xff;
            saltBlock[saltBytes.length + 1] = (b >>> 16) & 0xff;
            saltBlock[saltBytes.length + 2] = (b >>> 8) & 0xff;
            saltBlock[saltBytes.length + 3] = b & 0xff;

            let u = hmacSha256(pwdBytes, saltBlock);
            const t = new Uint8Array(u);
            for (let i = 1; i < iterations; i++) {
                u = hmacSha256(pwdBytes, u);
                for (let j = 0; j < 32; j++) t[j] ^= u[j];
            }
            out.set(t, (b - 1) * 32);
        }
        return out.subarray(0, dkLen);
    }

    // --- AES-256-CTR (FIPS-197) ---
    const SBOX = new Uint8Array(256);
    const RCON = new Uint8Array([0x00, 0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36]);
    (function initAesTables() {
        const p = new Uint8Array(256), q = new Uint8Array(256);
        let x = 1;
        for (let i = 0; i < 256; i++) {
            p[i] = x;
            q[x] = i;
            x ^= (x << 1) ^ ((x & 0x80) ? 0x11b : 0);
        }
        SBOX[0] = 0x63;
        for (let i = 1; i < 256; i++) {
            let y = p[255 - q[i]];
            let s = y;
            for (let r = 1; r < 5; r++) {
                y = ((y << 1) | (y >>> 7)) & 0xff;
                s ^= y;
            }
            SBOX[i] = s ^ 0x63;
        }
    })();

    function xtime(a) {
        return ((a << 1) ^ ((a & 0x80) ? 0x1b : 0)) & 0xff;
    }

    function expandKey256(key32) {
        const w = new Uint8Array(240);
        w.set(key32);
        let i = 32, rconIdx = 1;
        const temp = new Uint8Array(4);
        while (i < 240) {
            temp[0] = w[i - 4]; temp[1] = w[i - 3]; temp[2] = w[i - 2]; temp[3] = w[i - 1];
            if (i % 32 === 0) {
                const t = temp[0];
                temp[0] = SBOX[temp[1]] ^ RCON[rconIdx++];
                temp[1] = SBOX[temp[2]];
                temp[2] = SBOX[temp[3]];
                temp[3] = SBOX[t];
            } else if (i % 32 === 16) {
                temp[0] = SBOX[temp[0]]; temp[1] = SBOX[temp[1]];
                temp[2] = SBOX[temp[2]]; temp[3] = SBOX[temp[3]];
            }
            w[i] = w[i - 32] ^ temp[0];
            w[i + 1] = w[i - 31] ^ temp[1];
            w[i + 2] = w[i - 30] ^ temp[2];
            w[i + 3] = w[i - 29] ^ temp[3];
            i += 4;
        }
        return w;
    }

    function aes256EncryptBlock(block16, roundKeys, out16) {
        const s = new Uint8Array(16);
        const t = new Uint8Array(16);
        for (let i = 0; i < 16; i++) s[i] = block16[i] ^ roundKeys[i];

        for (let round = 1; round <= 14; round++) {
            const rkOff = round * 16;
            t[0] = SBOX[s[0]];  t[1] = SBOX[s[5]];  t[2] = SBOX[s[10]]; t[3] = SBOX[s[15]];
            t[4] = SBOX[s[4]];  t[5] = SBOX[s[9]];  t[6] = SBOX[s[14]]; t[7] = SBOX[s[3]];
            t[8] = SBOX[s[8]];  t[9] = SBOX[s[13]]; t[10] = SBOX[s[2]]; t[11] = SBOX[s[7]];
            t[12] = SBOX[s[12]]; t[13] = SBOX[s[1]]; t[14] = SBOX[s[6]]; t[15] = SBOX[s[11]];

            if (round < 14) {
                for (let c = 0; c < 16; c += 4) {
                    const a0 = t[c], a1 = t[c + 1], a2 = t[c + 2], a3 = t[c + 3];
                    const tm = a0 ^ a1 ^ a2 ^ a3;
                    s[c] = a0 ^ tm ^ xtime(a0 ^ a1) ^ roundKeys[rkOff + c];
                    s[c + 1] = a1 ^ tm ^ xtime(a1 ^ a2) ^ roundKeys[rkOff + c + 1];
                    s[c + 2] = a2 ^ tm ^ xtime(a2 ^ a3) ^ roundKeys[rkOff + c + 2];
                    s[c + 3] = a3 ^ tm ^ xtime(a3 ^ a0) ^ roundKeys[rkOff + c + 3];
                }
            } else {
                for (let i = 0; i < 16; i++) out16[i] = t[i] ^ roundKeys[rkOff + i];
            }
        }
    }

    function aes256CtrCrypt(dataBytes, key32, iv16) {
        const roundKeys = expandKey256(key32);
        const counter = new Uint8Array(iv16);
        const keystream = new Uint8Array(16);
        const out = new Uint8Array(dataBytes.length);

        for (let off = 0; off < dataBytes.length; off += 16) {
            aes256EncryptBlock(counter, roundKeys, keystream);
            const rem = Math.min(16, dataBytes.length - off);
            for (let i = 0; i < rem; i++) {
                out[off + i] = dataBytes[off + i] ^ keystream[i];
            }
            for (let c = 15; c >= 0; c--) {
                counter[c] = (counter[c] + 1) & 0xff;
                if (counter[c] !== 0) break;
            }
        }
        return out;
    }

    function constantTimeEqualHex(a, b) {
        if (typeof a !== 'string' || typeof b !== 'string' || a.length !== b.length) return false;
        let diff = 0;
        for (let i = 0; i < a.length; i++) diff |= a.charCodeAt(i) ^ b.charCodeAt(i);
        return diff === 0;
    }

    const USER_DIRECTORY_KEY = 'KENTVIZYON_USER_DIRECTORY_V1';
    const AUDIT_LOGS_KEY = 'KENTVIZYON_AUDIT_LOGS_V1';

    function randomBytes(len) {
        const out = new Uint8Array(len);
        if (typeof crypto !== 'undefined' && typeof crypto.getRandomValues === 'function') {
            crypto.getRandomValues(out);
            return out;
        }
        for (let i = 0; i < len; i++) {
            out[i] = Math.floor(Math.random() * 256);
        }
        return out;
    }

    function normalizeRole(role, username) {
        const uname = String(username || '').trim().toLowerCase();
        if (uname === 'admin') return 'yonetici';
        if (role === 'duzenleyen' || role === 'uzman' || role === 'saha') return 'duzenleyen';
        return 'goruntuleyen';
    }

    function getDefaultPermissionsForRole(role) {
        if (role === 'yonetici') {
            return {
                canUpdateStage: true,
                canUploadPdf: true,
                canSendTebligat: true,
                canViewExecSummary: true,
                canViewPdf: true,
                canAccessAdminPanel: true
            };
        }
        if (role === 'duzenleyen' || role === 'uzman' || role === 'saha') {
            return {
                canUpdateStage: true,
                canUploadPdf: true,
                canSendTebligat: true,
                canViewExecSummary: true,
                canViewPdf: true,
                canAccessAdminPanel: false
            };
        }
        // 'goruntuleyen' (Sadece Görüntüleme / Salt Okunur)
        return {
            canUpdateStage: false,
            canUploadPdf: false,
            canSendTebligat: false,
            canViewExecSummary: true,
            canViewPdf: true,
            canAccessAdminPanel: false
        };
    }

    function getRoleLabel(role) {
        const map = {
            'yonetici': 'Yönetici (Admin)',
            'duzenleyen': 'Düzenleyen',
            'goruntuleyen': 'Görüntüleyen',
            'uzman': 'Düzenleyen',
            'saha': 'Düzenleyen',
            'kullanici': 'Görüntüleyen'
        };
        return map[role] || 'Görüntüleyen';
    }

    // --- İLİŞKİSEL VERİTABANI (SQLite / REST API) İSTEMCİSİ ---
    const IS_LOCAL_ENV = (typeof location !== 'undefined') && (
        location.protocol === 'file:' ||
        location.hostname === 'localhost' ||
        location.hostname === '127.0.0.1' ||
        location.hostname === '0.0.0.0'
    );

    const DEFAULT_DB_API_BASE = (typeof location !== 'undefined' && location.port === '8000')
        ? ''
        : (IS_LOCAL_ENV ? 'http://127.0.0.1:8000' : '');

    let dbApiAvailable = IS_LOCAL_ENV;

    let dbConnectionState = {
        connected: false,
        engine: 'SQLite3 (kentvizyon.db)',
        dbSizeKB: 184.0,
        lastSyncAt: null,
        stats: null,
        districtView: []
    };

    async function apiRequest(path, method = 'GET', bodyObj = null) {
        if (typeof fetch !== 'function' || !dbApiAvailable) return null;
        try {
            const opts = {
                method: method,
                headers: { 'Content-Type': 'application/json' }
            };
            if (bodyObj !== null && method !== 'GET') {
                opts.body = JSON.stringify(bodyObj);
            }
            const res = await fetch(DEFAULT_DB_API_BASE + path, opts);
            if (!res.ok) return null;
            const data = await res.json();
            if (data && data.ok) {
                dbConnectionState.connected = true;
                dbConnectionState.lastSyncAt = new Date().toISOString();
            }
            return data;
        } catch (err) {
            return null;
        }
    }

    async function syncFromDatabase() {
        const boot = await apiRequest('/api/bootstrap', 'GET');
        if (!boot || !boot.ok) return { ok: false, connected: false };

        dbConnectionState.connected = true;
        dbConnectionState.stats = boot.stats || null;
        if (boot.dbSizeKB) dbConnectionState.dbSizeKB = boot.dbSizeKB;
        if (Array.isArray(boot.districtView)) dbConnectionState.districtView = boot.districtView;
        dbConnectionState.lastSyncAt = new Date().toISOString();

        // 1. Kullanıcı dizinini senkronize et (Yerel yeni kayıtlar varsa veritabanına da gönder)
        if (boot.users && typeof boot.users === 'object') {
            const localUsers = loadUserDirectory();
            const mergedUsers = { ...localUsers, ...boot.users };
            saveUserDirectory(mergedUsers);
            Object.values(localUsers).forEach(lu => {
                const uname = String(lu.username || '').toLowerCase();
                if (!boot.users[uname]) {
                    apiRequest('/api/users/save', 'POST', { user: lu });
                }
            });
        }

        // 2. Denetim günlüğü (audit_logs) kayıtlarını birleştir ve senkronize et
        if (Array.isArray(boot.auditLogs)) {
            const localLogs = getAuditLogs();
            const dbLogIds = new Set(boot.auditLogs.map(l => l.id));
            const unsyncedLocal = localLogs.filter(l => l && l.id && !dbLogIds.has(l.id));
            unsyncedLocal.forEach(l => {
                apiRequest('/api/audit/log', 'POST', { log: l });
            });
            const combined = [...unsyncedLocal, ...boot.auditLogs]
                .sort((a, b) => String(b.timestamp || '').localeCompare(String(a.timestamp || '')))
                .slice(0, 1500);
            saveAuditLogs(combined);
        }

        // 3. Yapı güncellemelerini (overrides) senkronize et
        if (boot.overrides && typeof boot.overrides === 'object') {
            const state = loadDeltaState();
            const localOverrides = state.overrides || {};
            Object.keys(localOverrides).forEach(bid => {
                if (!boot.overrides[bid]) {
                    apiRequest('/api/buildings/update', 'POST', {
                        building: localOverrides[bid],
                        updatedBy: 'senkronizasyon'
                    });
                }
            });
            state.overrides = { ...localOverrides, ...boot.overrides };
            saveDeltaState(state);
        }

        if (typeof global.dispatchEvent === 'function' && typeof CustomEvent === 'function') {
            global.dispatchEvent(new CustomEvent('kentvizyon:db-synced', { detail: dbConnectionState }));
        }
        return { ok: true, connected: true, state: dbConnectionState };
    }

    // --- DENETİM GÜNLÜĞÜ (AUDIT LOG) SERVİSİ ---
    function getAuditLogs() {
        try {
            const raw = localStorage.getItem(AUDIT_LOGS_KEY);
            if (raw) {
                const parsed = JSON.parse(raw);
                if (Array.isArray(parsed)) return parsed;
            }
        } catch (e) {}
        return [];
    }

    function saveAuditLogs(logs) {
        try {
            const trimmed = logs.slice(0, 1500);
            localStorage.setItem(AUDIT_LOGS_KEY, JSON.stringify(trimmed));
        } catch (e) {}
    }

    function logAudit(entry) {
        if (!entry) return;
        const session = loadSession();
        const logs = getAuditLogs();
        const newLog = {
            id: 'log_' + Date.now() + '_' + Math.random().toString(36).slice(2, 7),
            timestamp: entry.timestamp || new Date().toISOString(),
            username: entry.username || (session ? session.username : 'anonim'),
            displayName: entry.displayName || (session ? session.displayName : 'Bilinmeyen Kullanıcı'),
            role: entry.role || (session ? session.role : 'goruntuleyen'),
            category: entry.category || 'SYSTEM',
            action: entry.action || 'İşlem Kaydı',
            target: entry.target || '-',
            details: entry.details || '',
            status: entry.status || 'success'
        };
        logs.unshift(newLog);
        saveAuditLogs(logs);
        apiRequest('/api/audit/log', 'POST', { log: newLog });
        return newLog;
    }

    function clearAuditLogs() {
        try {
            localStorage.removeItem(AUDIT_LOGS_KEY);
            apiRequest('/api/audit/clear', 'POST', {}).then(() => {
                logAudit({
                    category: 'USER_MGMT',
                    action: 'Denetim Günlüğü Temizlendi',
                    target: 'Sistem Logları',
                    details: 'Yönetici tarafından geçmiş işlem kayıtları sıfırlandı.',
                    status: 'warning'
                });
            });
        } catch (e) {}
    }

    // --- KULLANICI DİZİNİ VE YETKİ YÖNETİMİ ---
    function loadUserDirectory() {
        const bundle = global.ENCRYPTED_GEOJSON_DATA;
        const baseUsers = (bundle && Array.isArray(bundle.users)) ? bundle.users : [];
        let storedMap = {};
        try {
            const raw = localStorage.getItem(USER_DIRECTORY_KEY);
            if (raw) storedMap = JSON.parse(raw) || {};
        } catch (e) {}

        const mergedMap = {};

        baseUsers.forEach((bu) => {
            const uname = bu.username.toLowerCase();
            const existing = storedMap[uname] || {};
            const role = normalizeRole(existing.role || bu.role, uname);
            const defaultPerms = getDefaultPermissionsForRole(role);
            const perms = existing.permissions
                ? { ...defaultPerms, ...existing.permissions, canAccessAdminPanel: uname === 'admin' }
                : defaultPerms;

            mergedMap[uname] = {
                username: bu.username,
                displayName: existing.displayName || bu.displayName || bu.username,
                department: existing.department || (uname === 'admin' ? 'Kentsel Dönüşüm Dairesi Başkanlığı' : 'CBS & Teknik İnceleme Birimi'),
                role: role,
                status: uname === 'admin' ? 'aktif' : (existing.status || 'aktif'),
                isBuiltIn: true,
                createdAt: existing.createdAt || '2026-03-01T09:00:00.000Z',
                lastLoginAt: existing.lastLoginAt || null,
                permissions: perms,
                salt: existing.salt || bu.salt,
                iterations: existing.iterations || bu.iterations || 10000,
                wrapIv: existing.wrapIv || bu.wrapIv,
                wrappedKey: existing.wrappedKey || bu.wrappedKey,
                wrapMac: existing.wrapMac || bu.wrapMac
            };
        });

        Object.keys(storedMap).forEach(uname => {
            // Eski ikinci yönetici ('yonetici') hesabını tek admin kuralı gereği yoksay
            if (uname === 'yonetici') return;
            if (!mergedMap[uname] && !storedMap[uname].deleted) {
                const cu = storedMap[uname];
                const role = normalizeRole(cu.role, uname);
                const defaultPerms = getDefaultPermissionsForRole(role);
                const perms = cu.permissions
                    ? { ...defaultPerms, ...cu.permissions, canAccessAdminPanel: false }
                    : defaultPerms;

                mergedMap[uname] = {
                    username: cu.username || uname,
                    displayName: cu.displayName || uname,
                    department: cu.department || 'Kentsel Dönüşüm Birimi',
                    role: role,
                    status: cu.status || 'aktif',
                    isBuiltIn: false,
                    createdAt: cu.createdAt || new Date().toISOString(),
                    lastLoginAt: cu.lastLoginAt || null,
                    permissions: perms,
                    salt: cu.salt,
                    iterations: cu.iterations || 10000,
                    wrapIv: cu.wrapIv,
                    wrappedKey: cu.wrappedKey,
                    wrapMac: cu.wrapMac
                };
            }
        });

        return mergedMap;
    }

    function saveUserDirectory(dirMap) {
        try {
            localStorage.setItem(USER_DIRECTORY_KEY, JSON.stringify(dirMap));
        } catch (e) {}
    }

    function getUsers() {
        const dirMap = loadUserDirectory();
        return Object.values(dirMap);
    }

    function getUserByUsername(username) {
        if (!username) return null;
        const dirMap = loadUserDirectory();
        return dirMap[String(username).trim().toLowerCase()] || null;
    }

    function wrapMasterKeyForPassword(masterKeyHex, passwordStr, iterations = 10000) {
        const masterBytes = hexToBytes(masterKeyHex);
        const saltBytes = randomBytes(16);
        const wrapIvBytes = randomBytes(16);
        const derived = pbkdf2Sha256(String(passwordStr || ''), saltBytes, iterations, 64);
        const uAesKey = derived.subarray(0, 32);
        const uHmacKey = derived.subarray(32, 64);

        const wrappedKeyBytes = aes256CtrCrypt(masterBytes, uAesKey, wrapIvBytes);
        const macInput = new Uint8Array(wrapIvBytes.length + wrappedKeyBytes.length);
        macInput.set(wrapIvBytes, 0);
        macInput.set(wrappedKeyBytes, wrapIvBytes.length);
        const wrapMacHex = bytesToHex(hmacSha256(uHmacKey, macInput));

        return {
            salt: bytesToHex(saltBytes),
            iterations: iterations,
            wrapIv: bytesToHex(wrapIvBytes),
            wrappedKey: bytesToHex(wrappedKeyBytes),
            wrapMac: wrapMacHex
        };
    }

    function createOrUpdateUser(userPayload) {
        const session = loadSession();
        if (!session || !session.masterKeyHex) {
            return { ok: false, error: 'Anahtar oturumu bulunamadı. Lütfen yeniden giriş yapın.' };
        }
        const uname = String(userPayload.username || '').trim().toLowerCase();
        if (!uname || uname.length < 3) {
            return { ok: false, error: 'Kullanıcı adı en az 3 karakter olmalıdır.' };
        }
        if (uname === 'yonetici') {
            return { ok: false, error: 'Sistemde yalnızca tek bir Yönetici (admin) hesabı bulunabilir.' };
        }
        if (uname !== 'admin' && userPayload.role === 'yonetici') {
            return { ok: false, error: 'Sistemde yalnızca tek bir Yönetici (admin) olabilir. Diğer kullanıcılar yalnızca "Düzenleyen" veya "Görüntüleyen" olarak tanımlanabilir.' };
        }

        const dirMap = loadUserDirectory();
        const existing = dirMap[uname];
        const isNew = !existing;

        if (isNew && (!userPayload.password || String(userPayload.password).length < 4)) {
            return { ok: false, error: 'Yeni kullanıcı için en az 4 karakterli bir şifre belirlemelisiniz.' };
        }

        const role = normalizeRole(userPayload.role || (existing ? existing.role : 'goruntuleyen'), uname);
        const permissions = userPayload.permissions
            ? { ...getDefaultPermissionsForRole(role), ...userPayload.permissions, canAccessAdminPanel: uname === 'admin' }
            : getDefaultPermissionsForRole(role);

        let cryptoFields = existing ? {
            salt: existing.salt,
            iterations: existing.iterations || 10000,
            wrapIv: existing.wrapIv,
            wrappedKey: existing.wrappedKey,
            wrapMac: existing.wrapMac
        } : null;

        if (userPayload.password && String(userPayload.password).trim().length > 0) {
            cryptoFields = wrapMasterKeyForPassword(session.masterKeyHex, String(userPayload.password).trim(), 10000);
        }

        const updatedUser = {
            username: existing ? existing.username : String(userPayload.username).trim(),
            displayName: userPayload.displayName || (existing ? existing.displayName : uname),
            department: userPayload.department || (existing ? existing.department : 'CBS & Teknik İnceleme Birimi'),
            role: role,
            status: uname === 'admin' ? 'aktif' : (userPayload.status || (existing ? existing.status : 'aktif')),
            isBuiltIn: existing ? Boolean(existing.isBuiltIn) : false,
            createdAt: existing ? existing.createdAt : new Date().toISOString(),
            lastLoginAt: existing ? existing.lastLoginAt : null,
            permissions: permissions,
            ...cryptoFields
        };

        dirMap[uname] = updatedUser;
        saveUserDirectory(dirMap);
        apiRequest('/api/users/save', 'POST', { user: updatedUser });

        logAudit({
            category: 'USER_MGMT',
            action: isNew ? 'Yeni Kullanıcı Oluşturuldu' : 'Kullanıcı Bilgileri Güncellendi',
            target: `Kullanıcı: ${updatedUser.username} (${updatedUser.displayName})`,
            details: `Rol: ${getRoleLabel(updatedUser.role)} | Birim: ${updatedUser.department} | Durum: ${updatedUser.status.toUpperCase()}${userPayload.password ? ' | Şifre güncellendi' : ''}`,
            status: 'success'
        });

        return { ok: true, user: updatedUser, isNew: isNew };
    }

    function updateUserPermissions(username, newRole, newPermissions) {
        const uname = String(username || '').trim().toLowerCase();
        const dirMap = loadUserDirectory();
        const target = dirMap[uname];
        if (!target) return { ok: false, error: 'Kullanıcı bulunamadı.' };

        if (uname === 'admin') {
            target.role = 'yonetici';
            target.permissions = getDefaultPermissionsForRole('yonetici');
        } else {
            if (newRole) {
                target.role = normalizeRole(newRole, uname);
            }
            if (newPermissions) {
                target.permissions = {
                    ...target.permissions,
                    ...newPermissions,
                    canAccessAdminPanel: false
                };
            }
        }
        dirMap[uname] = target;
        saveUserDirectory(dirMap);
        apiRequest('/api/users/save', 'POST', { user: target });

        // Eğer aktif oturumdaki kullanıcının yetkisi güncellendiyse oturumu da güncelle
        const currentSession = loadSession();
        if (currentSession && currentSession.username.toLowerCase() === uname) {
            currentSession.role = target.role;
            currentSession.permissions = target.permissions;
            saveSession(currentSession);
        }

        const activePerms = Object.entries(target.permissions)
            .filter(([, v]) => Boolean(v))
            .map(([k]) => k)
            .join(', ');

        logAudit({
            category: 'USER_MGMT',
            action: 'Kullanıcı Yetkileri Güncellendi',
            target: `Kullanıcı: ${target.username} (${target.displayName})`,
            details: `Rol: ${getRoleLabel(target.role)} | Aktif Yetkiler: ${activePerms || 'Salt Okunur (Görüntüleyen)'}`,
            status: 'success'
        });

        return { ok: true, user: target };
    }

    function toggleUserStatus(username) {
        const uname = String(username || '').trim().toLowerCase();
        const dirMap = loadUserDirectory();
        const target = dirMap[uname];
        if (!target) return { ok: false, error: 'Kullanıcı bulunamadı.' };
        if (uname === 'admin') {
            return { ok: false, error: 'Ana sistem yöneticisi (admin) hesabı askıya alınamaz.' };
        }

        target.status = target.status === 'aktif' ? 'pasif' : 'aktif';
        dirMap[uname] = target;
        saveUserDirectory(dirMap);
        apiRequest('/api/users/save', 'POST', { user: target });

        logAudit({
            category: 'USER_MGMT',
            action: target.status === 'aktif' ? 'Kullanıcı Hesabı Aktifleştirildi' : 'Kullanıcı Hesabı Askıya Alındı',
            target: `Kullanıcı: ${target.username} (${target.displayName})`,
            details: `${target.displayName} (${target.username}) hesabının durumu "${target.status.toUpperCase()}" olarak değiştirildi.`,
            status: target.status === 'aktif' ? 'success' : 'warning'
        });

        return { ok: true, user: target };
    }

    function deleteUser(username) {
        const uname = String(username || '').trim().toLowerCase();
        const dirMap = loadUserDirectory();
        const target = dirMap[uname];
        if (!target) return { ok: false, error: 'Kullanıcı bulunamadı.' };
        if (uname === 'admin') {
            return { ok: false, error: 'Ana sistem yöneticisi (admin) hesabı silinemez.' };
        }
        if (target.isBuiltIn) {
            return { ok: false, error: 'Varsayılan sistem hesabı silinemez; bunun yerine hesabı "Pasif (Askıya Alındı)" durumuna getirebilirsiniz.' };
        }

        delete dirMap[uname];
        saveUserDirectory(dirMap);
        apiRequest('/api/users/delete', 'POST', { username: uname });

        logAudit({
            category: 'USER_MGMT',
            action: 'Kullanıcı Hesabı Silindi',
            target: `Kullanıcı: ${target.username}`,
            details: `${target.displayName} (${target.username} - ${getRoleLabel(target.role)}) hesabı sistemden kalıcı olarak silindi.`,
            status: 'warning'
        });

        return { ok: true };
    }

    function hasPermission(permKey) {
        const session = loadSession();
        if (!session) return false;
        if (permKey === 'canAccessAdminPanel') {
            return String(session.username || '').toLowerCase() === 'admin' && session.role === 'yonetici';
        }
        const liveUser = getUserByUsername(session.username);
        const perms = (liveUser && liveUser.permissions) ? liveUser.permissions : (session.permissions || getDefaultPermissionsForRole(session.role));
        return Boolean(perms && perms[permKey]);
    }

    // --- Oturum ve Şifre Çözme API'si ---
    function saveSession(sessionObj) {
        const raw = JSON.stringify(sessionObj);
        try { sessionStorage.setItem(SESSION_KEY, raw); } catch (e) {}
        try { global.name = SESSION_KEY + ':' + raw; } catch (e) {}
    }

    function loadSession() {
        try {
            const s = sessionStorage.getItem(SESSION_KEY);
            if (s) return JSON.parse(s);
        } catch (e) {}
        try {
            if (typeof global.name === 'string' && global.name.startsWith(SESSION_KEY + ':')) {
                const raw = global.name.slice((SESSION_KEY + ':').length);
                return JSON.parse(raw);
            }
        } catch (e) {}
        return null;
    }

    function clearSession(shouldLog = true) {
        const current = loadSession();
        if (shouldLog && current) {
            logAudit({
                username: current.username,
                displayName: current.displayName,
                role: current.role,
                category: 'AUTH',
                action: 'Sistemden Çıkış Yapıldı',
                target: `Oturum: ${current.username}`,
                details: `${current.displayName} (${current.username}) güvenli çıkış yaptı.`,
                status: 'success'
            });
        }
        try { sessionStorage.removeItem(SESSION_KEY); } catch (e) {}
        try {
            if (typeof global.name === 'string' && global.name.startsWith(SESSION_KEY + ':')) {
                global.name = '';
            }
        } catch (e) {}
        delete global.GEOJSON_DATA;
    }

    function authenticate(username, password) {
        const bundle = global.ENCRYPTED_GEOJSON_DATA;
        if (!bundle || !Array.isArray(bundle.users)) {
            return { ok: false, error: 'Şifreli veri paketi (binalar_data.js) bulunamadı.' };
        }
        const normUser = String(username || '').trim().toLowerCase();
        const dirMap = loadUserDirectory();
        const userEntry = dirMap[normUser];

        if (!userEntry) {
            logAudit({
                username: normUser || 'bilinmeyen',
                displayName: 'Bilinmeyen Kullanıcı',
                role: 'kullanici',
                category: 'SECURITY',
                action: 'Hatalı Giriş Denemesi (Kullanıcı Yok)',
                target: `Kullanıcı Adı: ${normUser || '-'}`,
                details: `"${normUser}" kullanıcı adıyla başarısız giriş denemesi yapıldı.`,
                status: 'danger'
            });
            return { ok: false, error: 'Kullanıcı adı veya şifre hatalı!' };
        }

        if (userEntry.status === 'pasif') {
            logAudit({
                username: userEntry.username,
                displayName: userEntry.displayName,
                role: userEntry.role,
                category: 'SECURITY',
                action: 'Askıya Alınmış Hesap Giriş Denemesi',
                target: `Kullanıcı: ${userEntry.username}`,
                details: `Askıya alınmış (pasif) "${userEntry.username}" hesabıyla giriş denemesi engellendi.`,
                status: 'danger'
            });
            return { ok: false, error: 'Bu kullanıcı hesabı yönetici tarafından askıya alınmıştır!' };
        }

        const saltBytes = hexToBytes(userEntry.salt);
        const derived = pbkdf2Sha256(String(password || ''), saltBytes, userEntry.iterations || 10000, 64);
        const uAesKey = derived.subarray(0, 32);
        const uHmacKey = derived.subarray(32, 64);

        const wrapIvBytes = hexToBytes(userEntry.wrapIv);
        const wrappedKeyBytes = hexToBytes(userEntry.wrappedKey);
        const macInput = new Uint8Array(wrapIvBytes.length + wrappedKeyBytes.length);
        macInput.set(wrapIvBytes, 0);
        macInput.set(wrappedKeyBytes, wrapIvBytes.length);

        const computedWrapMac = bytesToHex(hmacSha256(uHmacKey, macInput));
        if (!constantTimeEqualHex(computedWrapMac, userEntry.wrapMac)) {
            logAudit({
                username: userEntry.username,
                displayName: userEntry.displayName,
                role: userEntry.role,
                category: 'SECURITY',
                action: 'Hatalı Şifre Denemesi',
                target: `Kullanıcı: ${userEntry.username}`,
                details: `${userEntry.displayName} (${userEntry.username}) hesabı için hatalı şifre girildi.`,
                status: 'danger'
            });
            return { ok: false, error: 'Kullanıcı adı veya şifre hatalı!' };
        }

        const masterBundle = aes256CtrCrypt(wrappedKeyBytes, uAesKey, wrapIvBytes);
        const masterKeyHex = bytesToHex(masterBundle);

        const nowIso = new Date().toISOString();
        userEntry.lastLoginAt = nowIso;
        dirMap[normUser] = userEntry;
        saveUserDirectory(dirMap);
        apiRequest('/api/users/save', 'POST', { user: userEntry });

        const sessionObj = {
            username: userEntry.username,
            role: userEntry.role,
            displayName: userEntry.displayName,
            department: userEntry.department,
            permissions: userEntry.permissions,
            masterKeyHex: masterKeyHex,
            loginTime: nowIso
        };
        saveSession(sessionObj);

        logAudit({
            username: userEntry.username,
            displayName: userEntry.displayName,
            role: userEntry.role,
            category: 'AUTH',
            action: 'Sisteme Başarılı Giriş',
            target: `Oturum: ${userEntry.username}`,
            details: `${userEntry.displayName} (${getRoleLabel(userEntry.role)}) sisteme giriş yaptı ve AES-256 veri kilidi açıldı.`,
            status: 'success'
        });

        return { ok: true, session: sessionObj };
    }

    function decryptGeojsonWithSession(sessionObj) {
        const bundle = global.ENCRYPTED_GEOJSON_DATA;
        if (!bundle || !bundle.ciphertextB64 || !sessionObj || !sessionObj.masterKeyHex) {
            return null;
        }
        const masterBytes = hexToBytes(sessionObj.masterKeyHex);
        if (masterBytes.length !== 64) return null;

        const masterAesKey = masterBytes.subarray(0, 32);
        const masterHmacKey = masterBytes.subarray(32, 64);
        const ivBytes = hexToBytes(bundle.iv);
        const ciphertextBytes = base64ToBytes(bundle.ciphertextB64);

        const macInput = new Uint8Array(ivBytes.length + ciphertextBytes.length);
        macInput.set(ivBytes, 0);
        macInput.set(ciphertextBytes, ivBytes.length);

        const computedMac = bytesToHex(hmacSha256(masterHmacKey, macInput));
        if (!constantTimeEqualHex(computedMac, bundle.mac)) {
            return null;
        }

        const plaintextBytes = aes256CtrCrypt(ciphertextBytes, masterAesKey, ivBytes);
        const jsonStr = bytesToUtf8(plaintextBytes);
        return JSON.parse(jsonStr);
    }

    function unlockAndLoadGeoJSON() {
        const sessionObj = loadSession();
        if (!sessionObj) return null;
        const liveUser = getUserByUsername(sessionObj.username);
        if (!liveUser || liveUser.status === 'pasif') {
            clearSession(false);
            return null;
        }
        // Güncel yetki ve rol bilgilerini oturuma yansıt
        sessionObj.role = liveUser.role;
        sessionObj.displayName = liveUser.displayName;
        sessionObj.department = liveUser.department;
        sessionObj.permissions = liveUser.permissions;

        try {
            const geojson = decryptGeojsonWithSession(sessionObj);
            if (!geojson || !Array.isArray(geojson.features)) {
                clearSession(false);
                return null;
            }
            global.GEOJSON_DATA = geojson;
            return sessionObj;
        } catch (err) {
            console.error('Şifreli veri çözülemedi:', err);
            clearSession(false);
            return null;
        }
    }

    // =========================================================================
    // KALICI VERİ VE PDF DEPOLAMA SERVİSİ (StorageService)
    // =========================================================================
    const pdfBlobUrlCache = {};

    function loadDeltaState() {
        try {
            const raw = localStorage.getItem(DELTA_STORAGE_KEY);
            if (raw) {
                const parsed = JSON.parse(raw);
                return {
                    overrides: parsed.overrides || {},
                    addedBuildings: Array.isArray(parsed.addedBuildings) ? parsed.addedBuildings : [],
                    updatedAt: parsed.updatedAt || null
                };
            }
        } catch (e) {
            console.warn('Delta verisi okunamadı:', e);
        }
        return { overrides: {}, addedBuildings: [], updatedAt: null };
    }

    function saveDeltaState(state) {
        state.updatedAt = new Date().toISOString();
        try {
            localStorage.setItem(DELTA_STORAGE_KEY, JSON.stringify(state));
        } catch (e) {
            console.error('Delta verisi kaydedilemedi:', e);
        }
    }

    function sanitizeBuildingForSave(b) {
        if (!b) return null;
        const copy = {};
        Object.keys(b).forEach(k => {
            if (k === 'layer' || k === 'rawFeature') return;
            copy[k] = b[k];
        });
        return copy;
    }

    function saveBuildingOverride(b) {
        if (!b || b.id === undefined || b.id === null) return;
        const state = loadDeltaState();
        const key = String(b.id);

        // Eğer sonradan eklenen bir yapıysa addedBuildings içinde de güncelle
        const addedIdx = state.addedBuildings.findIndex(item => String(item.id) === key);
        if (addedIdx !== -1) {
            state.addedBuildings[addedIdx] = sanitizeBuildingForSave(b);
        }

        const overridePayload = {
            id: b.id,
            maks: b.maks,
            stage: b.stage,
            stageText: b.stageText,
            color: b.color,
            zoningStatus: b.zoningStatus,
            zoningStatusText: b.zoningStatusText,
            timeline: Array.isArray(b.timeline) ? b.timeline.map(t => ({ ...t })) : [],
            tebligatGonderildi: Boolean(b.tebligatGonderildi),
            tebligatDurumu: b.tebligatDurumu || null,
            tebligatBitisTarihi: b.tebligatBitisTarihi || null,
            malikler: Array.isArray(b.malikler) ? b.malikler.map(m => ({ ...m })) : undefined,
            imarPdf: b.imarPdf || null,
            imarPdfName: b.imarPdfName || null,
            onincelemePdf: b.onincelemePdf || null,
            onincelemePdfName: b.onincelemePdfName || null,
            tebligatPdf: b.tebligatPdf || null,
            tebligatPdfName: b.tebligatPdfName || null,
            updatedAt: new Date().toISOString()
        };
        state.overrides[key] = overridePayload;
        saveDeltaState(state);

        const session = loadSession();
        apiRequest('/api/buildings/update', 'POST', {
            building: overridePayload,
            updatedBy: session ? session.username : 'sistem'
        });
    }

    function saveAddedBuilding(b) {
        if (!b) return;
        const state = loadDeltaState();
        const clean = sanitizeBuildingForSave(b);
        const existingIdx = state.addedBuildings.findIndex(item => String(item.id) === String(b.id));
        if (existingIdx !== -1) {
            state.addedBuildings[existingIdx] = clean;
        } else {
            state.addedBuildings.push(clean);
        }
        saveDeltaState(state);
    }

    function removeBuildingOverride(bId) {
        if (bId === undefined || bId === null) return;
        const state = loadDeltaState();
        delete state.overrides[String(bId)];
        saveDeltaState(state);
    }

    function getBuildingOverrides() {
        const state = loadDeltaState();
        return state.overrides || {};
    }

    function applyToBuildings(buildingList, buildingsMap, districtSet) {
        const state = loadDeltaState();
        const overrides = state.overrides || {};

        // Mevcut 759 binanın üzerine kaydedilmiş değişiklikleri uygula
        buildingList.forEach(b => {
            const ov = overrides[String(b.id)];
            if (ov) {
                if (ov.stage !== undefined) b.stage = ov.stage;
                if (ov.stageText) b.stageText = ov.stageText;
                if (ov.color) b.color = ov.color;
                if (ov.zoningStatus) b.zoningStatus = ov.zoningStatus;
                if (ov.zoningStatusText) b.zoningStatusText = ov.zoningStatusText;
                if (Array.isArray(ov.timeline)) b.timeline = ov.timeline;
                if (ov.tebligatGonderildi !== undefined) b.tebligatGonderildi = ov.tebligatGonderildi;
                if (ov.tebligatDurumu) b.tebligatDurumu = ov.tebligatDurumu;
                if (ov.tebligatBitisTarihi) b.tebligatBitisTarihi = ov.tebligatBitisTarihi;
                if (Array.isArray(ov.malikler)) b.malikler = ov.malikler;
                if (ov.imarPdf) b.imarPdf = ov.imarPdf;
                if (ov.imarPdfName) b.imarPdfName = ov.imarPdfName;
                if (ov.onincelemePdf) b.onincelemePdf = ov.onincelemePdf;
                if (ov.onincelemePdfName) b.onincelemePdfName = ov.onincelemePdfName;
                if (ov.tebligatPdf) b.tebligatPdf = ov.tebligatPdf;
                if (ov.tebligatPdfName) b.tebligatPdfName = ov.tebligatPdfName;
            }
        });
    }

    // --- IndexedDB ve SQLite PDF Depolama ---
    function openPdfDb() {
        return new Promise((resolve, reject) => {
            if (typeof indexedDB === 'undefined') {
                resolve(null);
                return;
            }
            const req = indexedDB.open(IDB_NAME, IDB_VERSION);
            req.onupgradeneeded = (e) => {
                const db = e.target.result;
                if (!db.objectStoreNames.contains(IDB_PDF_STORE)) {
                    db.createObjectStore(IDB_PDF_STORE, { keyPath: 'id' });
                }
            };
            req.onsuccess = (e) => resolve(e.target.result);
            req.onerror = () => resolve(null);
        });
    }

    function fileToDataUrl(fileOrBlob) {
        return new Promise((resolve, reject) => {
            const reader = new FileReader();
            reader.onload = () => resolve(reader.result);
            reader.onerror = (err) => reject(err);
            reader.readAsDataURL(fileOrBlob);
        });
    }

    function dataUrlToBlob(dataUrl) {
        const parts = dataUrl.split(',');
        const mimeMatch = parts[0].match(/:(.*?);/);
        const mime = mimeMatch ? mimeMatch[1] : 'application/pdf';
        const bytes = base64ToBytes(parts[1]);
        return new Blob([bytes], { type: mime });
    }

    async function savePdfFile(file, buildingId = null) {
        if (!file) return null;
        const pdfId = 'idb-pdf://pdf_' + Date.now() + '_' + Math.random().toString(36).slice(2, 8);
        const dataUrl = await fileToDataUrl(file);
        const blobUrl = URL.createObjectURL(file);
        pdfBlobUrlCache[pdfId] = blobUrl;

        const db = await openPdfDb();
        if (db) {
            await new Promise((resolve) => {
                const tx = db.transaction(IDB_PDF_STORE, 'readwrite');
                tx.objectStore(IDB_PDF_STORE).put({
                    id: pdfId,
                    name: file.name || 'evrak.pdf',
                    dataUrl: dataUrl,
                    createdAt: new Date().toISOString()
                });
                tx.oncomplete = () => resolve();
                tx.onerror = () => resolve();
            });
        }

        const session = loadSession();
        apiRequest('/api/pdfs/upload', 'POST', {
            id: pdfId,
            name: file.name || 'evrak.pdf',
            dataUrl: dataUrl,
            buildingId: buildingId,
            uploadedBy: session ? session.username : 'sistem'
        });

        return pdfId;
    }

    async function resolvePdfUrl(urlOrKey) {
        if (!urlOrKey || typeof urlOrKey !== 'string') return urlOrKey;
        if (!urlOrKey.startsWith('idb-pdf://')) return urlOrKey;
        if (pdfBlobUrlCache[urlOrKey]) return pdfBlobUrlCache[urlOrKey];

        const db = await openPdfDb();
        if (db) {
            const localResolved = await new Promise((resolve) => {
                const tx = db.transaction(IDB_PDF_STORE, 'readonly');
                const req = tx.objectStore(IDB_PDF_STORE).get(urlOrKey);
                req.onsuccess = () => {
                    const rec = req.result;
                    if (rec && rec.dataUrl) {
                        const blob = dataUrlToBlob(rec.dataUrl);
                        const blobUrl = URL.createObjectURL(blob);
                        pdfBlobUrlCache[urlOrKey] = blobUrl;
                        resolve(blobUrl);
                    } else {
                        resolve(null);
                    }
                };
                req.onerror = () => resolve(null);
            });
            if (localResolved) return localResolved;
        }

        // Yerel IndexedDB'de yoksa SQLite veritabanı sunucusundan getir
        const remotePdf = await apiRequest('/api/pdfs/get?id=' + encodeURIComponent(urlOrKey), 'GET');
        if (remotePdf && remotePdf.ok && remotePdf.dataUrl) {
            const blob = dataUrlToBlob(remotePdf.dataUrl);
            const blobUrl = URL.createObjectURL(blob);
            pdfBlobUrlCache[urlOrKey] = blobUrl;
            return blobUrl;
        }

        return urlOrKey;
    }

    async function getAllStoredPdfs() {
        const db = await openPdfDb();
        if (!db) return [];
        return new Promise((resolve) => {
            const tx = db.transaction(IDB_PDF_STORE, 'readonly');
            const req = tx.objectStore(IDB_PDF_STORE).getAll();
            req.onsuccess = () => resolve(req.result || []);
            req.onerror = () => resolve([]);
        });
    }

    async function restoreStoredPdfs(pdfList) {
        if (!Array.isArray(pdfList) || pdfList.length === 0) return;
        const db = await openPdfDb();
        if (!db) return;
        await new Promise((resolve) => {
            const tx = db.transaction(IDB_PDF_STORE, 'readwrite');
            const store = tx.objectStore(IDB_PDF_STORE);
            pdfList.forEach(item => {
                if (item && item.id && item.dataUrl) {
                    store.put(item);
                }
            });
            tx.oncomplete = () => resolve();
            tx.onerror = () => resolve();
        });
    }

    async function exportBackup() {
        const state = loadDeltaState();
        const pdfs = await getAllStoredPdfs();
        const backupObj = {
            app: 'IzmirKentVizyonGIS',
            version: 1,
            exportedAt: new Date().toISOString(),
            deltaState: state,
            pdfs: pdfs
        };
        const jsonStr = JSON.stringify(backupObj, null, 2);
        const blob = new Blob([jsonStr], { type: 'application/json' });
        const url = URL.createObjectURL(blob);
        const a = document.createElement('a');
        const dateStr = new Date().toISOString().split('T')[0];
        a.href = url;
        a.download = `kentvizyon_yedek_${dateStr}.json`;
        document.body.appendChild(a);
        a.click();
        setTimeout(() => {
            a.remove();
            URL.revokeObjectURL(url);
        }, 250);
    }

    async function importBackupFile(file) {
        const text = await new Promise((resolve, reject) => {
            const r = new FileReader();
            r.onload = () => resolve(r.result);
            r.onerror = (e) => reject(e);
            r.readAsText(file, 'utf-8');
        });
        const parsed = JSON.parse(text);
        if (!parsed || !parsed.deltaState) {
            throw new Error('Geçersiz yedek dosyası formatı.');
        }
        saveDeltaState(parsed.deltaState);
        if (Array.isArray(parsed.pdfs)) {
            await restoreStoredPdfs(parsed.pdfs);
        }
        return parsed;
    }

    async function resetAllChanges() {
        try { localStorage.removeItem(DELTA_STORAGE_KEY); } catch (e) {}
        const db = await openPdfDb();
        if (db) {
            await new Promise((resolve) => {
                const tx = db.transaction(IDB_PDF_STORE, 'readwrite');
                tx.objectStore(IDB_PDF_STORE).clear();
                tx.oncomplete = () => resolve();
                tx.onerror = () => resolve();
            });
        }
    }

    function getChangeStats() {
        const state = loadDeltaState();
        return {
            overrideCount: Object.keys(state.overrides || {}).length,
            addedCount: 0,
            updatedAt: state.updatedAt
        };
    }

    global.DatabaseClient = {
        syncFromDatabase: syncFromDatabase,
        getStatus: () => ({ ...dbConnectionState }),
        checkServerStatus: () => apiRequest('/api/status', 'GET')
    };

    // Sayfa yüklendiğinde arka planda SQLite veritabanı sunucusu ile otomatik senkronize ol
    if (typeof setTimeout === 'function') {
        setTimeout(() => {
            syncFromDatabase();
        }, 50);
    }

    global.AuthSecurity = {
        authenticate: authenticate,
        unlockAndLoadGeoJSON: unlockAndLoadGeoJSON,
        loadSession: loadSession,
        clearSession: clearSession,
        getUsers: getUsers,
        getUserByUsername: getUserByUsername,
        createOrUpdateUser: createOrUpdateUser,
        updateUserPermissions: updateUserPermissions,
        toggleUserStatus: toggleUserStatus,
        deleteUser: deleteUser,
        hasPermission: hasPermission,
        getDefaultPermissionsForRole: getDefaultPermissionsForRole,
        getRoleLabel: getRoleLabel,
        logAudit: logAudit,
        getAuditLogs: getAuditLogs,
        clearAuditLogs: clearAuditLogs,
        syncFromDatabase: syncFromDatabase
    };

    global.StorageService = {
        saveBuildingOverride: saveBuildingOverride,
        removeBuildingOverride: removeBuildingOverride,
        getBuildingOverrides: getBuildingOverrides,
        applyToBuildings: applyToBuildings,
        savePdfFile: savePdfFile,
        resolvePdfUrl: resolvePdfUrl,
        getAllStoredPdfs: getAllStoredPdfs,
        exportBackup: exportBackup,
        importBackupFile: importBackupFile,
        resetAllChanges: resetAllChanges,
        getChangeStats: getChangeStats
    };
})(typeof window !== 'undefined' ? window : globalThis);

