// github-forge — a GitHub-compatible git forge in a single file.
//
// Node 22 standard library only: no dependencies, no git binary, no outside
// service, no UI. One process serves, from its own in-memory store:
//
//   * git smart HTTP v2  (/info/refs, /git-upload-pack, /git-receive-pack)
//   * REST v3            (/api/v3/...)
//   * GraphQL            (/api/graphql)
//   * MCP over JSON-RPC  (/mcp)
//
// Determinism: every timestamp the server stamps on a commit is fixed, every
// id is assigned from a counter, and no clock or random value enters any
// stored object, so two runs fed the same requests leave the same state.
//
// Lifecycle: when MAKEFUN_ENV_URL is set, the process binds an ephemeral
// port, POSTs it to $MAKEFUN_ENV_URL/register, then polls
// $MAKEFUN_ENV_URL/done until the suite answers {"done": true} and exits 0.
// Without it (local practice runs) it listens on $PORT (default 0) and stays
// up until killed.

import http from 'node:http';
import crypto from 'node:crypto';
import zlib from 'node:zlib';
import { Buffer } from 'node:buffer';

// ---------------------------------------------------------------------------
// constants

const VIEWER_LOGIN = 'adaiversen';
const VIEWER_ID = 1000;
const VIEWER_NAME = 'ada iversen';
const VIEWER_EMAIL = 'adaiversen@example.invalid';
const ZERO_OID = '0000000000000000000000000000000000000000';
const FIXED_EPOCH = 1700000000; // every server-made commit carries this time
const COMMIT_IDENTITY = 'Conformance <conformance@make.fun>';
const AGENT = 'forge/1.0';
const SERVER_NAME = 'github-forge';
const SERVER_VERSION = '1.0.0';
const MCP_REVISION = '2026-07-28';
const MAX_BODY_BYTES = 64 * 1024 * 1024;

const SHOP_TOKEN = process.env.MAKEFUN_SHOP_TOKEN ?? '';
const ENV_URL = (process.env.MAKEFUN_ENV_URL ?? '').replace(/\/+$/, '');

// ---------------------------------------------------------------------------
// small utilities

function sha1hex(buf) {
  return crypto.createHash('sha1').update(buf).digest('hex');
}

/** The git object id of a typed object: SHA-1 over "<type> <size>\0" + bytes. */
function hashObject(type, data) {
  const head = Buffer.from(`${type} ${data.length}\0`, 'ascii');
  return sha1hex(Buffer.concat([head, data]));
}

function b64encode(buf) {
  return Buffer.from(buf).toString('base64');
}

function b64decode(text) {
  return Buffer.from(text, 'base64');
}

function isOid(value) {
  return typeof value === 'string' && /^[0-9a-f]{40}$/.test(value);
}

function clampInt(value, min, max, fallback) {
  if (typeof value !== 'number' || !Number.isFinite(value)) return fallback;
  return Math.min(max, Math.max(min, Math.trunc(value)));
}

let requestCounter = 0;
function nextRequestId() {
  requestCounter += 1;
  return `req-${requestCounter}`;
}

// ---------------------------------------------------------------------------
// pkt-line framing (git wire protocol)

function pktLine(payload) {
  const body = typeof payload === 'string' ? Buffer.from(payload, 'utf8') : payload;
  const head = Buffer.alloc(4);
  head.write((body.length + 4).toString(16).padStart(4, '0'), 'ascii');
  return Buffer.concat([head, body]);
}

const PKT_FLUSH = Buffer.from('0000', 'ascii');
const PKT_DELIM = Buffer.from('0001', 'ascii');

function encodePktLines(items) {
  const parts = [];
  for (const item of items) {
    if (item === 'flush') parts.push(PKT_FLUSH);
    else if (item === 'delim') parts.push(PKT_DELIM);
    else parts.push(pktLine(item));
  }
  return Buffer.concat(parts);
}

/**
 * Decode pkt-lines from a buffer. Returns { packets, rest } where packets are
 * { kind: 'data'|'flush'|'delim'|'response-end', payload? } and rest is the
 * bytes after the first flush packet (the pack bytes in a receive-pack body).
 * Stops at the first flush when stopAtFlush is true (the default).
 */
function decodePktLines(buf, stopAtFlush = true) {
  const packets = [];
  let off = 0;
  while (off + 4 <= buf.length) {
    const len = parseInt(buf.subarray(off, off + 4).toString('ascii'), 16);
    if (Number.isNaN(len) || len < 0) break;
    if (len === 0) {
      packets.push({ kind: 'flush' });
      off += 4;
      if (stopAtFlush) break;
      continue;
    }
    if (len === 1) {
      packets.push({ kind: 'delim' });
      off += 4;
      continue;
    }
    if (len === 2) {
      packets.push({ kind: 'response-end' });
      off += 4;
      continue;
    }
    if (len < 4 || off + len > buf.length) break;
    packets.push({ kind: 'data', payload: buf.subarray(off + 4, off + len) });
    off += len;
  }
  return { packets, rest: buf.subarray(off) };
}

/**
 * Split a buffer into sideband packets (band byte + data). A pkt-line is at
 * most 65520 bytes including its 4-byte length, so a sideband payload (band
 * byte + data) is at most 65516 bytes and the data at most 65515.
 */
function sidebandPackets(band, data) {
  const out = [];
  const CHUNK = 65515;
  if (data.length === 0) {
    out.push(pktLine(Buffer.concat([Buffer.from([band]), data])));
    return out;
  }
  for (let off = 0; off < data.length; off += CHUNK) {
    const piece = data.subarray(off, Math.min(data.length, off + CHUNK));
    out.push(pktLine(Buffer.concat([Buffer.from([band]), piece])));
  }
  return out;
}

// ---------------------------------------------------------------------------
// git objects: commit / tree / tag bodies

function buildCommitBytes({ tree, parents, message, author, committer }) {
  const a = author ?? COMMIT_IDENTITY;
  const c = committer ?? COMMIT_IDENTITY;
  const lines = [`tree ${tree}`];
  for (const p of parents) lines.push(`parent ${p}`);
  lines.push(`author ${a} ${FIXED_EPOCH} +0000`);
  lines.push(`committer ${c} ${FIXED_EPOCH} +0000`);
  lines.push('');
  lines.push(message);
  return Buffer.from(lines.join('\n'), 'utf8');
}

function parseCommit(data) {
  const text = data.toString('utf8');
  const split = text.indexOf('\n\n');
  const header = split === -1 ? text : text.slice(0, split);
  const message = split === -1 ? '' : text.slice(split + 2);
  let tree = '';
  const parents = [];
  let author = '';
  let committer = '';
  for (const line of header.split('\n')) {
    if (line.startsWith('tree ')) tree = line.slice(5).trim();
    else if (line.startsWith('parent ')) parents.push(line.slice(7).trim());
    else if (line.startsWith('author ')) author = line.slice(7);
    else if (line.startsWith('committer ')) committer = line.slice(10);
  }
  return { tree, parents, message, author, committer };
}

function buildTagBytes({ object, type, tag, tagger, message }) {
  const t = tagger ?? COMMIT_IDENTITY;
  const lines = [`object ${object}`, `type ${type}`, `tag ${tag}`, `tagger ${t} ${FIXED_EPOCH} +0000`, '', message];
  return Buffer.from(lines.join('\n'), 'utf8');
}

function parseTag(data) {
  const text = data.toString('utf8');
  const split = text.indexOf('\n\n');
  const header = split === -1 ? text : text.slice(0, split);
  const message = split === -1 ? '' : text.slice(split + 2);
  let object = '';
  let type = '';
  let tag = '';
  for (const line of header.split('\n')) {
    if (line.startsWith('object ')) object = line.slice(7).trim();
    else if (line.startsWith('type ')) type = line.slice(5).trim();
    else if (line.startsWith('tag ')) tag = line.slice(4).trim();
  }
  return { object, type, tag, message };
}

/** A tree entry: { mode, name, oid }. Modes are git's strings: '100644', '100755', '40000', '120000'. */
function buildTreeBytes(entries) {
  const parts = [];
  for (const entry of entries) {
    parts.push(Buffer.from(`${entry.mode} ${entry.name}\0`, 'utf8'));
    parts.push(Buffer.from(entry.oid, 'hex'));
  }
  return Buffer.concat(parts);
}

function parseTree(data) {
  const entries = [];
  let off = 0;
  while (off < data.length) {
    const space = data.indexOf(0x20, off);
    if (space === -1) break;
    const nul = data.indexOf(0x00, space);
    if (nul === -1 || nul + 21 > data.length) break;
    entries.push({
      mode: data.subarray(off, space).toString('ascii'),
      name: data.subarray(space + 1, nul).toString('utf8'),
      oid: data.subarray(nul + 1, nul + 21).toString('hex'),
    });
    off = nul + 21;
  }
  return entries;
}

/** Git's tree sort: a directory compares as if its name ended in '/'. */
function sortTreeEntries(entries) {
  const key = (entry) => (entry.mode === '40000' ? `${entry.name}/` : entry.name);
  return [...entries].sort((a, b) => {
    const ka = key(a);
    const kb = key(b);
    return ka < kb ? -1 : ka > kb ? 1 : 0;
  });
}

function isDirMode(mode) {
  return mode === '40000';
}

// ---------------------------------------------------------------------------
// packfiles

const TYPE_CODE = { commit: 1, tree: 2, blob: 3, tag: 4 };
const CODE_TYPE = { 1: 'commit', 2: 'tree', 3: 'blob', 4: 'tag' };

/** Build a packfile (version 2) from plain objects — no deltas, self-contained. */
function writePack(objects) {
  const parts = [];
  const head = Buffer.alloc(12);
  head.write('PACK', 0, 4, 'ascii');
  head.writeUInt32BE(2, 4);
  head.writeUInt32BE(objects.length, 8);
  parts.push(head);
  for (const obj of objects) {
    const typeCode = TYPE_CODE[obj.type];
    if (typeCode === undefined) throw new Error(`cannot pack object of type ${obj.type}`);
    const deflated = zlib.deflateSync(obj.data, { level: 6 });
    let size = obj.data.length;
    const first = (typeCode << 4) | (size & 0x0f);
    size >>= 4;
    const varint = [];
    if (size === 0) {
      varint.push(first);
    } else {
      varint.push(first | 0x80);
      while (size > 0) {
        const byte = size & 0x7f;
        size >>= 7;
        varint.push(size > 0 ? byte | 0x80 : byte);
      }
    }
    parts.push(Buffer.from(varint));
    parts.push(deflated);
  }
  const body = Buffer.concat(parts);
  const trailer = crypto.createHash('sha1').update(body).digest();
  return Buffer.concat([body, trailer]);
}

/**
 * Inflate exactly one zlib stream starting at `off`, knowing its inflated
 * size. A streaming Inflate consumes only that stream's bytes and reports
 * them as `bytesWritten` once it ends, so one inflate per object finds the
 * stream's true end without searching. The output length is checked against
 * the declared size.
 */
function inflateOne(buf, off, expectedSize) {
  return new Promise((resolve, reject) => {
    const inf = zlib.createInflate();
    const chunks = [];
    let settled = false;
    inf.on('data', (chunk) => chunks.push(chunk));
    inf.on('error', (err) => {
      if (!settled) {
        settled = true;
        reject(err);
      }
    });
    inf.on('end', () => {
      if (settled) return;
      settled = true;
      const data = Buffer.concat(chunks);
      if (data.length !== expectedSize) {
        reject(new Error('pack object does not inflate to its declared size'));
        return;
      }
      const end = off + inf.bytesWritten;
      if (end <= off || end > buf.length) {
        reject(new Error('pack object has an implausible compressed length'));
        return;
      }
      resolve({ data, end });
    });
    inf.write(buf.subarray(off));
    inf.end();
  });
}

/** Apply a delta (copy/insert ops) to a base object's bytes. */
function applyDelta(base, delta) {
  let pos = 0;
  const readVarint = () => {
    let value = 0;
    let shift = 0;
    for (;;) {
      const byte = delta[pos++];
      value |= (byte & 0x7f) << shift;
      shift += 7;
      if (!(byte & 0x80)) break;
    }
    return value;
  };
  const sourceSize = readVarint();
  const targetSize = readVarint();
  if (sourceSize !== base.length) throw new Error('delta base size mismatch');
  const out = [];
  let produced = 0;
  while (pos < delta.length) {
    const op = delta[pos++];
    if (op & 0x80) {
      let offset = 0;
      let size = 0;
      if (op & 0x01) offset = delta[pos++];
      if (op & 0x02) offset |= delta[pos++] << 8;
      if (op & 0x04) offset |= delta[pos++] << 16;
      if (op & 0x08) offset |= delta[pos++] << 24;
      if (op & 0x10) size = delta[pos++];
      if (op & 0x20) size |= delta[pos++] << 8;
      if (op & 0x40) size |= delta[pos++] << 16;
      if (size === 0) size = 0x10000;
      out.push(base.subarray(offset, offset + size));
      produced += size;
    } else if (op !== 0) {
      out.push(delta.subarray(pos, pos + op));
      pos += op;
      produced += op;
    } else {
      throw new Error('delta op 0 is reserved');
    }
  }
  if (produced !== targetSize) throw new Error('delta target size mismatch');
  return Buffer.concat(out);
}

/**
 * Parse a packfile (version 2 or 3) into a Map of oid -> { type, data },
 * resolving OFS_DELTA and REF_DELTA entries. `lookup` resolves a REF_DELTA
 * base the pack itself does not carry (a thin pack's already-held object).
 * Returns { objects, deltaCount }.
 */
async function readPack(buf, lookup) {
  if (buf.length < 32 || buf.subarray(0, 4).toString('ascii') !== 'PACK') {
    throw new Error('pack does not start with PACK');
  }
  const version = buf.readUInt32BE(4);
  if (version !== 2 && version !== 3) throw new Error(`unsupported pack version ${version}`);
  const count = buf.readUInt32BE(8);
  // Verify the trailer checksum over the body (everything but the last 20 bytes).
  const trailer = buf.subarray(buf.length - 20).toString('hex');
  const expected = sha1hex(buf.subarray(0, buf.length - 20));
  if (trailer !== expected) throw new Error('pack trailer checksum mismatch');
  const objects = new Map();
  const byOffset = new Map();
  const refDeltas = [];
  let deltaCount = 0;
  let off = 12;
  for (let i = 0; i < count; i += 1) {
    const entryStart = off;
    let byte = buf[off++];
    const typeCode = (byte >> 4) & 0x07;
    let size = byte & 0x0f;
    let shift = 4;
    while (byte & 0x80) {
      byte = buf[off++];
      size |= (byte & 0x7f) << shift;
      shift += 7;
    }
    let base = null;
    if (typeCode === 6) {
      deltaCount += 1;
      byte = buf[off++];
      let deltaOffset = byte & 0x7f;
      while (byte & 0x80) {
        byte = buf[off++];
        deltaOffset = ((deltaOffset + 1) << 7) | (byte & 0x7f);
      }
      base = byOffset.get(entryStart - deltaOffset) ?? null;
      if (!base) throw new Error('ofs-delta base not found in pack');
    } else if (typeCode === 7) {
      deltaCount += 1;
      const baseOid = buf.subarray(off, off + 20).toString('hex');
      off += 20;
      base = objects.get(baseOid) ?? null;
      if (!base) {
        // The base is not in this pack (thin pack) or not yet read; defer.
        refDeltas.push({ entryStart, baseOid, off, size });
        // Skip this entry's data for now; resolve after the first pass.
        const inflated = await inflateOne(buf, off, size);
        refDeltas[refDeltas.length - 1].delta = inflated.data;
        off = inflated.end;
        continue;
      }
    }
    const inflated = await inflateOne(buf, off, size);
    off = inflated.end;
    if (typeCode === 6 || typeCode === 7) {
      const data = applyDelta(base.data, inflated.data);
      const obj = { type: base.type, data };
      const oid = hashObject(obj.type, data);
      objects.set(oid, obj);
      byOffset.set(entryStart, obj);
    } else {
      const type = CODE_TYPE[typeCode];
      if (!type) throw new Error(`unknown pack object type ${typeCode}`);
      const obj = { type, data: inflated.data };
      const oid = hashObject(type, inflated.data);
      objects.set(oid, obj);
      byOffset.set(entryStart, obj);
    }
  }
  // The objects must end exactly where the trailer begins; a drift means a
  // compressed length was misread.
  if (off !== buf.length - 20) throw new Error('pack objects do not end at the trailer');
  // Resolve deferred REF_DELTAs (bases that arrived later in the pack or are held).
  for (const pending of refDeltas) {
    let base = objects.get(pending.baseOid) ?? null;
    if (!base && lookup) base = lookup(pending.baseOid) ?? null;
    if (!base) throw new Error(`ref-delta base ${pending.baseOid} not found`);
    const data = applyDelta(base.data, pending.delta);
    const obj = { type: base.type, data };
    objects.set(hashObject(obj.type, data), obj);
  }
  return { objects, deltaCount };
}

// ---------------------------------------------------------------------------
// the store: repositories, issues, pull requests, labels, comments

const store = {
  repos: new Map(), // key: owner.toLowerCase() + '/' + name.toLowerCase()
  nextRepoId: 5000,
  nextIssueId: 1, // global REST `id` for issues and pull requests alike
  nextCommentId: 1,
  repoSeq: 0, // creation order, for stable list ordering
};

function repoKey(owner, name) {
  return `${owner.toLowerCase()}/${name.toLowerCase()}`;
}

function createRepoRecord({ name, owner, description, isPrivate }) {
  const id = store.nextRepoId++;
  store.repoSeq += 1;
  const repo = {
    id,
    name,
    owner,
    description: description ?? '',
    private: isPrivate ?? false,
    defaultBranch: 'main',
    createdSeq: store.repoSeq,
    objects: new Map(), // oid -> { type, data }
    refs: new Map(), // 'refs/heads/main' -> oid; 'refs/tags/v1' -> oid
    issues: [], // in creation order
    pulls: [], // in creation order
    labels: new Map(), // name -> { name, color }
    nextNumber: 1, // shared issue / pull-request number sequence
    comments: new Map(), // issue-or-pr number -> [{ id, body, seq }]
  };
  store.repos.set(repoKey(owner, name), repo);
  return repo;
}

function findRepo(owner, name) {
  return store.repos.get(repoKey(owner, name)) ?? null;
}

function listReposFor(owner) {
  const out = [];
  for (const repo of store.repos.values()) {
    if (repo.owner.toLowerCase() === owner.toLowerCase()) out.push(repo);
  }
  out.sort((a, b) => a.createdSeq - b.createdSeq);
  return out;
}

function deleteRepo(owner, name) {
  return store.repos.delete(repoKey(owner, name));
}

/** Store an object, returning its oid. */
function putObject(repo, type, data) {
  const oid = hashObject(type, data);
  if (!repo.objects.has(oid)) repo.objects.set(oid, { type, data });
  return oid;
}

function getObject(repo, oid) {
  return repo.objects.get(oid) ?? null;
}

/** The tip oid of a ref, or null. */
function refTip(repo, ref) {
  return repo.refs.get(ref) ?? null;
}

/** All refs sorted by name, as { name, oid } pairs. */
function sortedRefs(repo) {
  return [...repo.refs.entries()].map(([name, oid]) => ({ name, oid })).sort((a, b) => (a.name < b.name ? -1 : 1));
}

/** Resolve HEAD: the default branch's tip, or null when the repo is unborn. */
function headTip(repo) {
  return refTip(repo, `refs/heads/${repo.defaultBranch}`);
}

/**
 * Is `ancestor` reachable from `tip` by following parents? Used for the
 * fast-forward check on push. `tip` itself counts as reachable from itself.
 */
function isAncestor(repo, ancestor, tip) {
  if (ancestor === tip) return true;
  const seen = new Set();
  const stack = [tip];
  while (stack.length > 0) {
    const oid = stack.pop();
    if (oid === ancestor) return true;
    if (seen.has(oid)) continue;
    seen.add(oid);
    const obj = getObject(repo, oid);
    if (!obj || obj.type !== 'commit') continue;
    for (const parent of parseCommit(obj.data).parents) stack.push(parent);
  }
  return false;
}

/** The set of commit oids reachable from `roots` (parents followed). */
function reachableCommits(repo, roots) {
  const out = new Set();
  const stack = [...roots];
  while (stack.length > 0) {
    const oid = stack.pop();
    if (out.has(oid)) continue;
    const obj = getObject(repo, oid);
    if (!obj) continue;
    if (obj.type === 'tag') {
      out.add(oid);
      stack.push(parseTag(obj.data).object);
      continue;
    }
    if (obj.type !== 'commit') {
      out.add(oid);
      continue;
    }
    out.add(oid);
    for (const parent of parseCommit(obj.data).parents) stack.push(parent);
  }
  return out;
}

/**
 * Build (or rebuild) the tree for a path change. `files` is a Map of full
 * path -> blob oid for the whole tree; returns the root tree oid.
 * Implemented by nesting the paths into a directory tree and hashing
 * bottom-up, so a contents write is one root commit over a real tree.
 */
function buildTreeFromFiles(repo, files) {
  // A nested map: name -> Map (directory) or blob oid (file).
  const root = new Map();
  for (const [path, blobOid] of files) {
    const parts = path.split('/').filter((part) => part !== '');
    let node = root;
    for (let i = 0; i < parts.length; i += 1) {
      const part = parts[i];
      if (i === parts.length - 1) {
        node.set(part, blobOid);
      } else {
        if (!node.has(part)) node.set(part, new Map());
        node = node.get(part);
      }
    }
  }
  const writeNode = (node) => {
    const entries = [];
    for (const [name, value] of node) {
      if (typeof value === 'string') entries.push({ mode: '100644', name, oid: value });
      else entries.push({ mode: '40000', name, oid: writeNode(value) });
    }
    return putObject(repo, 'tree', buildTreeBytes(sortTreeEntries(entries)));
  };
  return writeNode(root);
}

/** Flatten a tree (by oid) into a Map of full path -> { mode, oid } for files. */
function flattenTree(repo, treeOid) {
  const files = new Map();
  const walk = (oid, prefix) => {
    const obj = getObject(repo, oid);
    if (!obj || obj.type !== 'tree') return;
    for (const entry of parseTree(obj.data)) {
      const path = prefix === '' ? entry.name : `${prefix}/${entry.name}`;
      if (isDirMode(entry.mode)) walk(entry.oid, path);
      else files.set(path, { mode: entry.mode, oid: entry.oid });
    }
  };
  walk(treeOid, '');
  return files;
}

/** The tree oid of a directory inside a tree, or null. */
function treeOidForPath(repo, treeOid, path) {
  if (path === '') return treeOid;
  const parts = path.split('/').filter((p) => p !== '');
  let current = treeOid;
  for (const part of parts) {
    const obj = getObject(repo, current);
    if (!obj || obj.type !== 'tree') return null;
    const entry = parseTree(obj.data).find((e) => e.name === part && isDirMode(e.mode));
    if (!entry) return null;
    current = entry.oid;
  }
  return current;
}

/** Read one file's blob from a tree, or null. */
function readFileFromTree(repo, treeOid, path) {
  const files = flattenTree(repo, treeOid);
  const entry = files.get(path);
  if (!entry) return null;
  const blob = getObject(repo, entry.oid);
  return blob && blob.type === 'blob' ? blob.data : null;
}

/**
 * Create a commit on `branch` that writes `path` with `content` (a Buffer),
 * on top of the branch's current tip (or as the first commit when unborn).
 * Returns { commitOid, blobOid, parentOid }.
 */
function commitFile(repo, { branch, path, content, message }) {
  // A write to a branch that does not exist yet starts that branch from the
  // default branch's tip (GitHub's behaviour), not from a disconnected root.
  let parentOid = refTip(repo, `refs/heads/${branch}`);
  if (!parentOid && branch !== repo.defaultBranch) parentOid = headTip(repo);
  const files = new Map();
  if (parentOid) {
    const parent = getObject(repo, parentOid);
    if (parent && parent.type === 'commit') {
      for (const [p, entry] of flattenTree(repo, parseCommit(parent.data).tree)) {
        files.set(p, entry.oid);
      }
    }
  }
  const blobOid = putObject(repo, 'blob', content);
  files.set(path, blobOid);
  const treeOid = buildTreeFromFiles(repo, files);
  const parents = parentOid ? [parentOid] : [];
  const commitOid = putObject(repo, 'commit', buildCommitBytes({ tree: treeOid, parents, message }));
  repo.refs.set(`refs/heads/${branch}`, commitOid);
  return { commitOid, blobOid, parentOid };
}

/** Delete `path` from `branch` in a new commit. Returns the commit oid, or null when the path is absent. */
function deleteFile(repo, { branch, path, message }) {
  const parentOid = refTip(repo, `refs/heads/${branch}`);
  if (!parentOid) return null;
  const parent = getObject(repo, parentOid);
  if (!parent || parent.type !== 'commit') return null;
  const files = flattenTree(repo, parseCommit(parent.data).tree);
  if (!files.has(path)) return null;
  const remaining = new Map();
  for (const [p, entry] of files) {
    if (p !== path) remaining.set(p, entry.oid);
  }
  const treeOid = buildTreeFromFiles(repo, remaining);
  const commitOid = putObject(repo, 'commit', buildCommitBytes({ tree: treeOid, parents: [parentOid], message }));
  repo.refs.set(`refs/heads/${branch}`, commitOid);
  return commitOid;
}

// ---------------------------------------------------------------------------
// fetch object selection (shared by v2 and v0)

/**
 * Decide which objects a fetch sends.
 *
 * wants: commit/tag oids the client asked for.
 * haves: commit oids the client already holds.
 * shallowReq: oids the client holds as shallow boundaries (it has them, but
 *   not their parents).
 * deepen: a depth limit (null = no limit). Depth 0 is the want itself.
 *
 * Returns { objects: Map<oid, {type, data}> to send (commits, tags, trees,
 * blobs), shallow: new shallow-boundary oids, unshallow: old boundaries now
 * deepened past, acks: haves that are common (in the repo and an ancestor of
 * a want, or equal to one) }.
 */
function selectFetch(repo, { wants, haves, shallowReq, deepen }) {
  const shallowSet = new Set(shallowReq);
  // Held commits: the closure of haves, cut at the client's shallow
  // boundaries (their parents are NOT held — the client never received them).
  const held = new Set();
  {
    const stack = [...haves];
    while (stack.length > 0) {
      const oid = stack.pop();
      if (held.has(oid)) continue;
      const obj = getObject(repo, oid);
      if (!obj || obj.type !== 'commit') continue;
      held.add(oid);
      if (shallowSet.has(oid)) continue;
      for (const parent of parseCommit(obj.data).parents) stack.push(parent);
    }
  }
  // BFS from the wants.
  const sendCommits = new Set();
  const sendTags = new Set();
  const newShallow = new Set();
  const deepened = new Set(); // request-shallow boundaries we traversed past
  const visited = new Set();
  const queue = wants.map((oid) => ({ oid, depth: 0 }));
  while (queue.length > 0) {
    const { oid, depth } = queue.shift();
    if (visited.has(oid)) continue;
    visited.add(oid);
    const obj = getObject(repo, oid);
    if (!obj) continue;
    if (obj.type === 'tag') {
      if (!held.has(oid)) sendTags.add(oid);
      queue.push({ oid: parseTag(obj.data).object, depth });
      continue;
    }
    if (obj.type !== 'commit') {
      if (!held.has(oid)) sendCommits.add(oid);
      continue;
    }
    const isHeld = held.has(oid);
    const isDepthBoundary = deepen != null && depth >= deepen - 1;
    if (isDepthBoundary) {
      // At the depth limit: send it (if new), mark it shallow, never descend.
      if (!isHeld) {
        sendCommits.add(oid);
        newShallow.add(oid);
      }
      continue;
    }
    if (isHeld) {
      if (shallowSet.has(oid)) {
        // Held, but a shallow boundary: descend to its parents (the client
        // lacks them) without sending the commit itself.
        deepened.add(oid);
        for (const parent of parseCommit(obj.data).parents) {
          queue.push({ oid: parent, depth: depth + 1 });
        }
      }
      // Otherwise held and complete: skip it and everything below it.
      continue;
    }
    sendCommits.add(oid);
    for (const parent of parseCommit(obj.data).parents) {
      queue.push({ oid: parent, depth: depth + 1 });
    }
  }
  // `unshallow`: a boundary is only really deepened when a parent was sent.
  const unshallow = new Set();
  for (const oid of deepened) {
    const obj = getObject(repo, oid);
    if (!obj || obj.type !== 'commit') continue;
    if (parseCommit(obj.data).parents.some((p) => sendCommits.has(p))) unshallow.add(oid);
  }
  // Trees and blobs reachable from the sent commits, minus those reachable
  // from held commits (the client already has them).
  const heldBlobs = new Set();
  {
    const seenTrees = new Set();
    const walkTree = (treeOid) => {
      if (seenTrees.has(treeOid)) return;
      seenTrees.add(treeOid);
      const obj = getObject(repo, treeOid);
      if (!obj || obj.type !== 'tree') return;
      for (const entry of parseTree(obj.data)) {
        if (isDirMode(entry.mode)) walkTree(entry.oid);
        else heldBlobs.add(entry.oid);
      }
      heldBlobs.add(treeOid);
    };
    for (const oid of held) {
      const obj = getObject(repo, oid);
      if (obj && obj.type === 'commit') walkTree(parseCommit(obj.data).tree);
    }
  }
  const objects = new Map();
  const addObject = (oid) => {
    if (objects.has(oid)) return;
    const obj = getObject(repo, oid);
    if (obj) objects.set(oid, obj);
  };
  const walkSendTree = (treeOid) => {
    if (heldBlobs.has(treeOid)) return;
    addObject(treeOid);
    const obj = getObject(repo, treeOid);
    if (!obj || obj.type !== 'tree') return;
    for (const entry of parseTree(obj.data)) {
      if (isDirMode(entry.mode)) walkSendTree(entry.oid);
      else if (!heldBlobs.has(entry.oid)) addObject(entry.oid);
    }
  };
  for (const oid of sendTags) addObject(oid);
  for (const oid of sendCommits) {
    addObject(oid);
    const obj = getObject(repo, oid);
    if (obj && obj.type === 'commit') walkSendTree(parseCommit(obj.data).tree);
    else if (obj && obj.type === 'tag') {
      // A tag wanted directly: its target is handled by the BFS, but a
      // non-commit want needs no tree walk.
    }
  }
  // Acks: haves that are in the repo and are an ancestor of (or equal to) a want.
  const acks = [];
  const wantReachable = reachableCommits(repo, wants);
  for (const have of haves) {
    if (wantReachable.has(have)) acks.push(have);
  }
  return { objects, shallow: [...newShallow], unshallow: [...unshallow], acks };
}

// ---------------------------------------------------------------------------
// git smart HTTP

const UPLOAD_CAPS_V2 = ['version 2', 'ls-refs=unborn', 'fetch=shallow wait-for-done', 'server-option', 'object-format=sha1', `agent=${AGENT}`];
const UPLOAD_CAPS_V0 = ['symref=HEAD:refs/heads/main', 'side-band-64k', 'thin-pack', 'ofs-delta', 'multi_ack_detailed', 'shallow', `agent=${AGENT}`];
const RECEIVE_CAPS = ['report-status', 'side-band-64k', 'delete-refs', 'ofs-delta', `agent=${AGENT}`];

/** Ref lines for a v0 advertisement: HEAD first (carrying the capabilities), then branches and tags. */
function v0RefLines(repo, capabilities) {
  const lines = [];
  const caps = capabilities.join(' ');
  const tip = headTip(repo);
  const refs = sortedRefs(repo);
  const tagPeeled = new Map(); // tag ref -> peeled commit oid (annotated tags)
  for (const ref of refs) {
    if (!ref.name.startsWith('refs/tags/')) continue;
    const obj = getObject(repo, ref.oid);
    if (obj && obj.type === 'tag') tagPeeled.set(ref.name, parseTag(obj.data).object);
  }
  if (refs.length === 0) {
    lines.push(`${ZERO_OID} capabilities^{}\0${caps}\n`);
    return lines;
  }
  let first = true;
  const emit = (oid, name) => {
    if (first) {
      lines.push(`${oid} ${name}\0${caps}\n`);
      first = false;
    } else {
      lines.push(`${oid} ${name}\n`);
    }
  };
  if (tip) emit(tip, 'HEAD');
  for (const ref of refs) {
    emit(ref.oid, ref.name);
    if (tagPeeled.has(ref.name)) emit(tagPeeled.get(ref.name), `${ref.name}^{}`);
  }
  return lines;
}

/** The info/refs advertisement for a repo and service. Returns { status, contentType, body }. */
function gitAdvertisement(repo, service, gitProtocol) {
  if (service === 'git-upload-pack' && gitProtocol === 2) {
    const body = encodePktLines([...UPLOAD_CAPS_V2, 'flush']);
    return { status: 200, contentType: 'application/x-git-upload-pack-advertisement', body };
  }
  const serviceName = service === 'git-upload-pack' ? 'git-upload-pack' : 'git-receive-pack';
  const caps = service === 'git-upload-pack' ? UPLOAD_CAPS_V0 : RECEIVE_CAPS;
  const lines = [`# service=${serviceName}\n`, 'flush', ...v0RefLines(repo, caps)];
  const body = encodePktLines(lines);
  return { status: 200, contentType: `application/x-${serviceName}-advertisement`, body };
}

/** Parse a v2 command request body into { command, args, rest } (rest = bytes after the first flush). */
function parseV2Command(body) {
  const { packets, rest } = decodePktLines(body, true);
  let command = null;
  const args = [];
  let seenDelim = false;
  for (const packet of packets) {
    if (packet.kind === 'flush') break;
    if (packet.kind === 'delim') {
      seenDelim = true;
      continue;
    }
    if (packet.kind !== 'data') continue;
    const line = packet.payload.toString('utf8');
    if (!seenDelim && line.startsWith('command=')) {
      command = line.slice('command='.length).replace(/\n$/, '');
    } else if (seenDelim) {
      args.push(line.replace(/\n$/, ''));
    }
    // Lines before the delim that are not `command=` are ignored (agent=, object-format=).
  }
  return { command, args, rest };
}

/** v2 ls-refs response lines for a repo, honouring ref-prefix filters. */
function lsRefsLines(repo, args) {
  const prefixes = args.filter((a) => a.startsWith('ref-prefix ')).map((a) => a.slice('ref-prefix '.length));
  const wantPeel = args.includes('peel');
  const wantSymrefs = args.includes('symrefs');
  const wantUnborn = args.includes('unborn');
  const lines = [];
  const tip = headTip(repo);
  const refs = sortedRefs(repo);
  const tagPeeled = new Map();
  for (const ref of refs) {
    if (!ref.name.startsWith('refs/tags/')) continue;
    const obj = getObject(repo, ref.oid);
    if (obj && obj.type === 'tag') tagPeeled.set(ref.name, parseTag(obj.data).object);
  }
  const keep = (name) => prefixes.length === 0 || prefixes.some((p) => name.startsWith(p));
  if (keep('HEAD')) {
    if (tip) {
      let line = `${tip} HEAD`;
      if (wantSymrefs) line += ` symref-target:refs/heads/${repo.defaultBranch}`;
      lines.push(`${line}\n`);
    } else if (wantUnborn) {
      let line = `unborn HEAD`;
      if (wantSymrefs) line += ` symref-target:refs/heads/${repo.defaultBranch}`;
      lines.push(`${line}\n`);
    }
  }
  for (const ref of refs) {
    if (!keep(ref.name)) continue;
    let line = `${ref.oid} ${ref.name}`;
    if (wantPeel && tagPeeled.has(ref.name)) line += ` peeled:${tagPeeled.get(ref.name)}`;
    lines.push(`${line}\n`);
  }
  // An empty repository reports no refs/ entry at all: an `unborn
  // refs/heads/<branch>` line would read as an existing branch at the zero
  // oid, and both a fresh clone and a fixture that lists the branch first
  // treat that as a branch that exists. The unborn HEAD line above already
  // carries the default branch's symref target.
  return lines;
}

/** The wanted-refs lines for a fetch: one "<oid> <ref>" per want that is a ref tip. */
function wantedRefsLines(repo, wants) {
  const lines = [];
  for (const want of wants) {
    for (const ref of sortedRefs(repo)) {
      if (ref.oid === want) lines.push(`${want} ${ref.name}\n`);
    }
    if (want === headTip(repo)) lines.push(`${want} HEAD\n`);
  }
  return lines;
}

/** Handle POST /<owner>/<repo>/git-upload-pack (v2 fetch or ls-refs, v0 fetch). */
function handleUploadPack(repo, body, gitProtocol) {
  // v2 commands arrive with a `command=` line; v0 arrives as want/have lines.
  const firstLine = (() => {
    const { packets } = decodePktLines(body, true);
    for (const packet of packets) {
      if (packet.kind === 'data') return packet.payload.toString('utf8');
    }
    return '';
  })();
  if (firstLine.startsWith('command=')) {
    const { command, args } = parseV2Command(body);
    if (command === 'ls-refs') {
      const lines = lsRefsLines(repo, args);
      return { status: 200, contentType: 'application/x-git-upload-pack-result', body: encodePktLines([...lines, 'flush']) };
    }
    if (command === 'fetch') {
      const wants = [];
      const haves = [];
      const shallowReq = [];
      let deepen = null;
      for (const arg of args) {
        if (arg.startsWith('want ')) wants.push(arg.slice(5).trim());
        else if (arg.startsWith('have ')) haves.push(arg.slice(5).trim());
        else if (arg.startsWith('shallow ')) shallowReq.push(arg.slice(8).trim());
        else if (arg.startsWith('deepen ')) {
          const n = parseInt(arg.slice(7).trim(), 10);
          if (Number.isFinite(n) && n > 0) deepen = n;
        }
      }
      const selected = selectFetch(repo, { wants, haves, shallowReq, deepen });
      const parts = [];
      parts.push(pktLine('acknowledgments\n'));
      if (selected.acks.length > 0) {
        for (const ack of selected.acks) parts.push(pktLine(`ACK ${ack}\n`));
      } else {
        parts.push(pktLine('NAK\n'));
      }
      parts.push(pktLine('ready\n'));
      parts.push(PKT_DELIM);
      if (selected.shallow.length > 0 || selected.unshallow.length > 0) {
        parts.push(pktLine('shallow-info\n'));
        for (const oid of selected.shallow) parts.push(pktLine(`shallow ${oid}\n`));
        for (const oid of selected.unshallow) parts.push(pktLine(`unshallow ${oid}\n`));
        parts.push(PKT_DELIM);
      }
      const wanted = wantedRefsLines(repo, wants);
      if (wanted.length > 0) {
        parts.push(pktLine('wanted-refs\n'));
        for (const line of wanted) parts.push(pktLine(line));
        parts.push(PKT_DELIM);
      }
      if (selected.objects.size > 0) {
        parts.push(pktLine('packfile\n'));
        const pack = writePack([...selected.objects.values()]);
        for (const packet of sidebandPackets(1, pack)) parts.push(packet);
      }
      parts.push(PKT_FLUSH);
      return { status: 200, contentType: 'application/x-git-upload-pack-result', body: Buffer.concat(parts) };
    }
    return { status: 400, contentType: 'application/json', body: Buffer.from(JSON.stringify({ message: `unknown command ${command}` }), 'utf8') };
  }
  // v0 fetch: want/have/shallow/deepen lines, a flush, then haves and done, a flush.
  const { packets } = decodePktLines(body, false);
  const wants = [];
  const haves = [];
  const shallowReq = [];
  let deepen = null;
  for (const packet of packets) {
    if (packet.kind !== 'data') continue;
    const line = packet.payload.toString('utf8').replace(/\n$/, '');
    if (line.startsWith('want ')) wants.push(line.slice(5).split(' ')[0]);
    else if (line.startsWith('have ')) haves.push(line.slice(5).trim());
    else if (line.startsWith('shallow ')) shallowReq.push(line.slice(8).trim());
    else if (line.startsWith('deepen ')) {
      const n = parseInt(line.slice(7).trim(), 10);
      if (Number.isFinite(n) && n > 0) deepen = n;
    }
  }
  const selected = selectFetch(repo, { wants, haves, shallowReq, deepen });
  const parts = [];
  if (selected.acks.length > 0) {
    for (const ack of selected.acks) parts.push(pktLine(`ACK ${ack}\n`));
  } else {
    parts.push(pktLine('NAK\n'));
  }
  for (const oid of selected.shallow) parts.push(pktLine(`shallow ${oid}\n`));
  for (const oid of selected.unshallow) parts.push(pktLine(`unshallow ${oid}\n`));
  if (selected.objects.size > 0) {
    const pack = writePack([...selected.objects.values()]);
    for (const packet of sidebandPackets(1, pack)) parts.push(packet);
  }
  parts.push(PKT_FLUSH);
  return { status: 200, contentType: 'application/x-git-upload-pack-result', body: Buffer.concat(parts) };
}

/**
 * Handle POST /<owner>/<repo>/git-receive-pack (v0 push).
 * Returns { status, contentType, body } with a sideband-framed report.
 */
async function handleReceivePack(repo, body) {
  const { packets, rest } = decodePktLines(body, true);
  const commands = [];
  for (const packet of packets) {
    if (packet.kind !== 'data') continue;
    const line = packet.payload.toString('utf8').replace(/\n$/, '');
    const nul = line.indexOf('\0');
    const text = nul === -1 ? line : line.slice(0, nul);
    const parts = text.split(' ');
    if (parts.length < 3) continue;
    commands.push({ oldOid: parts[0], newOid: parts[1], ref: parts[2] });
  }
  const reportLines = [];
  let unpackOk = true;
  let unpackDetail = 'ok';
  const hasUpdates = commands.some((c) => c.newOid !== ZERO_OID);
  if (hasUpdates && rest.length > 0) {
    try {
      const { objects } = await readPack(rest, (oid) => getObject(repo, oid));
      for (const [oid, obj] of objects) {
        if (!repo.objects.has(oid)) repo.objects.set(oid, obj);
      }
    } catch (err) {
      unpackOk = false;
      unpackDetail = err instanceof Error ? err.message : 'unpacker error';
    }
  } else if (hasUpdates && rest.length === 0) {
    unpackOk = false;
    unpackDetail = 'unpacker error';
  }
  if (!unpackOk) {
    for (const command of commands) {
      reportLines.push({ ref: command.ref, ok: false, reason: 'unpacker error' });
    }
  } else {
    for (const command of commands) {
      if (command.newOid === ZERO_OID) {
        // Delete.
        if (!repo.refs.has(command.ref)) {
          reportLines.push({ ref: command.ref, ok: false, reason: 'remote ref does not exist' });
        } else {
          repo.refs.delete(command.ref);
          reportLines.push({ ref: command.ref, ok: true, reason: '' });
        }
        continue;
      }
      const current = repo.refs.get(command.ref) ?? null;
      if (command.oldOid === ZERO_OID) {
        // Create.
        if (current !== null) {
          reportLines.push({ ref: command.ref, ok: false, reason: 'already exists' });
          continue;
        }
      } else if (current !== command.oldOid) {
        reportLines.push({ ref: command.ref, ok: false, reason: 'remote ref does not match' });
        continue;
      } else if (!isAncestor(repo, command.oldOid, command.newOid)) {
        reportLines.push({ ref: command.ref, ok: false, reason: 'non-fast-forward' });
        continue;
      }
      const target = getObject(repo, command.newOid);
      if (!target) {
        reportLines.push({ ref: command.ref, ok: false, reason: 'object not found' });
        continue;
      }
      repo.refs.set(command.ref, command.newOid);
      reportLines.push({ ref: command.ref, ok: true, reason: '' });
    }
  }
  const lines = [`unpack ${unpackDetail}\n`];
  for (const entry of reportLines) {
    lines.push(entry.ok ? `ok ${entry.ref}\n` : `ng ${entry.ref} ${entry.reason}\n`);
  }
  const reportStream = encodePktLines(lines);
  const parts = [];
  for (const packet of sidebandPackets(1, reportStream)) parts.push(packet);
  parts.push(PKT_FLUSH);
  return { status: 200, contentType: 'application/x-git-receive-pack-result', body: Buffer.concat(parts) };
}

// ---------------------------------------------------------------------------
// REST v3

const FIXED_ISO = new Date(FIXED_EPOCH * 1000).toISOString();

function jsonBody(status, obj, extraHeaders) {
  const body = Buffer.from(JSON.stringify(obj), 'utf8');
  return { status, contentType: 'application/json', headers: extraHeaders ?? {}, body };
}

function errorBody(status, message) {
  return jsonBody(status, { message });
}

function repoJson(repo) {
  return {
    id: repo.id,
    name: repo.name,
    full_name: `${repo.owner}/${repo.name}`,
    owner: { login: repo.owner, id: repo.owner === VIEWER_LOGIN ? VIEWER_ID : 1001, type: 'User' },
    private: repo.private,
    description: repo.description,
    default_branch: repo.defaultBranch,
    html_url: `https://github.example/${repo.owner}/${repo.name}`,
    url: `/api/v3/repos/${repo.owner}/${repo.name}`,
    clone_url: `https://github.example/${repo.owner}/${repo.name}.git`,
    git_url: `git://github.example/${repo.owner}/${repo.name}.git`,
    ssh_url: `git@github.example:${repo.owner}/${repo.name}.git`,
    created_at: FIXED_ISO,
    updated_at: FIXED_ISO,
    pushed_at: FIXED_ISO,
    has_issues: true,
    has_projects: true,
    has_wiki: true,
    fork: false,
    archived: false,
    disabled: false,
    visibility: repo.private ? 'private' : 'public',
    open_issues_count: repo.issues.filter((i) => i.state === 'open').length,
  };
}

function labelJson(label) {
  return { id: label.id, name: label.name, color: label.color, description: label.description ?? '', default: false };
}

function userJson(login) {
  return { login, id: login === VIEWER_LOGIN ? VIEWER_ID : 1001, type: 'User', avatar_url: '', html_url: `https://github.example/${login}` };
}

function issueJson(repo, issue) {
  return {
    id: issue.id,
    number: issue.number,
    title: issue.title,
    body: issue.body ?? '',
    state: issue.state,
    labels: issue.labels.map((l) => labelJson(l)),
    user: userJson(VIEWER_LOGIN),
    assignees: [],
    created_at: FIXED_ISO,
    updated_at: FIXED_ISO,
    closed_at: issue.state === 'closed' ? FIXED_ISO : null,
    html_url: `https://github.example/${repo.owner}/${repo.name}/issues/${issue.number}`,
    url: `/api/v3/repos/${repo.owner}/${repo.name}/issues/${issue.number}`,
    comments: (repo.comments.get(issue.number) ?? []).length,
    comments_url: `/api/v3/repos/${repo.owner}/${repo.name}/issues/${issue.number}/comments`,
  };
}

function pullJson(repo, pr) {
  const headSha = refTip(repo, `refs/heads/${pr.head.ref}`) ?? pr.head.sha ?? ZERO_OID;
  const baseSha = refTip(repo, `refs/heads/${pr.base.ref}`) ?? pr.base.sha ?? ZERO_OID;
  return {
    id: pr.id,
    number: pr.number,
    title: pr.title,
    body: pr.body ?? '',
    state: pr.state,
    head: { ref: pr.head.ref, sha: headSha, label: `${repo.owner}:${pr.head.ref}`, user: userJson(VIEWER_LOGIN), repo: repoJson(repo) },
    base: { ref: pr.base.ref, sha: baseSha, label: `${repo.owner}:${pr.base.ref}`, user: userJson(VIEWER_LOGIN), repo: repoJson(repo) },
    merged: pr.merged,
    merged_at: pr.merged_at,
    merge_commit_sha: pr.merge_commit_sha,
    mergeable: prMergeable(repo, pr),
    mergeable_state: prMergeable(repo, pr).toLowerCase(),
    user: userJson(VIEWER_LOGIN),
    created_at: FIXED_ISO,
    updated_at: FIXED_ISO,
    closed_at: pr.state === 'closed' ? FIXED_ISO : null,
    html_url: `https://github.example/${repo.owner}/${repo.name}/pull/${pr.number}`,
    url: `/api/v3/repos/${repo.owner}/${repo.name}/pulls/${pr.number}`,
  };
}

function commentJson(repo, issueNumber, comment) {
  return {
    id: comment.id,
    body: comment.body,
    user: userJson(VIEWER_LOGIN),
    created_at: FIXED_ISO,
    updated_at: FIXED_ISO,
    html_url: `https://github.example/${repo.owner}/${repo.name}/issues/${issueNumber}#issuecomment-${comment.id}`,
    url: `/api/v3/repos/${repo.owner}/${repo.name}/issues/${issueNumber}/comments/${comment.id}`,
  };
}

function commitTreeOid(repo, commitOid) {
  const obj = getObject(repo, commitOid);
  if (!obj || obj.type !== 'commit') return null;
  return parseCommit(obj.data).tree;
}

/** The merge-base of two commits: the first common ancestor (BFS from both sides). */
function findMergeBase(repo, a, b) {
  if (!a || !b) return null;
  if (a === b) return a;
  const ancestorsA = reachableCommits(repo, [a]);
  const queue = [b];
  const seen = new Set();
  while (queue.length > 0) {
    const oid = queue.shift();
    if (ancestorsA.has(oid)) return oid;
    if (seen.has(oid)) continue;
    seen.add(oid);
    const obj = getObject(repo, oid);
    if (!obj || obj.type !== 'commit') continue;
    for (const parent of parseCommit(obj.data).parents) queue.push(parent);
  }
  return null;
}

/**
 * The file diff of a pull request: files changed from the merge-base tree to
 * the head tree, plus whether the head conflicts with the current base tip.
 * Returns { changed: Map<path, {status, oid}>, conflict, mergeBase, baseTip, headTip }.
 */
function prDiff(repo, pr) {
  const baseTip = refTip(repo, `refs/heads/${pr.base.ref}`);
  const headTipOid = refTip(repo, `refs/heads/${pr.head.ref}`);
  const mergeBase = findMergeBase(repo, headTipOid, baseTip);
  const baseFiles = mergeBase ? flattenTree(repo, commitTreeOid(repo, mergeBase)) : new Map();
  const headFiles = headTipOid ? flattenTree(repo, commitTreeOid(repo, headTipOid)) : new Map();
  const currentFiles = baseTip ? flattenTree(repo, commitTreeOid(repo, baseTip)) : new Map();
  const changed = new Map();
  for (const [path, entry] of headFiles) {
    const baseEntry = baseFiles.get(path);
    if (!baseEntry) changed.set(path, { status: 'added', oid: entry.oid });
    else if (baseEntry.oid !== entry.oid) changed.set(path, { status: 'modified', oid: entry.oid });
  }
  for (const [path] of baseFiles) {
    if (!headFiles.has(path)) changed.set(path, { status: 'removed', oid: null });
  }
  let conflict = false;
  for (const [path, change] of changed) {
    const baseEntry = baseFiles.get(path);
    const currentEntry = currentFiles.get(path);
    const headEntry = headFiles.get(path);
    const currentChanged = currentEntry === undefined ? baseEntry !== undefined : !baseEntry || baseEntry.oid !== currentEntry.oid;
    if (currentChanged) {
      const currentOid = currentEntry ? currentEntry.oid : null;
      const headOid = headEntry ? headEntry.oid : null;
      if (currentOid !== headOid) conflict = true;
    }
  }
  return { changed, conflict, mergeBase, baseTip, headTip: headTipOid };
}

function prMergeable(repo, pr) {
  if (pr.state !== 'open') return 'UNKNOWN';
  if (!refTip(repo, `refs/heads/${pr.head.ref}`) || !refTip(repo, `refs/heads/${pr.base.ref}`)) return 'UNKNOWN';
  return prDiff(repo, pr).conflict ? 'CONFLICTING' : 'MERGEABLE';
}

/** A simple line multiset diff: { additions, deletions } between two texts. */
function lineDiff(oldText, newText) {
  const countLines = (text) => {
    if (text === '') return new Map();
    const map = new Map();
    for (const line of text.split('\n')) map.set(line, (map.get(line) ?? 0) + 1);
    return map;
  };
  const oldLines = countLines(oldText ?? '');
  const newLines = countLines(newText ?? '');
  let additions = 0;
  let deletions = 0;
  for (const [line, count] of newLines) additions += Math.max(0, count - (oldLines.get(line) ?? 0));
  for (const [line, count] of oldLines) deletions += Math.max(0, count - (newLines.get(line) ?? 0));
  return { additions, deletions };
}

/** Paginate an array by ?page=&per_page=, returning { page, headers } with a Link header. */
function paginate(items, query, req, path) {
  const perPage = clampInt(parseInt(query.per_page ?? '30', 10), 1, 100, 30);
  const page = clampInt(parseInt(query.page ?? '1', 10), 1, 1000000, 1);
  const total = items.length;
  const pages = Math.max(1, Math.ceil(total / perPage));
  const start = (page - 1) * perPage;
  const slice = items.slice(start, start + perPage);
  const host = req.headers.host ?? '127.0.0.1';
  const base = `http://${host}${path}`;
  const linkFor = (p, rel) => `<${base}?per_page=${perPage}&page=${p}>; rel="${rel}"`;
  const links = [];
  if (page < pages) links.push(linkFor(page + 1, 'next'));
  if (page > 1) links.push(linkFor(page - 1, 'prev'));
  links.push(linkFor(1, 'first'));
  links.push(linkFor(pages, 'last'));
  return { page: slice, headers: { link: links.join(', ') } };
}

// ---------------------------------------------------------------------------
// REST routing

/**
 * Dispatch a REST request. `segments` are the decoded path parts after
 * /api/v3, `query` the parsed query, `body` the parsed JSON body (or null).
 * Returns { status, contentType, headers, body }.
 */
function handleRest(req, segments, query, body) {
  const method = req.method;
  const seg = segments;

  // GET /api/v3/ — the API root.
  if (seg.length === 0) {
    if (method !== 'GET') return errorBody(404, 'Not Found');
    return jsonBody(200, { current_user_url: '/api/v3/user', repository_url: '/api/v3/repos/{owner}/{repo}' }, { 'x-oauth-scopes': 'repo, read:org' });
  }

  // GET /api/v3/meta
  if (seg.length === 1 && seg[0] === 'meta') {
    if (method !== 'GET') return errorBody(404, 'Not Found');
    return jsonBody(200, { installed_version: SERVER_VERSION, verifiable_password_authentication: true });
  }

  // GET /api/v3/user
  if (seg.length === 1 && seg[0] === 'user') {
    if (method !== 'GET') return errorBody(404, 'Not Found');
    return jsonBody(200, { login: VIEWER_LOGIN, id: VIEWER_ID, name: VIEWER_NAME, email: VIEWER_EMAIL, type: 'User' });
  }

  // POST /api/v3/user/repos  |  GET /api/v3/user/repos
  if (seg.length === 2 && seg[0] === 'user' && seg[1] === 'repos') {
    if (method === 'POST') {
      const name = typeof body?.name === 'string' ? body.name.trim() : '';
      if (name === '' || /[\s/]/.test(name) || name.length > 100) return errorBody(422, 'Invalid repository name');
      if (findRepo(VIEWER_LOGIN, name)) return errorBody(422, 'Repository already exists');
      const repo = createRepoRecord({ name, owner: VIEWER_LOGIN, description: typeof body?.description === 'string' ? body.description : '', isPrivate: body?.private === true });
      return jsonBody(201, repoJson(repo));
    }
    if (method === 'GET') {
      const repos = listReposFor(VIEWER_LOGIN);
      const { page, headers } = paginate(repos, query, req, '/api/v3/user/repos');
      return jsonBody(200, page.map((r) => repoJson(r)), headers);
    }
    return errorBody(404, 'Not Found');
  }

  // /api/v3/repos/{owner}/{repo}/...
  if (seg.length >= 3 && seg[0] === 'repos') {
    const owner = seg[1];
    const repoName = seg[2];
    const repo = findRepo(owner, repoName);
    const rest = seg.slice(3);
    if (!repo) {
      // A repo under another login is a 404, never a 403.
      return errorBody(404, 'Not Found');
    }
    if (owner.toLowerCase() !== VIEWER_LOGIN.toLowerCase()) return errorBody(404, 'Not Found');

    // GET / PATCH / DELETE /api/v3/repos/{o}/{r}
    if (rest.length === 0) {
      if (method === 'GET') return jsonBody(200, repoJson(repo));
      if (method === 'PATCH') {
        if (typeof body?.description === 'string') repo.description = body.description;
        if (typeof body?.private === 'boolean') repo.private = body.private;
        if (typeof body?.default_branch === 'string' && body.default_branch !== '') repo.defaultBranch = body.default_branch;
        return jsonBody(200, repoJson(repo));
      }
      if (method === 'DELETE') {
        deleteRepo(owner, repoName);
        return { status: 204, contentType: 'application/json', headers: {}, body: Buffer.alloc(0) };
      }
      return errorBody(404, 'Not Found');
    }

    // GET /api/v3/repos/{o}/{r}/branches  |  /branches/{branch}
    if (rest[0] === 'branches') {
      if (rest.length === 1 && method === 'GET') {
        const branches = sortedRefs(repo)
          .filter((r) => r.name.startsWith('refs/heads/'))
          .map((r) => ({ name: r.name.slice('refs/heads/'.length), commit: { sha: r.oid, url: `/api/v3/repos/${owner}/${repoName}/commits/${r.oid}` }, protected: false }));
        return jsonBody(200, branches);
      }
      if (rest.length === 2 && method === 'GET') {
        const branch = rest[1];
        const tip = refTip(repo, `refs/heads/${branch}`);
        if (!tip) return errorBody(404, 'Not Found');
        return jsonBody(200, { name: branch, commit: { sha: tip, url: `/api/v3/repos/${owner}/${repoName}/commits/${tip}` }, protected: false });
      }
      return errorBody(404, 'Not Found');
    }

    // GET /api/v3/repos/{o}/{r}/commits[?sha=]
    if (rest[0] === 'commits') {
      if (method !== 'GET') return errorBody(404, 'Not Found');
      let tip = null;
      if (typeof query.sha === 'string' && query.sha !== '') {
        tip = refTip(repo, `refs/heads/${query.sha}`) ?? (isOid(query.sha) ? query.sha : null);
      } else {
        tip = headTip(repo);
      }
      const commits = [];
      if (tip) {
        const seen = new Set();
        const stack = [tip];
        while (stack.length > 0) {
          const oid = stack.pop();
          if (seen.has(oid)) continue;
          seen.add(oid);
          const obj = getObject(repo, oid);
          if (!obj || obj.type !== 'commit') continue;
          const parsed = parseCommit(obj.data);
          commits.push({
            sha: oid,
            commit: {
              message: parsed.message,
              author: { name: 'Conformance', email: 'conformance@make.fun', date: FIXED_ISO },
              committer: { name: 'Conformance', email: 'conformance@make.fun', date: FIXED_ISO },
              tree: { sha: parsed.tree },
            },
            author: userJson(VIEWER_LOGIN),
            committer: userJson(VIEWER_LOGIN),
            parents: parsed.parents.map((p) => ({ sha: p })),
          });
          for (const parent of parsed.parents) stack.push(parent);
        }
      }
      return jsonBody(200, commits);
    }

    // POST /api/v3/repos/{o}/{r}/git/refs  |  GET .../git/refs[/heads/{branch}]
    if (rest[0] === 'git' && rest[1] === 'refs') {
      if (method === 'POST' && rest.length === 2) {
        const ref = typeof body?.ref === 'string' ? body.ref : '';
        const sha = typeof body?.sha === 'string' ? body.sha : '';
        if (!ref.startsWith('refs/') || !isOid(sha)) return errorBody(422, 'Invalid ref or sha');
        if (!getObject(repo, sha)) return errorBody(422, 'Object does not exist');
        if (repo.refs.has(ref)) return errorBody(422, 'Reference already exists');
        repo.refs.set(ref, sha);
        return jsonBody(201, { ref, object: { sha, type: (getObject(repo, sha) ?? {}).type ?? 'commit', url: `/api/v3/repos/${owner}/${repoName}/git/${(getObject(repo, sha) ?? {}).type ?? 'commits'}/${sha}` } });
      }
      if (method === 'GET' && rest.length >= 3) {
        const refName = `refs/${rest.slice(2).join('/')}`;
        const tip = refTip(repo, refName);
        if (!tip) return errorBody(404, 'Not Found');
        return jsonBody(200, { ref: refName, object: { sha: tip, type: (getObject(repo, tip) ?? {}).type ?? 'commit' } });
      }
      if (method === 'GET' && rest.length === 2) {
        const refs = sortedRefs(repo).map((r) => ({ ref: r.name, object: { sha: r.oid } }));
        return jsonBody(200, refs);
      }
      return errorBody(404, 'Not Found');
    }

    // PUT / GET / DELETE /api/v3/repos/{o}/{r}/contents/{path...}
    if (rest[0] === 'contents') {
      const path = rest.slice(1).join('/');
      if (path === '') return errorBody(404, 'Not Found');
      if (method === 'PUT') {
        const branch = typeof body?.branch === 'string' && body.branch !== '' ? body.branch : repo.defaultBranch;
        const message = typeof body?.message === 'string' ? body.message : 'Update file';
        const contentB64 = typeof body?.content === 'string' ? body.content : '';
        let content;
        try {
          content = b64decode(contentB64);
        } catch {
          return errorBody(400, 'Invalid base64 content');
        }
        const branchTip = refTip(repo, `refs/heads/${branch}`);
        if (typeof body?.sha === 'string' && body.sha !== '') {
          // An update: the given sha must be the file's current blob.
          const current = branchTip ? readFileFromTree(repo, commitTreeOid(repo, branchTip), path) : null;
          const currentSha = current ? hashObject('blob', current) : null;
          if (currentSha !== body.sha) return errorBody(409, 'sha does not match the current file');
          const { commitOid, blobOid } = commitFile(repo, { branch, path, content, message });
          return jsonBody(200, { content: { name: path.split('/').pop(), path, sha: blobOid, size: content.length, encoding: 'base64', type: 'file' }, commit: { sha: commitOid, message } });
        }
        const { commitOid, blobOid } = commitFile(repo, { branch, path, content, message });
        return jsonBody(201, { content: { name: path.split('/').pop(), path, sha: blobOid, size: content.length, encoding: 'base64', type: 'file' }, commit: { sha: commitOid, message } });
      }
      if (method === 'GET') {
        let tip = null;
        if (typeof query.ref === 'string' && query.ref !== '') {
          tip = refTip(repo, `refs/heads/${query.ref}`) ?? (isOid(query.ref) ? query.ref : null);
        } else {
          tip = headTip(repo);
        }
        if (!tip) return errorBody(404, 'Not Found');
        const treeOid = commitTreeOid(repo, tip);
        if (!treeOid) return errorBody(404, 'Not Found');
        const files = flattenTree(repo, treeOid);
        const entry = files.get(path);
        if (entry) {
          const blob = getObject(repo, entry.oid);
          const data = blob && blob.type === 'blob' ? blob.data : Buffer.alloc(0);
          return jsonBody(200, { type: 'file', encoding: 'base64', size: data.length, name: path.split('/').pop(), path, content: b64encode(data), sha: entry.oid });
        }
        // A directory listing: entries directly under `path`.
        const prefix = `${path}/`;
        const children = new Map();
        for (const [p, e] of files) {
          if (!p.startsWith(prefix)) continue;
          const rest2 = p.slice(prefix.length);
          const first = rest2.split('/')[0];
          if (rest2.includes('/')) {
            const dirOid = treeOidForPath(repo, treeOid, `${path}/${first}`) ?? '';
            children.set(first, { type: 'dir', name: first, path: `${path}/${first}`, sha: dirOid });
          } else {
            children.set(first, { type: 'file', name: first, path: p, sha: e.oid, size: (getObject(repo, e.oid)?.data.length ?? 0) });
          }
        }
        if (children.size === 0) return errorBody(404, 'Not Found');
        return jsonBody(200, [...children.values()]);
      }
      if (method === 'DELETE') {
        const branch = typeof body?.branch === 'string' && body.branch !== '' ? body.branch : repo.defaultBranch;
        const message = typeof body?.message === 'string' ? body.message : 'Delete file';
        const sha = typeof body?.sha === 'string' ? body.sha : '';
        const branchTip = refTip(repo, `refs/heads/${branch}`);
        if (!branchTip) return errorBody(404, 'Not Found');
        const current = readFileFromTree(repo, commitTreeOid(repo, branchTip), path);
        if (!current) return errorBody(404, 'Not Found');
        if (sha !== '' && hashObject('blob', current) !== sha) return errorBody(409, 'sha does not match the current file');
        const commitOid = deleteFile(repo, { branch, path, message });
        if (!commitOid) return errorBody(404, 'Not Found');
        return jsonBody(200, { commit: { sha: commitOid, message } });
      }
      return errorBody(404, 'Not Found');
    }

    // POST /api/v3/repos/{o}/{r}/labels
    if (rest[0] === 'labels') {
      if (method === 'POST' && rest.length === 1) {
        const name = typeof body?.name === 'string' ? body.name.trim() : '';
        if (name === '') return errorBody(422, 'Invalid label name');
        const color = typeof body?.color === 'string' ? body.color : 'ededed';
        const existing = repo.labels.get(name);
        if (existing) return jsonBody(201, labelJson(existing));
        const label = { id: store.nextIssueId + repo.labels.size, name, color, description: typeof body?.description === 'string' ? body.description : '' };
        repo.labels.set(name, label);
        return jsonBody(201, labelJson(label));
      }
      if (method === 'GET' && rest.length === 1) {
        return jsonBody(200, [...repo.labels.values()].map((l) => labelJson(l)));
      }
      return errorBody(404, 'Not Found');
    }

    // Issues and pull requests live below.
    const issueOrPull = handleIssuesAndPulls(req, repo, owner, repoName, rest, query, body);
    if (issueOrPull !== null) return issueOrPull;
    return errorBody(404, 'Not Found');
  }

  return errorBody(404, 'Not Found');
}

// ---------------------------------------------------------------------------
// issues and pull requests (REST)

function newIssueRecord(repo, { title, body, labels }) {
  const number = repo.nextNumber++;
  const issue = {
    id: store.nextIssueId++,
    number,
    title,
    body: body ?? '',
    state: 'open',
    labels: labels ?? [],
    seq: repo.issues.length + repo.pulls.length + 1,
    kind: 'issue',
  };
  repo.issues.push(issue);
  return issue;
}

function newPullRecord(repo, { title, body, head, base }) {
  const number = repo.nextNumber++;
  const pr = {
    id: store.nextIssueId++,
    number,
    title,
    body: body ?? '',
    state: 'open',
    labels: [],
    seq: repo.issues.length + repo.pulls.length + 1,
    kind: 'pull',
    head: { ref: head, sha: refTip(repo, `refs/heads/${head}`) ?? ZERO_OID },
    base: { ref: base, sha: refTip(repo, `refs/heads/${base}`) ?? ZERO_OID },
    merged: false,
    merged_at: null,
    merge_commit_sha: null,
  };
  repo.pulls.push(pr);
  return pr;
}

function resolveLabels(repo, rawLabels) {
  if (rawLabels === undefined || rawLabels === null) return { labels: [], unknown: null };
  const names = [];
  for (const entry of Array.isArray(rawLabels) ? rawLabels : [rawLabels]) {
    if (typeof entry === 'string') names.push(entry);
    else if (entry && typeof entry.name === 'string') names.push(entry.name);
  }
  const labels = [];
  for (const name of names) {
    const label = repo.labels.get(name);
    if (!label) return { labels: [], unknown: name };
    labels.push(label);
  }
  return { labels, unknown: null };
}

function refNameOf(value) {
  if (typeof value === 'string') return value;
  if (value && typeof value.ref === 'string') return value.ref;
  if (value && typeof value.branch === 'string') return value.branch;
  return null;
}

/** Squash-merge a pull request onto its base branch. Returns { ok, status, body }. */
function mergePullRequest(repo, pr, mergeMethod) {
  if (pr.state !== 'open') return { ok: false, status: 405, body: { message: 'Pull request is not open' } };
  const diff = prDiff(repo, pr);
  if (diff.conflict) return { ok: false, status: 405, body: { message: 'Merge conflict' } };
  if (!diff.baseTip || !diff.headTip) return { ok: false, status: 405, body: { message: 'Cannot merge: missing ref' } };
  // The merged tree: the base tip's files, with the head's changes applied.
  const files = new Map();
  for (const [path, entry] of flattenTree(repo, commitTreeOid(repo, diff.baseTip))) {
    files.set(path, entry.oid);
  }
  for (const [path, change] of diff.changed) {
    if (change.status === 'removed') files.delete(path);
    else files.set(path, change.oid);
  }
  const treeOid = buildTreeFromFiles(repo, files);
  const commitOid = putObject(repo, 'commit', buildCommitBytes({ tree: treeOid, parents: [diff.baseTip], message: pr.title }));
  repo.refs.set(`refs/heads/${pr.base.ref}`, commitOid);
  pr.merged = true;
  pr.state = 'closed';
  pr.merged_at = FIXED_ISO;
  pr.merge_commit_sha = commitOid;
  return { ok: true, status: 200, body: { sha: commitOid, merged: true, message: pr.title } };
}

function handleIssuesAndPulls(req, repo, owner, repoName, rest, query, body) {
  const method = req.method;
  // ---- labels are handled by the caller; issues start here ----
  if (rest[0] === 'issues') {
    // POST /issues  |  GET /issues
    if (rest.length === 1) {
      if (method === 'POST') {
        const title = typeof body?.title === 'string' ? body.title : '';
        if (title === '') return errorBody(422, 'title is required');
        const { labels, unknown } = resolveLabels(repo, body?.labels);
        if (unknown) return errorBody(422, `Label '${unknown}' does not exist`);
        const issue = newIssueRecord(repo, { title, body: typeof body?.body === 'string' ? body.body : '', labels });
        return jsonBody(201, issueJson(repo, issue));
      }
      if (method === 'GET') {
        let items = [...repo.issues];
        const state = typeof query.state === 'string' ? query.state : 'open';
        if (state !== 'all') items = items.filter((i) => i.state === state);
        const direction = query.direction === 'asc' ? 1 : -1;
        items.sort((a, b) => (a.seq - b.seq) * direction);
        const { page, headers } = paginate(items, query, req, `/api/v3/repos/${owner}/${repoName}/issues`);
        return jsonBody(200, page.map((i) => issueJson(repo, i)), headers);
      }
      return errorBody(404, 'Not Found');
    }
    // /issues/{n}
    const number = parseInt(rest[1], 10);
    if (!Number.isInteger(number)) return errorBody(404, 'Not Found');
    const issue = repo.issues.find((i) => i.number === number) ?? null;
    if (!issue) return errorBody(404, 'Not Found');
    // /issues/{n}/comments
    if (rest.length === 3 && rest[2] === 'comments') {
      if (method === 'POST') {
        const text = typeof body?.body === 'string' ? body.body : '';
        if (text === '') return errorBody(422, 'body is required');
        const comment = { id: store.nextCommentId++, body: text, seq: (repo.comments.get(number) ?? []).length + 1 };
        if (!repo.comments.has(number)) repo.comments.set(number, []);
        repo.comments.get(number).push(comment);
        return jsonBody(201, commentJson(repo, number, comment));
      }
      if (method === 'GET') {
        const comments = repo.comments.get(number) ?? [];
        return jsonBody(200, comments.map((c) => commentJson(repo, number, c)));
      }
      return errorBody(404, 'Not Found');
    }
    if (rest.length === 2) {
      if (method === 'GET') return jsonBody(200, issueJson(repo, issue));
      if (method === 'PATCH') {
        if (typeof body?.state === 'string' && (body.state === 'open' || body.state === 'closed')) issue.state = body.state;
        if (typeof body?.title === 'string') issue.title = body.title;
        if (typeof body?.body === 'string') issue.body = body.body;
        if (body?.labels !== undefined) {
          const { labels, unknown } = resolveLabels(repo, body.labels);
          if (unknown) return errorBody(422, `Label '${unknown}' does not exist`);
          issue.labels = labels;
        }
        return jsonBody(200, issueJson(repo, issue));
      }
      return errorBody(404, 'Not Found');
    }
    return errorBody(404, 'Not Found');
  }

  if (rest[0] === 'pulls') {
    // POST /pulls  |  GET /pulls
    if (rest.length === 1) {
      if (method === 'POST') {
        const title = typeof body?.title === 'string' ? body.title : '';
        const head = refNameOf(body?.head);
        const base = refNameOf(body?.base);
        if (title === '' || !head || !base) return errorBody(422, 'title, head and base are required');
        if (!refTip(repo, `refs/heads/${head}`)) return errorBody(422, `head branch '${head}' does not exist`);
        if (!refTip(repo, `refs/heads/${base}`)) return errorBody(422, `base branch '${base}' does not exist`);
        const pr = newPullRecord(repo, { title, body: typeof body?.body === 'string' ? body.body : '', head, base });
        return jsonBody(201, pullJson(repo, pr));
      }
      if (method === 'GET') {
        let items = [...repo.pulls];
        const state = typeof query.state === 'string' ? query.state : 'open';
        if (state !== 'all') items = items.filter((p) => p.state === state);
        const { page, headers } = paginate(items, query, req, `/api/v3/repos/${owner}/${repoName}/pulls`);
        return jsonBody(200, page.map((p) => pullJson(repo, p)), headers);
      }
      return errorBody(404, 'Not Found');
    }
    const number = parseInt(rest[1], 10);
    if (!Number.isInteger(number)) return errorBody(404, 'Not Found');
    const pr = repo.pulls.find((p) => p.number === number) ?? null;
    if (!pr) return errorBody(404, 'Not Found');
    // GET /pulls/{n}/files
    if (rest.length === 3 && rest[2] === 'files') {
      if (method !== 'GET') return errorBody(404, 'Not Found');
      const diff = prDiff(repo, pr);
      const mergeBaseFiles = diff.mergeBase ? flattenTree(repo, commitTreeOid(repo, diff.mergeBase)) : new Map();
      const files = [];
      for (const [path, change] of diff.changed) {
        let additions = 0;
        let deletions = 0;
        if (change.status === 'added') {
          const data = getObject(repo, change.oid)?.data ?? Buffer.alloc(0);
          additions = data.toString('utf8').split('\n').length;
          if (data.length > 0 && data[data.length - 1] === 0x0a) additions -= 1;
        } else if (change.status === 'modified') {
          const oldEntry = mergeBaseFiles.get(path);
          const oldText = oldEntry ? (getObject(repo, oldEntry.oid)?.data.toString('utf8') ?? '') : '';
          const newText = getObject(repo, change.oid)?.data.toString('utf8') ?? '';
          const d = lineDiff(oldText, newText);
          additions = Math.max(1, d.additions);
          deletions = d.deletions;
        } else if (change.status === 'removed') {
          const oldEntry = mergeBaseFiles.get(path);
          const oldText = oldEntry ? (getObject(repo, oldEntry.oid)?.data.toString('utf8') ?? '') : '';
          deletions = oldText.split('\n').length;
        }
        files.push({ filename: path, status: change.status, additions, deletions, changes: additions + deletions });
      }
      return jsonBody(200, files);
    }
    // PUT /pulls/{n}/merge
    if (rest.length === 3 && rest[2] === 'merge') {
      if (method !== 'PUT') return errorBody(404, 'Not Found');
      const result = mergePullRequest(repo, pr, typeof body?.merge_method === 'string' ? body.merge_method : 'squash');
      return jsonBody(result.status, result.body);
    }
    if (rest.length === 2) {
      if (method === 'GET') return jsonBody(200, pullJson(repo, pr));
      return errorBody(404, 'Not Found');
    }
    return errorBody(404, 'Not Found');
  }
  return null;
}

// ---------------------------------------------------------------------------
// GraphQL: a small parser and executor for the shapes `gh` and
// github-mcp-server send (queries, mutations, fragments, variables, batches).

function tokenizeGraphQL(source) {
  const tokens = [];
  let i = 0;
  const isNameStart = (c) => /[A-Za-z_]/.test(c);
  const isNameChar = (c) => /[A-Za-z0-9_]/.test(c);
  while (i < source.length) {
    const c = source[i];
    if (c === ' ' || c === '\t' || c === '\n' || c === '\r' || c === ',' || c === '\ufeff') {
      i += 1;
      continue;
    }
    if (c === '#') {
      while (i < source.length && source[i] !== '\n') i += 1;
      continue;
    }
    if (c === '.' && source.slice(i, i + 3) === '...') {
      tokens.push({ kind: 'spread' });
      i += 3;
      continue;
    }
    if ('{}():=@!$'.includes(c)) {
      tokens.push({ kind: c });
      i += 1;
      continue;
    }
    if (c === '[' || c === ']') {
      tokens.push({ kind: c });
      i += 1;
      continue;
    }
    if (c === '"') {
      let j = i + 1;
      let out = '';
      while (j < source.length && source[j] !== '"') {
        if (source[j] === '\\' && j + 1 < source.length) {
          const esc = source[j + 1];
          if (esc === 'n') out += '\n';
          else if (esc === 't') out += '\t';
          else if (esc === 'r') out += '\r';
          else if (esc === 'u') {
            out += String.fromCharCode(parseInt(source.slice(j + 2, j + 6), 16));
            j += 4;
          } else out += esc;
          j += 2;
        } else {
          out += source[j];
          j += 1;
        }
      }
      tokens.push({ kind: 'string', value: out });
      i = j + 1;
      continue;
    }
    if (c === '-' || /[0-9]/.test(c)) {
      let j = i;
      if (source[j] === '-') j += 1;
      while (j < source.length && /[0-9.]/.test(source[j])) j += 1;
      if (j < source.length && (source[j] === 'e' || source[j] === 'E')) {
        j += 1;
        if (source[j] === '+' || source[j] === '-') j += 1;
        while (j < source.length && /[0-9]/.test(source[j])) j += 1;
      }
      const text = source.slice(i, j);
      tokens.push({ kind: 'number', value: text.includes('.') || /e/i.test(text) ? parseFloat(text) : parseInt(text, 10) });
      i = j;
      continue;
    }
    if (isNameStart(c)) {
      let j = i;
      while (j < source.length && isNameChar(source[j])) j += 1;
      const name = source.slice(i, j);
      if (name === 'true' || name === 'false') tokens.push({ kind: 'boolean', value: name === 'true' });
      else if (name === 'null') tokens.push({ kind: 'null', value: null });
      else tokens.push({ kind: 'name', value: name });
      i = j;
      continue;
    }
    throw new Error(`unexpected character ${JSON.stringify(c)} in GraphQL document`);
  }
  tokens.push({ kind: 'eof' });
  return tokens;
}

function parseGraphQL(source) {
  const tokens = tokenizeGraphQL(source);
  let pos = 0;
  const peek = () => tokens[pos];
  const next = () => tokens[pos++];
  const expect = (kind) => {
    const token = next();
    if (token.kind !== kind) throw new Error(`expected ${kind} in GraphQL document, got ${token.kind}`);
    return token;
  };
  const parseName = () => expect('name').value;

  function parseValue() {
    const token = peek();
    if (token.kind === 'string' || token.kind === 'number' || token.kind === 'boolean' || token.kind === 'null') {
      next();
      return { kind: 'literal', value: token.value };
    }
    if (token.kind === 'name') {
      next();
      return { kind: 'enum', value: token.value };
    }
    if (token.kind === '$') {
      next();
      return { kind: 'variable', name: parseName() };
    }
    if (token.kind === '[') {
      next();
      const values = [];
      while (peek().kind !== ']') values.push(parseValue());
      expect(']');
      return { kind: 'list', values };
    }
    if (token.kind === '{') {
      next();
      const fields = {};
      while (peek().kind !== '}') {
        const name = parseName();
        expect(':');
        fields[name] = parseValue();
      }
      expect('}');
      return { kind: 'object', fields };
    }
    throw new Error(`unexpected token ${token.kind} as a GraphQL value`);
  }

  function parseArguments() {
    const args = {};
    if (peek().kind !== '(') return args;
    expect('(');
    while (peek().kind !== ')') {
      const name = parseName();
      expect(':');
      args[name] = parseValue();
    }
    expect(')');
    return args;
  }

  function parseDirectives() {
    const directives = [];
    while (peek().kind === '@') {
      next();
      const name = parseName();
      const args = parseArguments();
      directives.push({ name, args });
    }
    return directives;
  }

  function parseSelectionSet() {
    expect('{');
    const selections = [];
    while (peek().kind !== '}') {
      if (peek().kind === 'spread') {
        next();
        if (peek().kind === 'name' && peek().value === 'on') {
          next();
          const typeCondition = parseName();
          const directives = parseDirectives();
          selections.push({ kind: 'inline', typeCondition, directives, selectionSet: parseSelectionSet() });
        } else if (peek().kind === 'name') {
          const name = parseName();
          const directives = parseDirectives();
          selections.push({ kind: 'fragment', name, directives });
        } else {
          const directives = parseDirectives();
          selections.push({ kind: 'inline', typeCondition: null, directives, selectionSet: parseSelectionSet() });
        }
        continue;
      }
      let name = parseName();
      let alias = null;
      if (peek().kind === ':') {
        next();
        alias = name;
        name = parseName();
      }
      const args = parseArguments();
      const directives = parseDirectives();
      let selectionSet = null;
      if (peek().kind === '{') selectionSet = parseSelectionSet();
      selections.push({ kind: 'field', name, alias, args, directives, selectionSet });
    }
    expect('}');
    return selections;
  }

  function parseVariableDefinitions() {
    const defs = [];
    if (peek().kind !== '(') return defs;
    expect('(');
    while (peek().kind !== ')') {
      if (peek().kind === '$') next();
      const name = parseName();
      expect(':');
      // A type: a name, possibly wrapped in [ ] and suffixed with !.
      let type = '';
      const readType = () => {
        if (peek().kind === '[') {
          next();
          const inner = readType();
          expect(']');
          let t = `[${inner}]`;
          if (peek().kind === '!') {
            next();
            t += '!';
          }
          return t;
        }
        const base = parseName();
        let t = base;
        if (peek().kind === '!') {
          next();
          t += '!';
        }
        return t;
      };
      type = readType();
      let defaultValue = undefined;
      if (peek().kind === '=') {
        next();
        defaultValue = parseValue();
      }
      defs.push({ name, type, defaultValue });
    }
    expect(')');
    return defs;
  }

  const operations = [];
  const fragments = new Map();
  while (peek().kind !== 'eof') {
    if (peek().kind === '{') {
      operations.push({ kind: 'query', name: null, variables: [], selectionSet: parseSelectionSet() });
      continue;
    }
    if (peek().kind === 'name' && (peek().value === 'query' || peek().value === 'mutation' || peek().value === 'subscription')) {
      const opKind = next().value;
      let name = null;
      if (peek().kind === 'name') name = next().value;
      const variables = parseVariableDefinitions();
      const directives = parseDirectives();
      operations.push({ kind: opKind, name, variables, directives, selectionSet: parseSelectionSet() });
      continue;
    }
    if (peek().kind === 'name' && peek().value === 'fragment') {
      next();
      const name = parseName();
      if (peek().kind === 'name' && peek().value === 'on') next();
      const typeCondition = parseName();
      parseDirectives();
      fragments.set(name, { typeCondition, selectionSet: parseSelectionSet() });
      continue;
    }
    throw new Error(`unexpected token ${peek().kind} at the top of a GraphQL document`);
  }
  return { operations, fragments };
}

/** Resolve a parsed value node against the operation's variables. */
function resolveValue(node, variables) {
  if (!node) return undefined;
  if (node.kind === 'literal') return node.value;
  if (node.kind === 'enum') return node.value;
  if (node.kind === 'variable') return variables[node.name];
  if (node.kind === 'list') return node.values.map((v) => resolveValue(v, variables));
  if (node.kind === 'object') {
    const out = {};
    for (const [key, value] of Object.entries(node.fields)) out[key] = resolveValue(value, variables);
    return out;
  }
  return undefined;
}

function resolveArguments(argNodes, variables) {
  const out = {};
  for (const [key, node] of Object.entries(argNodes ?? {})) out[key] = resolveValue(node, variables);
  return out;
}

// ---------------------------------------------------------------------------
// GraphQL execution

function encodeGlobalId(kind, ...parts) {
  return b64encode(Buffer.from(`${kind}:${parts.join(':')}`, 'utf8'));
}

function decodeGlobalId(id) {
  if (typeof id !== 'string' || id === '') return null;
  let text;
  try {
    text = b64decode(id).toString('utf8');
  } catch {
    return null;
  }
  const parts = text.split(':');
  if (parts.length < 2) return null;
  return { kind: parts[0], parts: parts.slice(1) };
}

function encodeCursor(index) {
  return b64encode(Buffer.from(`cursor:${index}`, 'utf8'));
}

function decodeCursor(cursor) {
  try {
    const text = b64decode(cursor).toString('utf8');
    if (!text.startsWith('cursor:')) return null;
    const n = parseInt(text.slice('cursor:'.length), 10);
    return Number.isInteger(n) ? n : null;
  } catch {
    return null;
  }
}

function findRepoByDbId(dbId) {
  for (const repo of store.repos.values()) {
    if (repo.id === dbId) return repo;
  }
  return null;
}

/** A Relay-style connection over a filtered, sorted item list. */
function connectionFromItems(items, args, connectionTypename, edgeTypename, wrapNode) {
  const first = args.first === undefined || args.first === null ? items.length : clampInt(args.first, 0, 100, items.length);
  const after = typeof args.after === 'string' && args.after !== '' ? decodeCursor(args.after) : null;
  const start = after === null ? 0 : after + 1;
  const page = items.slice(start, start + first);
  const edges = page.map((item, i) => ({
    __typename: edgeTypename,
    node: wrapNode(item),
    cursor: encodeCursor(start + i),
  }));
  return {
    __typename: connectionTypename,
    nodes: page.map((item) => wrapNode(item)),
    edges,
    totalCount: items.length,
    pageInfo: {
      __typename: 'PageInfo',
      hasNextPage: start + first < items.length,
      hasPreviousPage: start > 0,
      startCursor: edges.length > 0 ? edges[0].cursor : null,
      endCursor: edges.length > 0 ? edges[edges.length - 1].cursor : null,
    },
  };
}

function sortIssues(items, orderBy) {
  const field = String(orderBy?.field ?? 'CREATED_AT').toUpperCase();
  const direction = String(orderBy?.direction ?? 'DESC').toUpperCase();
  const factor = direction === 'ASC' ? 1 : -1;
  // CREATED_AT, UPDATED_AT and COMMENTS all reduce to creation order here:
  // every record carries the same fixed timestamp, so the stable order is
  // the creation sequence.
  void field;
  return [...items].sort((a, b) => (a.seq - b.seq) * factor);
}

function issuesConnection(repo, args) {
  let items = [...repo.issues];
  if (Array.isArray(args.states) && args.states.length > 0) {
    const wanted = new Set(args.states.map((s) => String(s).toLowerCase()));
    items = items.filter((i) => wanted.has(i.state));
  }
  items = sortIssues(items, args.orderBy);
  return connectionFromItems(items, args, 'IssueConnection', 'IssueEdge', (issue) => ({ __typename: 'Issue', repo, issue }));
}

function pullsConnection(repo, args) {
  let items = [...repo.pulls];
  if (Array.isArray(args.states) && args.states.length > 0) {
    const wanted = new Set(args.states.map((s) => String(s).toUpperCase()));
    items = items.filter((p) => {
      const state = p.merged ? 'MERGED' : p.state === 'closed' ? 'CLOSED' : 'OPEN';
      return wanted.has(state);
    });
  }
  items = sortIssues(items, args.orderBy);
  return connectionFromItems(items, args, 'PullRequestConnection', 'PullRequestEdge', (pr) => ({ __typename: 'PullRequest', repo, pr }));
}

function prState(pr) {
  if (pr.merged) return 'MERGED';
  return pr.state === 'closed' ? 'CLOSED' : 'OPEN';
}

function issueState(issue) {
  return issue.state === 'closed' ? 'CLOSED' : 'OPEN';
}

const INTROSPECTION = {
  Query: { kind: 'OBJECT', fields: ['viewer', 'repository', 'node'] },
  Mutation: { kind: 'OBJECT', fields: ['createIssue', 'closeIssue', 'createPullRequest', 'mergePullRequest', 'addComment'] },
  Issue: {
    kind: 'OBJECT',
    fields: ['id', 'number', 'title', 'body', 'state', 'createdAt', 'updatedAt', 'author', 'repository', 'comments', 'url'],
  },
  PullRequest: {
    kind: 'OBJECT',
    fields: ['id', 'number', 'title', 'body', 'state', 'headRefName', 'baseRefName', 'headRef', 'baseRef', 'mergeable', 'merged', 'mergedAt', 'mergeCommit', 'files', 'author', 'repository', 'url'],
  },
  Repository: {
    kind: 'OBJECT',
    fields: ['id', 'databaseId', 'name', 'nameWithOwner', 'owner', 'defaultBranchRef', 'viewerPermission', 'hasIssuesEnabled', 'issue', 'issues', 'pullRequest', 'pullRequests', 'createdAt', 'updatedAt', 'url'],
  },
  User: { kind: 'OBJECT', fields: ['id', 'login', 'name', 'email', 'avatarUrl'] },
  Ref: { kind: 'OBJECT', fields: ['id', 'name', 'prefix'] },
  IssueConnection: { kind: 'OBJECT', fields: ['nodes', 'edges', 'pageInfo', 'totalCount'] },
  PullRequestConnection: { kind: 'OBJECT', fields: ['nodes', 'edges', 'pageInfo', 'totalCount'] },
  IssueCommentConnection: { kind: 'OBJECT', fields: ['nodes', 'edges', 'pageInfo', 'totalCount'] },
  PullRequestChangedFileConnection: { kind: 'OBJECT', fields: ['nodes', 'edges', 'pageInfo', 'totalCount'] },
  SearchType: { kind: 'ENUM', enumValues: ['ISSUE', 'REPOSITORY', 'USER', 'DISCUSSION', 'COMMIT', 'CODE', 'MILESTONE', 'LABEL'] },
  IssueState: { kind: 'ENUM', enumValues: ['OPEN', 'CLOSED'] },
  PullRequestState: { kind: 'ENUM', enumValues: ['OPEN', 'CLOSED', 'MERGED'] },
  MergeableState: { kind: 'ENUM', enumValues: ['MERGEABLE', 'CONFLICTING', 'UNKNOWN'] },
  PullRequestMergeMethod: { kind: 'ENUM', enumValues: ['MERGE', 'SQUASH', 'REBASE'] },
  RepositoryPermission: { kind: 'ENUM', enumValues: ['ADMIN', 'MAINTAIN', 'WRITE', 'TRIAGE', 'READ'] },
};

function introspectionType(name) {
  const entry = INTROSPECTION[name];
  if (!entry) return null;
  return { __typename: '__Type', typeName: name, kind: entry.kind };
}

/** Resolve one field on a value. Returns undefined for an unknown field (the caller records an error). */
function resolveGraphQLField(value, fieldName, args, ctx) {
  const typename = value.__typename;
  switch (typename) {
    case 'Query': {
      if (fieldName === 'viewer') return { __typename: 'User', login: VIEWER_LOGIN };
      if (fieldName === 'repository') {
        const repo = findRepo(args.owner, args.name);
        return repo ? { __typename: 'Repository', repo } : null;
      }
      if (fieldName === 'node') {
        const decoded = decodeGlobalId(args.id);
        if (!decoded) return null;
        if (decoded.kind === 'Repository') {
          const repo = findRepoByDbId(parseInt(decoded.parts[0], 10));
          return repo ? { __typename: 'Repository', repo } : null;
        }
        if (decoded.kind === 'Issue') {
          const repo = findRepoByDbId(parseInt(decoded.parts[0], 10));
          const issue = repo?.issues.find((i) => i.number === parseInt(decoded.parts[1], 10));
          return issue ? { __typename: 'Issue', repo, issue } : null;
        }
        if (decoded.kind === 'PullRequest') {
          const repo = findRepoByDbId(parseInt(decoded.parts[0], 10));
          const pr = repo?.pulls.find((p) => p.number === parseInt(decoded.parts[1], 10));
          return pr ? { __typename: 'PullRequest', repo, pr } : null;
        }
        if (decoded.kind === 'User') return { __typename: 'User', login: decoded.parts[0] };
        return null;
      }
      if (fieldName === '__type') return introspectionType(args.name);
      if (fieldName === '__schema') return { __typename: '__Schema' };
      return undefined;
    }
    case 'Mutation': {
      if (fieldName === 'createIssue') {
        const input = args.input ?? {};
        const decoded = decodeGlobalId(input.repositoryId);
        const repo = decoded && decoded.kind === 'Repository' ? findRepoByDbId(parseInt(decoded.parts[0], 10)) : null;
        if (!repo) return { __typename: 'CreateIssuePayload', issue: null, clientMutationId: input.clientMutationId ?? null };
        const issue = newIssueRecord(repo, { title: input.title ?? '', body: input.body ?? '', labels: [] });
        return { __typename: 'CreateIssuePayload', issue: { __typename: 'Issue', repo, issue }, clientMutationId: input.clientMutationId ?? null };
      }
      if (fieldName === 'closeIssue') {
        const input = args.input ?? {};
        const decoded = decodeGlobalId(input.issueId);
        let found = null;
        if (decoded && decoded.kind === 'Issue') {
          const repo = findRepoByDbId(parseInt(decoded.parts[0], 10));
          const issue = repo?.issues.find((i) => i.number === parseInt(decoded.parts[1], 10));
          if (issue) {
            issue.state = 'closed';
            found = { __typename: 'Issue', repo, issue };
          }
        }
        return { __typename: 'CloseIssuePayload', issue: found, clientMutationId: input.clientMutationId ?? null };
      }
      if (fieldName === 'createPullRequest') {
        const input = args.input ?? {};
        const decoded = decodeGlobalId(input.repositoryId);
        const repo = decoded && decoded.kind === 'Repository' ? findRepoByDbId(parseInt(decoded.parts[0], 10)) : null;
        if (!repo) return { __typename: 'CreatePullRequestPayload', pullRequest: null, clientMutationId: input.clientMutationId ?? null };
        const head = input.headRefName;
        const base = input.baseRefName;
        if (!refTip(repo, `refs/heads/${head}`) || !refTip(repo, `refs/heads/${base}`)) {
          return { __typename: 'CreatePullRequestPayload', pullRequest: null, clientMutationId: input.clientMutationId ?? null };
        }
        const pr = newPullRecord(repo, { title: input.title ?? '', body: input.body ?? '', head, base });
        return { __typename: 'CreatePullRequestPayload', pullRequest: { __typename: 'PullRequest', repo, pr }, clientMutationId: input.clientMutationId ?? null };
      }
      if (fieldName === 'mergePullRequest') {
        const input = args.input ?? {};
        const decoded = decodeGlobalId(input.pullRequestId);
        let found = null;
        if (decoded && decoded.kind === 'PullRequest') {
          const repo = findRepoByDbId(parseInt(decoded.parts[0], 10));
          const pr = repo?.pulls.find((p) => p.number === parseInt(decoded.parts[1], 10));
          if (pr && repo) {
            mergePullRequest(repo, pr, 'squash');
            found = { __typename: 'PullRequest', repo, pr };
          }
        }
        return { __typename: 'MergePullRequestPayload', pullRequest: found, clientMutationId: input.clientMutationId ?? null };
      }
      if (fieldName === 'addComment') {
        const input = args.input ?? {};
        const decoded = decodeGlobalId(input.subjectId);
        let edge = null;
        if (decoded && decoded.kind === 'Issue') {
          const repo = findRepoByDbId(parseInt(decoded.parts[0], 10));
          const number = parseInt(decoded.parts[1], 10);
          const issue = repo?.issues.find((i) => i.number === number);
          if (issue && repo) {
            const comment = { id: store.nextCommentId++, body: input.body ?? '', seq: (repo.comments.get(number) ?? []).length + 1 };
            if (!repo.comments.has(number)) repo.comments.set(number, []);
            repo.comments.get(number).push(comment);
            edge = { __typename: 'IssueCommentEdge', node: { __typename: 'IssueComment', repo, issueNumber: number, comment }, cursor: encodeCursor(comment.seq - 1) };
          }
        }
        return { __typename: 'AddCommentPayload', commentEdge: edge, clientMutationId: input.clientMutationId ?? null };
      }
      return undefined;
    }
    case 'Repository': {
      const repo = value.repo;
      if (fieldName === 'id') return encodeGlobalId('Repository', repo.id);
      if (fieldName === 'databaseId') return repo.id;
      if (fieldName === 'name') return repo.name;
      if (fieldName === 'nameWithOwner') return `${repo.owner}/${repo.name}`;
      if (fieldName === 'owner') return { __typename: 'User', login: repo.owner };
      if (fieldName === 'defaultBranchRef') {
        return headTip(repo) ? { __typename: 'Ref', name: repo.defaultBranch } : null;
      }
      if (fieldName === 'viewerPermission') return 'ADMIN';
      if (fieldName === 'hasIssuesEnabled') return true;
      if (fieldName === 'url') return `https://github.example/${repo.owner}/${repo.name}`;
      if (fieldName === 'createdAt' || fieldName === 'updatedAt') return FIXED_ISO;
      if (fieldName === 'issue') {
        const issue = repo.issues.find((i) => i.number === args.number);
        return issue ? { __typename: 'Issue', repo, issue } : null;
      }
      if (fieldName === 'issues') return issuesConnection(repo, args);
      if (fieldName === 'pullRequest') {
        const pr = repo.pulls.find((p) => p.number === args.number);
        return pr ? { __typename: 'PullRequest', repo, pr } : null;
      }
      if (fieldName === 'pullRequests') return pullsConnection(repo, args);
      return undefined;
    }
    case 'Issue': {
      const { repo, issue } = value;
      if (fieldName === 'id') return encodeGlobalId('Issue', repo.id, issue.number);
      if (fieldName === 'number') return issue.number;
      if (fieldName === 'title') return issue.title;
      if (fieldName === 'body') return issue.body ?? '';
      if (fieldName === 'state') return issueState(issue);
      if (fieldName === 'createdAt' || fieldName === 'updatedAt') return FIXED_ISO;
      if (fieldName === 'author') return { __typename: 'User', login: VIEWER_LOGIN };
      if (fieldName === 'repository') return { __typename: 'Repository', repo };
      if (fieldName === 'url') return `https://github.example/${repo.owner}/${repo.name}/issues/${issue.number}`;
      if (fieldName === 'comments') {
        const comments = repo.comments.get(issue.number) ?? [];
        return connectionFromItems(comments, args, 'IssueCommentConnection', 'IssueCommentEdge', (comment) => ({ __typename: 'IssueComment', repo, issueNumber: issue.number, comment }));
      }
      return undefined;
    }
    case 'PullRequest': {
      const { repo, pr } = value;
      if (fieldName === 'id') return encodeGlobalId('PullRequest', repo.id, pr.number);
      if (fieldName === 'number') return pr.number;
      if (fieldName === 'title') return pr.title;
      if (fieldName === 'body') return pr.body ?? '';
      if (fieldName === 'state') return prState(pr);
      if (fieldName === 'headRefName') return pr.head.ref;
      if (fieldName === 'baseRefName') return pr.base.ref;
      if (fieldName === 'headRef') return { __typename: 'Ref', name: pr.head.ref };
      if (fieldName === 'baseRef') return { __typename: 'Ref', name: pr.base.ref };
      if (fieldName === 'mergeable') return prMergeable(repo, pr);
      if (fieldName === 'merged') return pr.merged;
      if (fieldName === 'mergedAt') return pr.merged_at;
      if (fieldName === 'mergeCommit') {
        return pr.merge_commit_sha ? { __typename: 'Commit', oid: pr.merge_commit_sha } : null;
      }
      if (fieldName === 'createdAt' || fieldName === 'updatedAt') return FIXED_ISO;
      if (fieldName === 'author') return { __typename: 'User', login: VIEWER_LOGIN };
      if (fieldName === 'repository') return { __typename: 'Repository', repo };
      if (fieldName === 'url') return `https://github.example/${repo.owner}/${repo.name}/pull/${pr.number}`;
      if (fieldName === 'files') {
        const diff = prDiff(repo, pr);
        const mergeBaseFiles = diff.mergeBase ? flattenTree(repo, commitTreeOid(repo, diff.mergeBase)) : new Map();
        const files = [];
        for (const [path, change] of diff.changed) {
          let additions = 0;
          let deletions = 0;
          if (change.status === 'added') {
            const data = getObject(repo, change.oid)?.data ?? Buffer.alloc(0);
            additions = Math.max(1, data.toString('utf8').split('\n').length - (data.length > 0 && data[data.length - 1] === 0x0a ? 1 : 0));
          } else if (change.status === 'modified') {
            const oldEntry = mergeBaseFiles.get(path);
            const oldText = oldEntry ? (getObject(repo, oldEntry.oid)?.data.toString('utf8') ?? '') : '';
            const newText = getObject(repo, change.oid)?.data.toString('utf8') ?? '';
            const d = lineDiff(oldText, newText);
            additions = Math.max(1, d.additions);
            deletions = d.deletions;
          }
          files.push({ __typename: 'PullRequestChangedFile', path, additions, deletions });
        }
        return connectionFromItems(files, args, 'PullRequestChangedFileConnection', 'PullRequestChangedFileEdge', (file) => file);
      }
      return undefined;
    }
    case 'User': {
      if (fieldName === 'id') return encodeGlobalId('User', value.login);
      if (fieldName === 'login') return value.login;
      if (fieldName === 'name') return value.login === VIEWER_LOGIN ? VIEWER_NAME : value.login;
      if (fieldName === 'email') return value.login === VIEWER_LOGIN ? VIEWER_EMAIL : '';
      if (fieldName === 'avatarUrl') return '';
      return undefined;
    }
    case 'Ref': {
      if (fieldName === 'id') return encodeGlobalId('Ref', value.name);
      if (fieldName === 'name') return value.name;
      if (fieldName === 'prefix') return 'refs/heads/';
      return undefined;
    }
    case 'IssueConnection':
    case 'PullRequestConnection':
    case 'IssueCommentConnection':
    case 'PullRequestChangedFileConnection': {
      if (fieldName === 'nodes') return value.nodes;
      if (fieldName === 'edges') return value.edges;
      if (fieldName === 'pageInfo') return value.pageInfo;
      if (fieldName === 'totalCount') return value.totalCount;
      return undefined;
    }
    case 'IssueEdge':
    case 'PullRequestEdge':
    case 'IssueCommentEdge':
    case 'PullRequestChangedFileEdge': {
      if (fieldName === 'node') return value.node;
      if (fieldName === 'cursor') return value.cursor;
      return undefined;
    }
    case 'PageInfo': {
      if (fieldName === 'hasNextPage') return value.hasNextPage;
      if (fieldName === 'hasPreviousPage') return value.hasPreviousPage;
      if (fieldName === 'startCursor') return value.startCursor;
      if (fieldName === 'endCursor') return value.endCursor;
      return undefined;
    }
    case 'IssueComment': {
      if (fieldName === 'id') return encodeGlobalId('IssueComment', value.repo.id, value.issueNumber, value.comment.id);
      if (fieldName === 'body') return value.comment.body;
      if (fieldName === 'author') return { __typename: 'User', login: VIEWER_LOGIN };
      if (fieldName === 'createdAt' || fieldName === 'updatedAt') return FIXED_ISO;
      if (fieldName === 'url') return `https://github.example/${value.repo.owner}/${value.repo.name}/issues/${value.issueNumber}#issuecomment-${value.comment.id}`;
      return undefined;
    }
    case 'PullRequestChangedFile': {
      if (fieldName === 'path') return value.path;
      if (fieldName === 'additions') return value.additions;
      if (fieldName === 'deletions') return value.deletions;
      if (fieldName === 'changeType') return 'ADDED';
      return undefined;
    }
    case 'Commit': {
      if (fieldName === 'oid') return value.oid;
      if (fieldName === 'message') {
        const obj = value.repo ? getObject(value.repo, value.oid) : null;
        return obj && obj.type === 'commit' ? parseCommit(obj.data).message : '';
      }
      return undefined;
    }
    case 'CreateIssuePayload':
    case 'CloseIssuePayload': {
      if (fieldName === 'issue') return value.issue ?? null;
      if (fieldName === 'clientMutationId') return value.clientMutationId ?? null;
      return undefined;
    }
    case 'CreatePullRequestPayload':
    case 'MergePullRequestPayload': {
      if (fieldName === 'pullRequest') return value.pullRequest ?? null;
      if (fieldName === 'clientMutationId') return value.clientMutationId ?? null;
      return undefined;
    }
    case 'AddCommentPayload': {
      if (fieldName === 'commentEdge') return value.commentEdge ?? null;
      if (fieldName === 'comment') return value.commentEdge?.node ?? null;
      if (fieldName === 'clientMutationId') return value.clientMutationId ?? null;
      return undefined;
    }
    case '__Type': {
      const entry = INTROSPECTION[value.typeName];
      if (fieldName === 'name') return value.typeName;
      if (fieldName === 'kind') return value.kind;
      if (fieldName === 'fields') {
        if (!entry || !entry.fields) return null;
        return entry.fields.map((name) => ({ __typename: '__Field', name }));
      }
      if (fieldName === 'enumValues') {
        if (!entry || !entry.enumValues) return null;
        return entry.enumValues.map((name) => ({ __typename: '__EnumValue', name }));
      }
      return undefined;
    }
    case '__Field': {
      if (fieldName === 'name') return value.name;
      if (fieldName === 'description') return null;
      return undefined;
    }
    case '__EnumValue': {
      if (fieldName === 'name') return value.name;
      if (fieldName === 'description') return null;
      return undefined;
    }
    case '__Schema': {
      if (fieldName === 'types') return Object.keys(INTROSPECTION).map((name) => introspectionType(name));
      if (fieldName === 'queryType') return introspectionType('Query');
      if (fieldName === 'mutationType') return introspectionType('Mutation');
      return undefined;
    }
    default:
      return undefined;
  }
}

function executeSelection(parentValue, selectionSet, variables, fragments, errors, ctx) {
  if (parentValue === null || parentValue === undefined) return null;
  const out = {};
  for (const selection of selectionSet) {
    if (selection.kind === 'fragment') {
      const fragment = fragments.get(selection.name);
      if (!fragment) {
        errors.push({ message: `Unknown fragment "${selection.name}".` });
        continue;
      }
      Object.assign(out, executeSelection(parentValue, fragment.selectionSet, variables, fragments, errors, ctx));
      continue;
    }
    if (selection.kind === 'inline') {
      if (selection.typeCondition && selection.typeCondition !== parentValue.__typename) continue;
      Object.assign(out, executeSelection(parentValue, selection.selectionSet, variables, fragments, errors, ctx));
      continue;
    }
    const responseKey = selection.alias ?? selection.name;
    const args = resolveArguments(selection.args, variables);
    const value = resolveGraphQLField(parentValue, selection.name, args, ctx);
    if (value === undefined) {
      errors.push({ message: `Cannot query field "${selection.name}" on type "${parentValue.__typename}".` });
      out[responseKey] = null;
      continue;
    }
    if (!selection.selectionSet) {
      out[responseKey] = value === undefined ? null : value;
    } else if (value === null) {
      out[responseKey] = null;
    } else if (Array.isArray(value)) {
      out[responseKey] = value.map((item) => {
        if (item === null || item === undefined) return null;
        if (typeof item === 'object' && item.__typename) return executeSelection(item, selection.selectionSet, variables, fragments, errors, ctx);
        return item;
      });
    } else if (typeof value === 'object' && value.__typename) {
      out[responseKey] = executeSelection(value, selection.selectionSet, variables, fragments, errors, ctx);
    } else {
      out[responseKey] = value;
    }
  }
  return out;
}

function executeGraphQLDocument(source, operationName, variables) {
  let document;
  try {
    document = parseGraphQL(source);
  } catch (err) {
    return { data: null, errors: [{ message: err instanceof Error ? err.message : 'GraphQL parse error' }] };
  }
  const operation = operationName
    ? document.operations.find((op) => op.name === operationName) ?? null
    : document.operations[0] ?? null;
  if (!operation) {
    return { data: null, errors: [{ message: operationName ? `Unknown operation named "${operationName}".` : 'No operation provided.' }] };
  }
  const varValues = { ...(variables ?? {}) };
  for (const def of operation.variables) {
    if (varValues[def.name] === undefined && def.defaultValue !== undefined) {
      varValues[def.name] = resolveValue(def.defaultValue, varValues);
    }
  }
  const rootType = operation.kind === 'mutation' ? 'Mutation' : 'Query';
  const errors = [];
  const data = executeSelection({ __typename: rootType }, operation.selectionSet, varValues, document.fragments, errors, {});
  const out = { data };
  if (errors.length > 0) out.errors = errors;
  return out;
}

/** Handle POST /api/graphql. Body may be one operation or a JSON array (batch). */
function handleGraphQL(body) {
  if (Array.isArray(body)) {
    return body.map((entry) => {
      if (!entry || typeof entry.query !== 'string') return { data: null, errors: [{ message: 'A batched operation needs a query string.' }] };
      return executeGraphQLDocument(entry.query, entry.operationName ?? null, entry.variables ?? {});
    });
  }
  if (!body || typeof body.query !== 'string') {
    return { data: null, errors: [{ message: 'A GraphQL operation needs a query string.' }] };
  }
  return executeGraphQLDocument(body.query, body.operationName ?? null, body.variables ?? {});
}

// ---------------------------------------------------------------------------
// MCP (Model Context Protocol, JSON-RPC over streamable HTTP at /mcp)

const MCP_TOOLS = [
  {
    name: 'create_repo',
    description: 'Create a repository for the authenticated user.',
    inputSchema: {
      type: 'object',
      properties: {
        name: { type: 'string', description: 'The repository name.' },
        description: { type: 'string', description: 'A short description of the repository.' },
        private: { type: 'boolean', description: 'Whether the repository is private.' },
      },
      required: ['name'],
    },
  },
  {
    name: 'get_repo',
    description: 'Get a repository by owner and name.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'The repository owner login.' },
        repo: { type: 'string', description: 'The repository name.' },
      },
      required: ['owner', 'repo'],
    },
  },
  {
    name: 'create_issue',
    description: 'Create an issue in a repository.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'The repository owner login.' },
        repo: { type: 'string', description: 'The repository name.' },
        title: { type: 'string', description: 'The issue title.' },
        body: { type: 'string', description: 'The issue body.' },
      },
      required: ['owner', 'repo', 'title'],
    },
  },
  {
    name: 'list_issues',
    description: 'List issues in a repository.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'The repository owner login.' },
        repo: { type: 'string', description: 'The repository name.' },
        state: { type: 'string', description: 'Filter by state: open, closed, or all.' },
      },
      required: ['owner', 'repo'],
    },
  },
  {
    name: 'create_pull_request',
    description: 'Create a pull request in a repository.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'The repository owner login.' },
        repo: { type: 'string', description: 'The repository name.' },
        title: { type: 'string', description: 'The pull request title.' },
        body: { type: 'string', description: 'The pull request body.' },
        head: { type: 'string', description: 'The head branch name.' },
        base: { type: 'string', description: 'The base branch name.' },
      },
      required: ['owner', 'repo', 'title', 'head', 'base'],
    },
  },
  {
    name: 'merge_pull_request',
    description: 'Merge a pull request in a repository.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'The repository owner login.' },
        repo: { type: 'string', description: 'The repository name.' },
        pull_number: { type: 'integer', description: 'The pull request number.' },
      },
      required: ['owner', 'repo', 'pull_number'],
    },
  },
];

function mcpToolResult(payload) {
  return { content: [{ type: 'text', text: JSON.stringify(payload) }], structuredContent: payload, isError: false };
}

function mcpToolError(message) {
  return { content: [{ type: 'text', text: message }], isError: true };
}

function mcpFindRepo(args) {
  const owner = typeof args.owner === 'string' ? args.owner : VIEWER_LOGIN;
  const repo = typeof args.repo === 'string' ? args.repo : '';
  if (repo === '') return { error: 'a repo name is required' };
  const found = findRepo(owner, repo);
  if (!found) return { error: `repository ${owner}/${repo} not found` };
  return { repo: found };
}

/** Run one MCP tool. Returns { result } or { error } (a tool-level error, isError:true). */
function runMcpTool(name, args) {
  switch (name) {
    case 'create_repo': {
      const repoName = typeof args.name === 'string' ? args.name.trim() : '';
      if (repoName === '') return { error: 'a repo name is required' };
      if (findRepo(VIEWER_LOGIN, repoName)) return { error: `repository ${VIEWER_LOGIN}/${repoName} already exists` };
      const repo = createRepoRecord({
        name: repoName,
        owner: VIEWER_LOGIN,
        description: typeof args.description === 'string' ? args.description : '',
        isPrivate: args.private === true,
      });
      return { result: mcpToolResult(repoJson(repo)) };
    }
    case 'get_repo': {
      const found = mcpFindRepo(args);
      if (found.error) return found;
      return { result: mcpToolResult(repoJson(found.repo)) };
    }
    case 'create_issue': {
      const found = mcpFindRepo(args);
      if (found.error) return found;
      const title = typeof args.title === 'string' ? args.title : '';
      if (title === '') return { error: 'a title is required' };
      const issue = newIssueRecord(found.repo, { title, body: typeof args.body === 'string' ? args.body : '', labels: [] });
      return { result: mcpToolResult(issueJson(found.repo, issue)) };
    }
    case 'list_issues': {
      const found = mcpFindRepo(args);
      if (found.error) return found;
      let items = [...found.repo.issues];
      const state = typeof args.state === 'string' ? args.state : 'open';
      if (state !== 'all') items = items.filter((i) => i.state === state);
      const list = items.map((i) => issueJson(found.repo, i));
      return { result: mcpToolResult({ issues: list }) };
    }
    case 'create_pull_request': {
      const found = mcpFindRepo(args);
      if (found.error) return found;
      const title = typeof args.title === 'string' ? args.title : '';
      const head = typeof args.head === 'string' ? args.head : '';
      const base = typeof args.base === 'string' ? args.base : '';
      if (title === '' || head === '' || base === '') return { error: 'title, head and base are required' };
      if (!refTip(found.repo, `refs/heads/${head}`)) return { error: `head branch '${head}' does not exist` };
      if (!refTip(found.repo, `refs/heads/${base}`)) return { error: `base branch '${base}' does not exist` };
      const pr = newPullRecord(found.repo, { title, body: typeof args.body === 'string' ? args.body : '', head, base });
      return { result: mcpToolResult(pullJson(found.repo, pr)) };
    }
    case 'merge_pull_request': {
      const found = mcpFindRepo(args);
      if (found.error) return found;
      const number = typeof args.pull_number === 'number' ? args.pull_number : parseInt(args.pull_number, 10);
      if (!Number.isInteger(number)) return { error: 'a pull_number is required' };
      const pr = found.repo.pulls.find((p) => p.number === number);
      if (!pr) return { error: `pull request #${number} not found` };
      const result = mergePullRequest(found.repo, pr, 'squash');
      if (!result.ok) return { error: result.body.message };
      return { result: mcpToolResult({ number, merged: true, sha: result.body.sha, state: 'closed' }) };
    }
    default:
      return { unknownTool: true };
  }
}

function mcpErrorResponse(id, code, message) {
  return { status: 200, contentType: 'application/json', headers: {}, body: Buffer.from(JSON.stringify({ jsonrpc: '2.0', id: id ?? null, error: { code, message } }), 'utf8') };
}

/** Handle POST /mcp. `rawBody` is the request Buffer (kept raw to catch malformed JSON). */
function handleMcp(rawBody) {
  let request;
  try {
    request = JSON.parse(rawBody.toString('utf8'));
  } catch {
    return {
      status: 400,
      contentType: 'application/json',
      headers: {},
      body: Buffer.from(JSON.stringify({ jsonrpc: '2.0', id: null, error: { code: -32700, message: 'Parse error' } }), 'utf8'),
    };
  }
  const id = request && typeof request === 'object' && 'id' in request ? request.id : null;
  const method = request?.method;
  const params = request?.params ?? {};
  const ok = (result) => ({
    status: 200,
    contentType: 'application/json',
    headers: {},
    body: Buffer.from(JSON.stringify({ jsonrpc: '2.0', id, result }), 'utf8'),
  });
  // A notification (no id) is answered 202 with no body.
  if (id === null || id === undefined) {
    return { status: 202, contentType: 'application/json', headers: {}, body: Buffer.alloc(0) };
  }
  if (method === 'server/discover') {
    return ok({
      resultType: 'DiscoverResult',
      supportedVersions: [MCP_REVISION],
      capabilities: { tools: {} },
      serverInfo: { name: SERVER_NAME, version: SERVER_VERSION },
      _meta: { 'io.modelcontextprotocol/serverInfo': { name: SERVER_NAME, version: SERVER_VERSION } },
    });
  }
  if (method === 'initialize') {
    return ok({
      protocolVersion: MCP_REVISION,
      capabilities: { tools: {} },
      serverInfo: { name: SERVER_NAME, version: SERVER_VERSION },
    });
  }
  if (method === 'tools/list') {
    return ok({ tools: MCP_TOOLS });
  }
  if (method === 'tools/call') {
    const toolName = typeof params.name === 'string' ? params.name : '';
    const tool = MCP_TOOLS.find((t) => t.name === toolName);
    if (!tool) return mcpErrorResponse(id, -32602, `Unknown tool: ${toolName}`);
    const args = params.arguments && typeof params.arguments === 'object' ? params.arguments : {};
    const missing = (tool.inputSchema.required ?? []).filter((key) => args[key] === undefined || args[key] === null || args[key] === '');
    if (missing.length > 0) {
      return mcpErrorResponse(id, -32602, `Missing required arguments: ${missing.join(', ')}`);
    }
    const outcome = runMcpTool(toolName, args);
    if (outcome.unknownTool) return mcpErrorResponse(id, -32602, `Unknown tool: ${toolName}`);
    if (outcome.error) return ok(mcpToolError(outcome.error));
    return ok(outcome.result);
  }
  return mcpErrorResponse(id, -32601, `Method not found: ${method}`);
}

// ---------------------------------------------------------------------------
// HTTP server, routing, auth, lifecycle

function authorized(req) {
  const header = req.headers.authorization ?? '';
  if (!header.startsWith('Bearer ')) return false;
  const token = header.slice('Bearer '.length);
  if (token === '') return false;
  if (SHOP_TOKEN !== '') return token === SHOP_TOKEN;
  return true;
}

function sendResponse(res, result) {
  const headers = {
    'content-type': result.contentType ?? 'application/json',
    'x-github-request-id': nextRequestId(),
    ...result.headers,
  };
  res.writeHead(result.status, headers);
  res.end(result.body);
}

function readBody(req) {
  return new Promise((resolve, reject) => {
    const chunks = [];
    let total = 0;
    req.on('data', (chunk) => {
      total += chunk.length;
      if (total > MAX_BODY_BYTES) {
        reject(new Error('request body too large'));
        req.destroy();
        return;
      }
      chunks.push(chunk);
    });
    req.on('end', () => resolve(Buffer.concat(chunks)));
    req.on('error', reject);
  });
}

function parseJsonBody(raw) {
  if (raw.length === 0) return null;
  return JSON.parse(raw.toString('utf8'));
}

async function handleRequest(req, res) {
  const url = new URL(req.url ?? '/', 'http://127.0.0.1');
  const pathname = url.pathname;
  const query = Object.fromEntries(url.searchParams.entries());

  // GET /healthz: the boot check. No token, always 200.
  if (pathname === '/healthz' && req.method === 'GET') {
    sendResponse(res, jsonBody(200, { ok: true }));
    return;
  }

  // Every other route needs a bearer token.
  if (!authorized(req)) {
    sendResponse(res, errorBody(401, 'Unauthorized'));
    return;
  }

  const segments = pathname.split('/').filter((s) => s !== '').map((s) => {
    try {
      return decodeURIComponent(s);
    } catch {
      return s;
    }
  });

  try {
    // ---- git smart HTTP: /<owner>/<repo>.git/info/refs | git-upload-pack | git-receive-pack ----
    if (segments.length >= 3 && segments[2] === 'info' && segments[3] === 'refs') {
      const owner = segments[0];
      const repoName = segments[1].endsWith('.git') ? segments[1].slice(0, -4) : segments[1];
      const repo = findRepo(owner, repoName);
      if (!repo || owner.toLowerCase() !== VIEWER_LOGIN.toLowerCase()) {
        sendResponse(res, errorBody(404, 'Not Found'));
        return;
      }
      const service = query.service ?? '';
      if (service !== 'git-upload-pack' && service !== 'git-receive-pack') {
        sendResponse(res, errorBody(400, 'a service parameter is required'));
        return;
      }
      const gitProtocol = req.headers['git-protocol'] === 'version=2' ? 2 : 0;
      sendResponse(res, gitAdvertisement(repo, service, gitProtocol));
      return;
    }
    if (segments.length === 3 && (segments[2] === 'git-upload-pack' || segments[2] === 'git-receive-pack')) {
      const owner = segments[0];
      const repoName = segments[1].endsWith('.git') ? segments[1].slice(0, -4) : segments[1];
      const repo = findRepo(owner, repoName);
      if (!repo || owner.toLowerCase() !== VIEWER_LOGIN.toLowerCase()) {
        sendResponse(res, errorBody(404, 'Not Found'));
        return;
      }
      if (req.method !== 'POST') {
        sendResponse(res, errorBody(405, 'Method Not Allowed'));
        return;
      }
      const body = await readBody(req);
      if (segments[2] === 'git-upload-pack') {
        const gitProtocol = req.headers['git-protocol'] === 'version=2' ? 2 : 0;
        sendResponse(res, handleUploadPack(repo, body, gitProtocol));
      } else {
        sendResponse(res, await handleReceivePack(repo, body));
      }
      return;
    }

    // ---- GraphQL: POST /api/graphql ----
    if (pathname === '/api/graphql' && req.method === 'POST') {
      const raw = await readBody(req);
      let parsed;
      try {
        parsed = parseJsonBody(raw);
      } catch {
        sendResponse(res, jsonBody(400, { errors: [{ message: 'Request body is not valid JSON.' }] }));
        return;
      }
      const result = handleGraphQL(parsed);
      sendResponse(res, jsonBody(200, result));
      return;
    }

    // ---- MCP: POST /mcp (DELETE for a session close) ----
    if (pathname === '/mcp') {
      if (req.method === 'DELETE') {
        sendResponse(res, { status: 204, contentType: 'application/json', headers: {}, body: Buffer.alloc(0) });
        return;
      }
      if (req.method !== 'POST') {
        sendResponse(res, errorBody(405, 'Method Not Allowed'));
        return;
      }
      const raw = await readBody(req);
      sendResponse(res, handleMcp(raw));
      return;
    }

    // ---- REST v3: /api/v3/... ----
    if (segments[0] === 'api' && segments[1] === 'v3') {
      let parsed = null;
      if (req.method === 'POST' || req.method === 'PUT' || req.method === 'PATCH' || req.method === 'DELETE') {
        const raw = await readBody(req);
        if (raw.length > 0) {
          try {
            parsed = parseJsonBody(raw);
          } catch {
            sendResponse(res, errorBody(400, 'Request body is not valid JSON'));
            return;
          }
        }
      }
      const result = handleRest(req, segments.slice(2), query, parsed);
      sendResponse(res, result);
      return;
    }

    // ---- anything else: a JSON 404 ----
    sendResponse(res, errorBody(404, 'Not Found'));
  } catch (err) {
    // A handler that throws must not take the server down (repo-survives-errors).
    const message = err instanceof Error ? err.message : 'Internal Server Error';
    try {
      sendResponse(res, errorBody(500, message));
    } catch {
      // The socket is already gone; nothing more to do.
    }
  }
}

// ---------------------------------------------------------------------------
// lifecycle: register with the suite, poll /done, exit 0

async function postJson(url, payload) {
  const data = Buffer.from(JSON.stringify(payload), 'utf8');
  const response = await fetch(url, {
    method: 'POST',
    headers: { 'content-type': 'application/json', 'content-length': String(data.length) },
    body: data,
  });
  return response;
}

async function getJson(url) {
  const response = await fetch(url, { method: 'GET', headers: { accept: 'application/json' } });
  return response.json();
}

function sleep(ms) {
  return new Promise((resolve) => setTimeout(resolve, ms));
}

async function main() {
  const server = http.createServer((req, res) => {
    void handleRequest(req, res);
  });
  const port = process.env.PORT ? parseInt(process.env.PORT, 10) : 0;
  await new Promise((resolve, reject) => {
    server.once('error', reject);
    server.listen({ port: Number.isFinite(port) ? port : 0, host: '127.0.0.1' }, () => {
      server.removeListener('error', reject);
      resolve();
    });
  });
  const address = server.address();
  const boundPort = typeof address === 'object' && address !== null ? address.port : 0;
  if (ENV_URL !== '') {
    // The suite's lifecycle: register this port, then poll /done until the
    // suite is over. Never exit early, never hold a poll open.
    try {
      await postJson(`${ENV_URL}/register`, { port: boundPort });
    } catch (err) {
      process.stderr.write(`register failed: ${err instanceof Error ? err.message : String(err)}\n`);
    }
    for (;;) {
      try {
        const done = await getJson(`${ENV_URL}/done`);
        if (done && done.done === true) break;
      } catch {
        // A failed poll is not a stop: keep polling.
      }
      await sleep(500);
    }
    server.close();
    process.exit(0);
  }
  process.stdout.write(`github-forge listening on http://127.0.0.1:${boundPort}\n`);
}

void main();
