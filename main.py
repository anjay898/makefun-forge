#!/usr/bin/env python3
"""forge: a GitHub-compatible git forge that lives in a single file.

One process holds every repository in memory and answers four kinds of
traffic: git smart HTTP (protocol v0 and v2, upload-pack and
receive-pack), the REST v3 resource tree, the GraphQL v4 endpoint and
an MCP tool endpoint.  Nothing beyond the Python standard library is
used, and no state ever leaves the process.
"""

import base64
import datetime
import difflib
import hashlib
import http.server
import itertools
import json
import os
import re
import socket
import struct
import sys
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
import zlib

VIEWER = {
    "login": "adaiversen",
    "name": "ada iversen",
    "id": 1000,
    "email": "adaiversen@example.invalid",
}
TOKEN = os.environ.get("MAKEFUN_SHOP_TOKEN", "")
ZERO = "0" * 40
HEX_DIGITS = frozenset("0123456789abcdef")

_stamp_cell = [1735689600]
_stamp_guard = threading.RLock()


def next_stamp():
    with _stamp_guard:
        _stamp_cell[0] += 1
        fresh = _stamp_cell[0]
    return fresh


def utc_text(stamp):
    moment = datetime.datetime.fromtimestamp(int(stamp), datetime.timezone.utc)
    return moment.strftime("%Y-%m-%dT%H:%M:%SZ")


class Repository:
    """One hosted repository: object store, refs, and social state."""

    def __init__(self, id=0, name="", owner=None, private=False,
                 description="", default_branch="main"):
        self.id = id
        self.name = name
        self.owner = VIEWER["login"] if owner is None else owner
        self.private = private
        self.description = description
        self.default_branch = default_branch
        self.objects = {}
        self.refs = {}
        self.labels = {}
        self.issues = []
        self.pulls = []
        self.next_number = 1
        self.lock = threading.RLock()


class Catalog:
    """The whole forge: every repository, keyed by bare name."""

    def __init__(self):
        self.repos = {}
        self.next_repo_id = 1
        self.lock = threading.RLock()


CATALOG = Catalog()


def find_repo(owner, name):
    with CATALOG.lock:
        candidate = CATALOG.repos.get(name)
    if candidate is None or candidate.owner != owner:
        return None
    return candidate


def frozen_copy(repo):
    with repo.lock:
        clone = Repository(repo.id, repo.name, repo.owner, repo.private,
                           repo.description, repo.default_branch)
        clone.objects = dict(repo.objects)
        clone.refs = dict(repo.refs)
    return clone


def looks_like_oid(oid):
    if not isinstance(oid, str):
        return False
    return len(oid) == 40 and not (set(oid) - HEX_DIGITS)


# ---------------------------------------------------------------------------
# The git object model: blobs, trees, commits and tags in a plain dict.
# ---------------------------------------------------------------------------

def object_id(kind, data):
    prefix = kind.encode("ascii") + b" " + str(len(data)).encode("ascii") + b"\0"
    return hashlib.sha1(prefix + data).hexdigest()


def put_object(repo, kind, data):
    blob = bytes(data)
    oid = object_id(kind, blob)
    with repo.lock:
        if oid not in repo.objects:
            repo.objects[oid] = (kind, blob)
    return oid


def read_commit(data):
    head, _, message = data.partition(b"\n\n")
    commit = {
        "tree": "",
        "parents": [],
        "message": message.decode("utf-8", "replace"),
        "author": "",
        "committer": "",
        "timestamp": 0,
    }
    for raw_line in head.split(b"\n"):
        key, sep, value = raw_line.partition(b" ")
        if sep == b"":
            continue
        text = value.decode("utf-8", "replace")
        if key == b"tree":
            commit["tree"] = text
        elif key == b"parent":
            commit["parents"].append(text)
        elif key == b"author" or key == b"committer":
            commit[key.decode("ascii")] = text
    identity = commit["committer"] or commit["author"]
    fields = identity.rsplit(" ", 2)
    if len(fields) >= 2:
        try:
            commit["timestamp"] = int(fields[-2])
        except ValueError:
            pass
    return commit


LEGAL_MODES = (0o40000, 0o100644, 0o100755, 0o120000, 0o160000)


def checked_mode(mode):
    numeric = int(str(mode), 8)
    if numeric not in LEGAL_MODES:
        raise ValueError("invalid tree mode")
    return format(numeric, "o")


def read_tree(data):
    entries = []
    cursor = 0
    size = len(data)
    while cursor < size:
        space = data.find(b" ", cursor)
        if space <= cursor:
            raise ValueError("invalid tree")
        stop = data.find(b"\0", space + 1)
        if stop < 0 or stop + 21 > size:
            raise ValueError("invalid tree")
        mode = checked_mode(data[cursor:space].decode("ascii"))
        name = data[space + 1:stop].decode("utf-8", "surrogateescape")
        if name == "" or "/" in name:
            raise ValueError("invalid tree name")
        entries.append((mode, name, data[stop + 1:stop + 21].hex()))
        cursor = stop + 21
    return entries


def _tree_sort_key(entry):
    mode, raw_name, _oid = entry
    suffix = b"/" if mode == "40000" else b""
    return raw_name + suffix


def tree_bytes(entries):
    prepared = []
    seen_names = set()
    for mode, name, oid in entries:
        mode = checked_mode(mode)
        raw_name = name.encode("utf-8", "surrogateescape")
        if raw_name == b"" or b"/" in raw_name or b"\0" in raw_name:
            raise ValueError("invalid or duplicate tree name")
        if name in seen_names:
            raise ValueError("invalid or duplicate tree name")
        if not looks_like_oid(oid):
            raise ValueError("invalid object id")
        seen_names.add(name)
        prepared.append((mode, raw_name, oid))
    prepared.sort(key=_tree_sort_key)
    pieces = []
    for mode, raw_name, oid in prepared:
        pieces.append(mode.encode("ascii"))
        pieces.append(b" ")
        pieces.append(raw_name)
        pieces.append(b"\0")
        pieces.append(bytes.fromhex(oid))
    return b"".join(pieces)


def flatten(repo, tree_oid, prefix=""):
    with repo.lock:
        objects = dict(repo.objects)
    flat = {}

    def descend(oid, base, active):
        if oid in active:
            raise ValueError("tree cycle")
        found = objects.get(oid)
        if found is None:
            return
        if found[0] != "tree":
            raise ValueError("expected tree")
        active.add(oid)
        try:
            for mode, name, child in read_tree(found[1]):
                if mode == "40000":
                    descend(child, base + name + "/", active)
                else:
                    flat[base + name] = (mode, child)
        finally:
            active.discard(oid)

    descend(tree_oid, prefix, set())
    return flat


def unflatten(repo, flat):
    root = {}
    for path in flat:
        parts = path.split("/")
        for part in parts:
            if part in ("", ".", "..") or "\0" in part:
                raise ValueError("invalid path")
        node = root
        for part in parts[:-1]:
            child = node.get(part)
            if child is None:
                child = {}
                node[part] = child
            if not isinstance(child, dict):
                raise ValueError("file/directory conflict")
            node = child
        leaf = parts[-1]
        if leaf in node:
            raise ValueError("file/directory conflict")
        node[leaf] = flat[path]

    def build(node):
        entries = []
        for name in node:
            value = node[name]
            if isinstance(value, dict):
                entries.append(("40000", name, build(value)))
            else:
                entries.append((value[0], name, value[1]))
        return put_object(repo, "tree", tree_bytes(entries))

    with repo.lock:
        return build(root)


_commit_info_cache = {}


def commit_info(objects, oid):
    # (tree, parents) of a commit, memoized by oid: object content is
    # addressed by its hash, so the parsed shape can never go stale.
    info = _commit_info_cache.get(oid)
    if info is None:
        found = objects.get(oid)
        if found is None or found[0] != "commit":
            return "", ()
        parsed = read_commit(found[1])
        info = (parsed["tree"], tuple(parsed["parents"]))
        if len(_commit_info_cache) > 16384:
            _commit_info_cache.clear()
        _commit_info_cache[oid] = info
    return info


def ancestor_set(objects, tip):
    seen = set()
    stack = [tip]
    while stack:
        oid = stack.pop()
        if oid in seen:
            continue
        found = objects.get(oid)
        if found is None or found[0] != "commit":
            continue
        seen.add(oid)
        stack.extend(commit_info(objects, oid)[1])
    return seen


def is_ancestor(objects, anc, tip):
    # Early-exit reachability: in the common fast-forward case the old
    # tip is the new tip's parent, so this answers in a step or two
    # where ancestor_set would walk (and parse) the whole history.
    seen = set()
    stack = [tip]
    while stack:
        oid = stack.pop()
        if oid == anc:
            return True
        if oid in seen:
            continue
        seen.add(oid)
        stack.extend(commit_info(objects, oid)[1])
    return False


def history_of(repo, tip):
    with repo.lock:
        objects = dict(repo.objects)
    return ancestor_set(objects, tip)


def tag_points_to(data):
    for raw_line in data.split(b"\n"):
        if raw_line == b"":
            break
        if raw_line[:7] == b"object ":
            oid = raw_line[7:].decode("ascii")
            if not looks_like_oid(oid):
                raise ValueError("invalid tag target")
            return oid
    raise ValueError("missing tag target")


def sweep(objects, tips, exclude=frozenset(), stop_commits=frozenset()):
    seen = set()
    stack = list(tips)
    while stack:
        oid = stack.pop()
        if oid in seen or oid in exclude:
            continue
        found = objects.get(oid)
        if found is None:
            continue
        seen.add(oid)
        kind, data = found
        if kind == "commit":
            tree, parents = commit_info(objects, oid)
            stack.append(tree)
            if oid not in stop_commits:
                stack.extend(parents)
        elif kind == "tree":
            for mode, _name, child in read_tree(data):
                if mode != "160000":
                    stack.append(child)
        elif kind == "tag":
            stack.append(tag_points_to(data))
    return seen


def reachable_from(repo, tips, exclude=frozenset()):
    with repo.lock:
        objects = dict(repo.objects)
    return sweep(objects, tips, exclude=exclude)


def closure_from(repo, tips, stop_commits=frozenset()):
    with repo.lock:
        objects = dict(repo.objects)
    return sweep(objects, tips, stop_commits=stop_commits)


def new_commit(repo, parents, tree_oid, message, author=None):
    if author is not None:
        identity = author
    else:
        identity = VIEWER["name"] + " <" + VIEWER["email"] + ">"
    with repo.lock:
        stamp = next_stamp()
        lines = ["tree " + tree_oid]
        for parent in parents:
            lines.append("parent " + parent)
        lines.append("author " + identity + " " + str(stamp) + " +0000")
        lines.append("committer " + identity + " " + str(stamp) + " +0000")
        payload = ("\n".join(lines) + "\n\n" + message).encode("utf-8")
        return put_object(repo, "commit", payload)


# ---------------------------------------------------------------------------
# Packfiles: writing packs for fetch, reading packs back on push.
# ---------------------------------------------------------------------------

KIND_BY_CODE = {1: "commit", 2: "tree", 3: "blob", 4: "tag"}
CODE_BY_KIND = {name: code for code, name in KIND_BY_CODE.items()}


def _object_header(code, size):
    head = bytearray()
    head.append((code << 4) | (size & 0x0F) | (0x80 if size >> 4 else 0))
    rest = size >> 4
    while rest:
        piece = rest & 0x7F
        rest >>= 7
        head.append(piece | (0x80 if rest else 0))
    return bytes(head)


def pack_bytes(objs):
    body = bytearray(struct.pack(">4sII", b"PACK", 2, len(objs)))
    for _oid, kind, data in objs:
        code = CODE_BY_KIND.get(kind)
        if code is None:
            raise ValueError("invalid pack object type")
        body += _object_header(code, len(data))
        body += zlib.compress(data)
    body += hashlib.sha1(bytes(body)).digest()
    return bytes(body)


def _delta_varint(delta, pos):
    value = 0
    shift = 0
    while True:
        if pos >= len(delta) or shift > 63:
            raise ValueError("invalid delta length")
        byte = delta[pos]
        pos += 1
        value |= (byte & 0x7F) << shift
        if byte & 0x80 == 0:
            return value, pos
        shift += 7


def delta_apply(base, delta):
    base_size, pos = _delta_varint(delta, 0)
    target_size, pos = _delta_varint(delta, pos)
    if base_size != len(base):
        raise ValueError("delta base size mismatch")
    out = bytearray()
    limit = len(delta)
    while pos < limit:
        opcode = delta[pos]
        pos += 1
        if opcode & 0x80:
            offset = 0
            size = 0
            for bit in range(7):
                if opcode & (1 << bit) == 0:
                    continue
                if pos >= limit:
                    raise ValueError("truncated delta copy")
                taken = delta[pos]
                pos += 1
                if bit < 4:
                    offset |= taken << (8 * bit)
                else:
                    size |= taken << (8 * (bit - 4))
            if size == 0:
                size = 0x10000
            if offset + size > len(base) or len(out) + size > target_size:
                raise ValueError("delta copy out of bounds")
            out += base[offset:offset + size]
        elif opcode != 0:
            if pos + opcode > limit or len(out) + opcode > target_size:
                raise ValueError("delta insert out of bounds")
            out += delta[pos:pos + opcode]
            pos += opcode
        else:
            raise ValueError("invalid delta opcode")
    if len(out) != target_size:
        raise ValueError("delta result size mismatch")
    return bytes(out)


def _pack_obj_header(data, pos, end):
    if pos >= end:
        raise ValueError("truncated pack")
    first = data[pos]
    pos += 1
    kind = (first >> 4) & 7
    size = first & 15
    shift = 4
    current = first
    while current & 0x80:
        if shift > 63:
            raise ValueError("oversized pack header")
        if pos >= end:
            raise ValueError("truncated pack")
        current = data[pos]
        pos += 1
        size |= (current & 0x7F) << shift
        shift += 7
    return kind, size, pos


def _ofs_base(data, pos, end, start, entries):
    if pos >= end:
        raise ValueError("truncated pack")
    current = data[pos]
    pos += 1
    offset = current & 0x7F
    while current & 0x80:
        if offset > len(data):
            raise ValueError("invalid delta offset")
        if pos >= end:
            raise ValueError("truncated pack")
        current = data[pos]
        pos += 1
        offset = ((offset + 1) << 7) | (current & 0x7F)
    base = start - offset
    if offset <= 0 or base not in entries:
        raise ValueError("missing offset delta base")
    return base, pos


def _scan_pack(data, end, count):
    entries = {}
    ordered = []
    pos = 12
    for _round in range(count):
        start = pos
        kind, size, pos = _pack_obj_header(data, pos, end)
        base = None
        if kind == 6:
            base, pos = _ofs_base(data, pos, end, start, entries)
        elif kind == 7:
            if pos + 20 > end:
                raise ValueError("truncated reference delta")
            base = data[pos:pos + 20].hex()
            pos += 20
        elif kind not in KIND_BY_CODE:
            raise ValueError("invalid pack type")
        inflater = zlib.decompressobj()
        raw = inflater.decompress(memoryview(data)[pos:])
        if not inflater.eof:
            raise ValueError("truncated compressed object")
        consumed = len(data) - pos - len(inflater.unused_data)
        if consumed <= 0 or pos + consumed > end or len(raw) != size:
            raise ValueError("invalid compressed object size")
        pos += consumed
        entries[start] = (kind, base, raw)
        ordered.append(start)
    if pos != end:
        raise ValueError("unexpected pack trailing data")
    return entries, ordered


def unpack(data, lookup):
    try:
        return _unpack_inner(data, lookup)
    except ValueError:
        raise
    except Exception as exc:
        raise ValueError("corrupt pack") from exc


def _unpack_inner(data, lookup):
    if len(data) < 32 or data[:4] != b"PACK":
        raise ValueError("invalid pack header")
    version, count = struct.unpack(">II", data[4:12])
    if version not in (2, 3):
        raise ValueError("unsupported pack version")
    end = len(data) - 20
    if hashlib.sha1(memoryview(data)[:end]).digest() != data[end:]:
        raise ValueError("pack checksum mismatch")
    entries, ordered = _scan_pack(data, end, count)
    objects = {}
    resolved = {}
    waiting = list(ordered)
    while waiting:
        stuck = []
        for start in waiting:
            kind, base, raw = entries[start]
            if kind in KIND_BY_CODE:
                obj = (KIND_BY_CODE[kind], raw)
            else:
                if kind == 6:
                    base_obj = resolved.get(base)
                else:
                    base_obj = objects.get(base)
                    if base_obj is None:
                        try:
                            base_obj = lookup(base)
                        except KeyError:
                            base_obj = None
                        if base_obj is not None:
                            base_kind, base_data = base_obj
                            if (base_kind not in CODE_BY_KIND
                                    or object_id(base_kind, base_data) != base):
                                raise ValueError("invalid external delta base")
                if base_obj is None:
                    stuck.append(start)
                    continue
                obj = (base_obj[0], delta_apply(base_obj[1], raw))
            oid = object_id(obj[0], obj[1])
            resolved[start] = obj
            objects[oid] = obj
        if len(stuck) == len(waiting):
            raise ValueError("unresolved or cyclic delta bases")
        waiting = stuck
    return objects


# ---------------------------------------------------------------------------
# The git wire protocol: pkt-lines, ref advertisement, fetch and push.
# ---------------------------------------------------------------------------

PKT_FLUSH = b"0000"
PKT_DELIM = b"0001"
NOT_FOUND_REPLY = (404, "application/json", b'{"message":"Not Found"}')
_HEX_BYTES = b"0123456789abcdefABCDEF"


def pkt_line(payload):
    total = len(payload) + 4
    if total > 65520:
        raise ValueError("pkt-line too long")
    return format(total, "04x").encode("ascii") + payload


def read_pkt_lines(data, pos=0):
    if pos < 0 or pos > len(data):
        raise ValueError("invalid pkt-line position")
    lines = []
    while pos < len(data):
        if pos + 4 > len(data):
            raise ValueError("truncated pkt-line header")
        header = data[pos:pos + 4]
        if any(byte not in _HEX_BYTES for byte in header):
            raise ValueError("invalid pkt-line header")
        length = int(header, 16)
        pos += 4
        if length == 0:
            lines.append("flush")
            return lines, pos
        if length == 1:
            lines.append("delim")
            continue
        if length < 4 or length > 65520 or pos + length - 4 > len(data):
            raise ValueError("invalid pkt-line length")
        lines.append(data[pos:pos + length - 4])
        pos += length - 4
    return lines, pos


def peel_tag(objects, oid):
    seen = set()
    while oid in objects and objects[oid][0] == "tag":
        if oid in seen:
            raise ValueError("tag cycle")
        seen.add(oid)
        oid = tag_points_to(objects[oid][1])
    return oid


def wire_bytes(text):
    return text.encode("utf-8", "surrogateescape")


def band_wrap(data):
    chunks = []
    for start in range(0, len(data), 32768):
        chunks.append(pkt_line(b"\x01" + data[start:start + 32768]))
    return b"".join(chunks)


def advertise(repo, service, version2):
    if repo is None:
        return NOT_FOUND_REPLY
    if service not in ("git-upload-pack", "git-receive-pack"):
        return 400, "application/json", b'{"message":"Unsupported service"}'
    content_type = "application/x-" + service + "-advertisement"
    repo = frozen_copy(repo)
    if service == "git-upload-pack" and version2:
        lines = (b"version 2\n", b"agent=forge/1.0\n", b"ls-refs=unborn\n",
                 b"fetch=shallow wait-for-done\n", b"object-format=sha1\n")
        return 200, content_type, b"".join(pkt_line(x) for x in lines) + PKT_FLUSH
    target = "refs/heads/" + repo.default_branch
    symref = "symref=HEAD:" + target
    if service == "git-upload-pack":
        caps = "side-band-64k thin-pack ofs-delta shallow " + symref + " agent=forge/1.0"
    else:
        caps = "report-status side-band-64k delete-refs ofs-delta agent=forge/1.0 " + symref
    if repo.refs:
        first = repo.refs.get(target, ZERO) + " HEAD"
    else:
        first = ZERO + " capabilities^{}"
    parts = [pkt_line(wire_bytes("# service=" + service + "\n")), PKT_FLUSH]
    parts.append(pkt_line(wire_bytes(first) + b"\0" + wire_bytes(caps) + b"\n"))
    for name in sorted(repo.refs):
        oid = repo.refs[name]
        parts.append(pkt_line(wire_bytes(oid + " " + name + "\n")))
        found = repo.objects.get(oid)
        if name.startswith("refs/tags/") and found is not None and found[0] == "tag":
            peeled = peel_tag(repo.objects, oid)
            parts.append(pkt_line(wire_bytes(peeled + " " + name + "^{}\n")))
    parts.append(PKT_FLUSH)
    return 200, content_type, b"".join(parts)


def ls_refs_reply(repo, args):
    flags = set(args)
    prefixes = []
    for arg in args:
        if arg.startswith("ref-prefix "):
            prefixes.append(arg[len("ref-prefix "):])
    target = "refs/heads/" + repo.default_branch
    out = bytearray()
    names = ["HEAD"] + sorted(repo.refs)
    for name in names:
        if prefixes and not any(name.startswith(p) for p in prefixes):
            continue
        if name == "HEAD":
            oid = repo.refs.get(target)
            if oid is None and "unborn" in flags:
                line = "unborn HEAD symref-target:" + target
            else:
                line = (oid or ZERO) + " HEAD"
                if "symrefs" in flags:
                    line += " symref-target:" + target
        else:
            oid = repo.refs[name]
            line = oid + " " + name
            found = repo.objects.get(oid)
            if "peel" in flags and found is not None and found[0] == "tag":
                line += " peeled:" + peel_tag(repo.objects, oid)
        out += pkt_line(wire_bytes(line + "\n"))
    return bytes(out) + PKT_FLUSH


def fetch_wants(args):
    wants = []
    haves = []
    shallow = []
    deepen = None
    done = False
    for arg in args:
        fields = arg.split()
        if not fields:
            continue
        key = fields[0]
        if key == "want" or key == "have" or key == "shallow":
            if len(fields) < 2 or not looks_like_oid(fields[1]):
                raise ValueError("invalid fetch object id")
            bucket = wants if key == "want" else haves if key == "have" else shallow
            bucket.append(fields[1])
        elif key == "deepen":
            if len(fields) != 2:
                raise ValueError("invalid depth")
            deepen = int(fields[1])
            if deepen < 1:
                raise ValueError("invalid depth")
        elif key == "done":
            done = True
    return wants, haves, shallow, deepen, done


def _peel_into(objects, oid, tags):
    seen = set()
    while oid in objects and objects[oid][0] == "tag":
        if oid in seen:
            raise ValueError("tag cycle")
        seen.add(oid)
        tags.add(oid)
        oid = tag_points_to(objects[oid][1])
    return oid


def shallow_pick(objects, wants, depth):
    generations = {}
    tags = set()
    queue = []
    for want in wants:
        queue.append((_peel_into(objects, want, tags), 1))
    direct = set()
    cursor = 0
    while cursor < len(queue):
        oid, generation = queue[cursor]
        cursor += 1
        found = objects.get(oid)
        if found is None:
            continue
        if found[0] != "commit":
            direct |= sweep(objects, [oid])
            continue
        known = generations.get(oid)
        if generation > depth or (known is not None and known <= generation):
            continue
        generations[oid] = generation
        if generation < depth:
            for parent in commit_info(objects, oid)[1]:
                queue.append((parent, generation + 1))
    commits = set(generations)
    selected = sweep(objects, commits, stop_commits=commits) | direct | tags
    boundary = set()
    for oid in generations:
        if generations[oid] != depth:
            continue
        parents = commit_info(objects, oid)[1]
        if any(parent in objects for parent in parents):
            boundary.add(oid)
    return selected, commits, boundary


_pack_cache = {}
_pack_cache_guard = threading.Lock()


def pack_for(objects, selected):
    # Pack bytes depend only on the selected oid set, and object content
    # is immutable (the oid is its hash), so a cached pack stays valid.
    key = tuple(selected)
    with _pack_cache_guard:
        cached = _pack_cache.get(key)
    if cached is not None:
        return cached
    pack = pack_bytes([(oid, objects[oid][0], objects[oid][1])
                       for oid in selected])
    with _pack_cache_guard:
        if len(_pack_cache) > 128:
            _pack_cache.clear()
        _pack_cache[key] = pack
    return pack


def fetch_reply(repo, args, version2):
    wants, haves, shallow, deepen, done = fetch_wants(args)
    objects = repo.objects
    have_set = []
    for have in haves:
        if have in objects and have not in have_set:
            have_set.append(have)
    client_shallow = set()
    for oid in shallow:
        found = objects.get(oid)
        if found is not None and found[0] == "commit":
            client_shallow.add(oid)
    shallow_out = set()
    unshallow_out = set()
    if deepen is not None:
        selected, commits, shallow_out = shallow_pick(objects, wants, deepen)
        if version2:
            held = sweep(objects, have_set, stop_commits=client_shallow)
        else:
            held = set()
        selected -= held
        unshallow_out = (client_shallow & commits) - shallow_out
    elif client_shallow:
        selected = (sweep(objects, wants, stop_commits=client_shallow)
                    - sweep(objects, have_set, stop_commits=client_shallow))
        shallow_out = client_shallow
    else:
        held = sweep(objects, have_set)
        selected = sweep(objects, wants, exclude=held)
    if not any(want in objects for want in wants):
        selected = set()
        have_set = []
        shallow_out = set()
        unshallow_out = set()
    rank = {"commit": 0, "tree": 1, "blob": 2, "tag": 3}
    chosen = [oid for oid in selected if oid in objects]
    chosen.sort(key=lambda oid: (rank.get(objects[oid][0], 4), oid))
    pack = pack_for(objects, chosen)
    out = bytearray()

    def emit(raw):
        out.extend(pkt_line(raw))

    if version2:
        if not done:
            # Once the client says done, protocol v2 forbids the
            # acknowledgments section altogether.
            emit(b"acknowledgments\n")
            if have_set:
                for oid in have_set:
                    emit(wire_bytes("ACK " + oid + "\n"))
                emit(b"ready\n")
            else:
                emit(b"NAK\n")
            out.extend(PKT_DELIM)
        if shallow_out or unshallow_out:
            emit(b"shallow-info\n")
            for oid in sorted(shallow_out):
                emit(wire_bytes("shallow " + oid + "\n"))
            for oid in sorted(unshallow_out):
                emit(wire_bytes("unshallow " + oid + "\n"))
            out.extend(PKT_DELIM)
        emit(b"packfile\n")
    else:
        if deepen is not None:
            for oid in sorted(shallow_out):
                emit(wire_bytes("shallow " + oid + "\n"))
        emit(b"NAK\n")
    out.extend(band_wrap(pack))
    out.extend(PKT_FLUSH)
    return bytes(out)


def upload_pack(repo, body, version2):
    if repo is None:
        return NOT_FOUND_REPLY
    content_type = "application/x-git-upload-pack-result"
    repo = frozen_copy(repo)
    try:
        if version2:
            lines, pos = read_pkt_lines(body)
            if not lines or not isinstance(lines[0], bytes):
                raise ValueError("missing command")
            command = lines[0].rstrip(b"\n")
            if "delim" not in lines or lines[-1] != "flush":
                raise ValueError("invalid version 2 request")
            cut = lines.index("delim")
            args = []
            for line in lines[cut + 1:-1]:
                if not isinstance(line, bytes):
                    raise ValueError("unexpected marker")
                args.append(line.rstrip(b"\n").decode("utf-8", "surrogateescape"))
            if pos != len(body):
                raise ValueError("trailing request data")
            if command == b"command=ls-refs":
                result = ls_refs_reply(repo, args)
            elif command == b"command=fetch":
                result = fetch_reply(repo, args, True)
            else:
                raise ValueError("unknown command")
        else:
            args = []
            pos = 0
            while True:
                lines, pos = read_pkt_lines(body, pos)
                for line in lines:
                    if isinstance(line, bytes):
                        args.append(line.rstrip(b"\n").decode("utf-8", "surrogateescape"))
                    elif line != "flush":
                        raise ValueError("unexpected delimiter")
                if pos == len(body):
                    break
            result = fetch_reply(repo, args, False)
        return 200, content_type, result
    except (ValueError, UnicodeError, TypeError, IndexError, struct.error, zlib.error):
        return 400, content_type, b""


def push_report(commands, reasons, unpack, sideband, report_status):
    inner = bytearray()
    inner += pkt_line(wire_bytes("unpack " + unpack + "\n"))
    for command, reason in zip(commands, reasons):
        ref = command[2]
        if reason:
            inner += pkt_line(wire_bytes("ng " + ref + " " + reason + "\n"))
        else:
            inner += pkt_line(wire_bytes("ok " + ref + "\n"))
    inner += PKT_FLUSH
    if sideband:
        return band_wrap(bytes(inner)) + PKT_FLUSH
    return bytes(inner) if report_status else b""


def ref_ok(ref):
    if not ref.startswith("refs/"):
        return False
    if ref.endswith("/") or ref.endswith("."):
        return False
    for ch in ref:
        if ord(ch) < 32 or ord(ch) == 127 or ch in " ~^:?*[\\":
            return False
    if ".." in ref or "@{" in ref or "//" in ref:
        return False
    for part in ref.split("/"):
        if part == "" or part.startswith(".") or part.endswith(".lock"):
            return False
    return True


def _push_reject(staged, refs, old, new, ref):
    if not ref_ok(ref):
        return "invalid ref"
    if old != refs.get(ref, ZERO):
        return "reference already exists"
    if new == ZERO:
        return None if ref in refs else "reference does not exist"
    if new not in staged:
        return "missing object"
    if staged[new][0] not in ("commit", "tag"):
        return "bad object"
    if old != ZERO and ref.startswith("refs/tags/") and new != old:
        return "already exists"
    if old != ZERO:
        old_obj = staged.get(old)
        if old_obj is not None and old_obj[0] == "commit" and staged[new][0] == "commit":
            try:
                if not is_ancestor(staged, old, new):
                    return "non-fast-forward"
            except (ValueError, UnicodeError):
                return "bad object"
    return None


def receive_pack(repo, body):
    if repo is None:
        return NOT_FOUND_REPLY
    content_type = "application/x-git-receive-pack-result"
    commands = []
    caps = set()
    try:
        lines, pos = read_pkt_lines(body)
        if not lines or lines[-1] != "flush":
            raise ValueError("missing command flush")
        index = 0
        for line in lines[:-1]:
            if not isinstance(line, bytes):
                raise ValueError("invalid command marker")
            line = line.rstrip(b"\n")
            if index == 0:
                head, sep, cap_data = line.partition(b"\0")
                if sep:
                    caps = set(cap_data.decode("ascii").split())
                    line = head
            elif b"\0" in line:
                raise ValueError("unexpected capabilities")
            fields = line.decode("utf-8", "surrogateescape").split(" ")
            if len(fields) != 3:
                raise ValueError("invalid command")
            old, new, ref = fields
            if not looks_like_oid(old) or not looks_like_oid(new) or ref == "":
                raise ValueError("invalid command")
            commands.append((old, new, ref))
            index += 1
    except (ValueError, UnicodeError, TypeError, IndexError):
        return 400, content_type, b""

    sideband = "side-band-64k" in caps
    report_status = "report-status" in caps
    with repo.lock:
        if pos < len(body):
            try:
                incoming = unpack(body[pos:], repo.objects.get)
            except ValueError:
                report = push_report(commands, ["unpack failed"] * len(commands),
                                     "error", sideband, report_status)
                return 200, content_type, report
        else:
            incoming = {}
        staged = dict(repo.objects)
        staged.update(incoming)
        refs = dict(repo.refs)
        reasons = []
        successes = 0
        for old, new, ref in commands:
            reason = _push_reject(staged, refs, old, new, ref)
            reasons.append(reason)
            if reason is None:
                successes += 1
                if new == ZERO:
                    refs.pop(ref, None)
                else:
                    refs[ref] = new
        if successes:
            repo.objects.update(incoming)
            repo.refs.clear()
            repo.refs.update(refs)
        report = push_report(commands, reasons, "ok", sideband, report_status)
    return 200, content_type, report


# ---------------------------------------------------------------------------
# The service layer behind REST (and shared by GraphQL and MCP).
# ---------------------------------------------------------------------------

_id_counter = itertools.count(1)


def reply_json(status, obj, extra_headers=None):
    headers = {"content-type": "application/json; charset=utf-8"}
    if extra_headers:
        headers.update(extra_headers)
    return status, headers, json.dumps(obj).encode()


def reply_error(status, msg):
    return reply_json(status, {"message": msg})


def branch_tip(repo, branch):
    if branch.startswith("refs/"):
        return repo.refs.get(branch)
    return repo.refs.get("refs/heads/" + branch)


def commit_view(repo, oid):
    if not oid:
        return None
    found = repo.objects.get(oid)
    if found is None or found[0] != "commit":
        return None
    try:
        return read_commit(found[1])
    except Exception:
        return None


def parents_of(repo, oid):
    view = commit_view(repo, oid)
    if not view:
        return []
    return view.get("parents", [])


def message_of(repo, oid):
    view = commit_view(repo, oid) or {}
    return view.get("message", "")


def stamp_of(repo, oid):
    view = commit_view(repo, oid) or {}
    return view.get("ts", view.get("timestamp", view.get("time", repo.seq)))


def author_of(repo, oid):
    view = commit_view(repo, oid) or {}
    author = view.get("author", VIEWER.get("name", VIEWER["login"]))
    if isinstance(author, dict):
        return author.get("name", VIEWER.get("name", VIEWER["login"]))
    return str(author)


def short_ref(value):
    text = str(value or "")
    if text.startswith("refs/heads/"):
        text = text[len("refs/heads/"):]
    if ":" in text:
        text = text.split(":", 1)[1]
    return text


def count_lines(data):
    return len(data.decode("utf-8", "replace").splitlines())


def raw_bytes(repo, oid):
    found = repo.objects.get(oid)
    if found is None:
        return b""
    _kind, data = found
    if isinstance(data, bytes):
        return data
    return str(data).encode()


def create_repo(name, private=False, description=""):
    if not isinstance(name, str):
        return None
    if name.endswith(".git"):
        return None
    if re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9._-]*", name) is None:
        return None
    if name in CATALOG.repos:
        return None
    rid = CATALOG.next_repo_id
    CATALOG.next_repo_id += 1
    repo = Repository(rid, name, VIEWER["login"], bool(private),
                      description if isinstance(description, str) else "")
    repo.seq = next_stamp()
    CATALOG.repos[name] = repo
    return repo


def delete_repo(repo):
    CATALOG.repos.pop(repo.name, None)


def repo_view(repo):
    view = {}
    view["id"] = repo.id
    view["name"] = repo.name
    view["full_name"] = repo.owner + "/" + repo.name
    view["owner"] = {"login": repo.owner, "id": 1000}
    view["private"] = repo.private
    view["description"] = repo.description if repo.description is not None else ""
    view["default_branch"] = repo.default_branch
    view["html_url"] = ""
    view["clone_url"] = ""
    view["created_at"] = utc_text(repo.seq)
    view["updated_at"] = utc_text(repo.seq)
    return view


def create_issue(repo, title, body, label_names):
    if not isinstance(title, str) or title.strip() == "":
        return None, 422, "Validation Failed"
    if not isinstance(body, str):
        body = ""
    if not isinstance(label_names, list):
        label_names = []
    for name in label_names:
        if name not in repo.labels:
            return None, 422, "Validation Failed"
    number = repo.next_number
    repo.next_number += 1
    stamp = next_stamp()
    issue = {
        "id": next(_id_counter),
        "number": number,
        "title": title,
        "body": body,
        "state": "open",
        "labels": list(label_names),
        "comments": [],
        "seq": stamp,
        "ts": stamp,
    }
    repo.issues.append(issue)
    return issue, None, None


def issue_view(repo, issue):
    labels = []
    for name in issue["labels"]:
        if name in repo.labels:
            color = repo.labels[name]["color"]
        else:
            color = "ededed"
        labels.append({"name": name, "color": color})
    view = {
        "id": issue["id"],
        "number": issue["number"],
        "title": issue["title"],
        "body": issue["body"],
        "state": issue["state"],
        "labels": labels,
        "user": {"login": repo.owner},
        "comments": len(issue["comments"]),
        "created_at": utc_text(issue["seq"]),
        "updated_at": utc_text(issue["seq"]),
        "html_url": "",
    }
    return view


def create_pull(repo, title, body, head, base):
    head = short_ref(head)
    base = short_ref(base)
    if head == "" or base == "" or head == base:
        return None, 422, "Validation Failed"
    if branch_tip(repo, head) is None:
        return None, 422, "Validation Failed"
    if branch_tip(repo, base) is None:
        return None, 422, "Validation Failed"
    number = repo.next_number
    repo.next_number += 1
    stamp = next_stamp()
    pull = {
        "id": next(_id_counter),
        "number": number,
        "title": title if isinstance(title, str) else "",
        "body": body if isinstance(body, str) else "",
        "state": "open",
        "merged": False,
        "head_ref": head,
        "base_ref": base,
        "merge_commit_sha": None,
        "merged_seq": None,
        "seq": stamp,
        "ts": stamp,
        "comments": [],
    }
    repo.pulls.append(pull)
    return pull, None, None


def pull_view(repo, pull):
    head_sha = branch_tip(repo, pull["head_ref"]) or ZERO
    base_sha = branch_tip(repo, pull["base_ref"]) or ZERO
    if pull["merged_seq"] is not None:
        merged_at = utc_text(pull["merged_seq"])
    else:
        merged_at = None
    view = {
        "id": pull["id"],
        "number": pull["number"],
        "state": "closed" if pull["state"] == "closed" or pull["merged"] else "open",
        "title": pull["title"],
        "body": pull["body"],
        "merged": pull["merged"],
        "merged_at": merged_at,
        "merge_commit_sha": pull["merge_commit_sha"],
        "head": {
            "ref": pull["head_ref"],
            "sha": head_sha,
            "label": repo.owner + ":" + pull["head_ref"],
        },
        "base": {
            "ref": pull["base_ref"],
            "sha": base_sha,
            "label": repo.owner + ":" + pull["base_ref"],
        },
        "user": {"login": repo.owner},
        "created_at": utc_text(pull["seq"]),
        "updated_at": utc_text(pull["merged_seq"] or pull["seq"]),
        "html_url": "",
    }
    return view


def common_base(repo, a, b):
    if not a or not b:
        return None
    distances = {}
    queue = [(a, 0)]
    head = 0
    while head < len(queue):
        oid, depth = queue[head]
        head += 1
        if oid in distances:
            continue
        distances[oid] = depth
        for parent in parents_of(repo, oid):
            queue.append((parent, depth + 1))
    queue = [b]
    seen = set()
    head = 0
    while head < len(queue):
        oid = queue[head]
        head += 1
        if oid in seen:
            continue
        seen.add(oid)
        if oid in distances:
            return oid
        queue.extend(parents_of(repo, oid))
    return None


def flat_view(repo, commit_oid):
    if not commit_oid:
        return {}
    view = commit_view(repo, commit_oid)
    if not view:
        return {}
    return flatten(repo, view.get("tree"))


def merge_flats(repo, base_c, head_c, target_c):
    base = flat_view(repo, base_c)
    head = flat_view(repo, head_c)
    target = flat_view(repo, target_c)
    merged = {}
    conflict = False
    for path in sorted(set(base) | set(head) | set(target)):
        bv = base.get(path)
        hv = head.get(path)
        tv = target.get(path)
        if hv == tv:
            value = hv
        elif bv == hv:
            value = tv
        elif bv == tv:
            value = hv
        else:
            conflict = True
            continue
        if value is not None:
            merged[path] = value
    if conflict:
        return None, True
    return merged, False


def merge_pull(repo, pull, method="squash"):
    if pull["merged"] or pull["state"] == "closed":
        return None, 405, "Pull Request is not mergeable"
    head_tip = branch_tip(repo, pull["head_ref"])
    base_tip = branch_tip(repo, pull["base_ref"])
    if not head_tip or not base_tip:
        return None, 405, "Pull Request is not mergeable"
    shared = common_base(repo, head_tip, base_tip)
    merged_flat, conflict = merge_flats(repo, shared, head_tip, base_tip)
    if conflict:
        return None, 405, "Pull Request is not mergeable"
    tree = unflatten(repo, merged_flat)
    sha = new_commit(repo, [base_tip], tree,
                     "Merge pull request #" + str(pull["number"]))
    with repo.lock:
        repo.refs["refs/heads/" + pull["base_ref"]] = sha
        pull["state"] = "closed"
        pull["merged"] = True
        pull["merge_commit_sha"] = sha
        pull["merged_seq"] = next_stamp()
    return sha, None, None


def changed_files(repo, pull):
    head = branch_tip(repo, pull["head_ref"])
    base = branch_tip(repo, pull["base_ref"])
    old = flat_view(repo, common_base(repo, head, base))
    new = flat_view(repo, head)
    result = []
    for path in sorted(set(old) | set(new)):
        before = old.get(path)
        after = new.get(path)
        if before is None:
            additions = count_lines(raw_bytes(repo, after[1]))
            result.append({
                "filename": path,
                "status": "added",
                "additions": additions,
                "deletions": 0,
                "changes": additions,
                "sha": after[1],
            })
        elif after is None:
            deletions = count_lines(raw_bytes(repo, before[1]))
            result.append({
                "filename": path,
                "status": "removed",
                "additions": 0,
                "deletions": deletions,
                "changes": deletions,
                "sha": before[1],
            })
        elif before != after:
            a_lines = raw_bytes(repo, before[1]).decode("utf-8", "replace").splitlines()
            b_lines = raw_bytes(repo, after[1]).decode("utf-8", "replace").splitlines()
            additions = 0
            deletions = 0
            matcher = difflib.SequenceMatcher(None, a_lines, b_lines)
            for tag, i1, i2, j1, j2 in matcher.get_opcodes():
                if tag == "replace" or tag == "delete":
                    deletions += i2 - i1
                if tag == "replace" or tag == "insert":
                    additions += j2 - j1
            result.append({
                "filename": path,
                "status": "modified",
                "additions": additions,
                "deletions": deletions,
                "changes": additions + deletions,
                "sha": after[1],
            })
    return result


def put_file(repo, path, content_bytes, message, branch=None, sha=None):
    branch = branch or repo.default_branch
    ref = "refs/heads/" + branch
    tip = repo.refs.get(ref)
    if tip:
        flat = flat_view(repo, tip)
    else:
        tip = branch_tip(repo, repo.default_branch)
        flat = flat_view(repo, tip)
    existing = flat.get(path)
    if existing and sha is not None and sha != existing[1]:
        return 409, "sha does not match"
    blob = put_object(repo, "blob", content_bytes)
    flat[path] = ("100644", blob)
    tree = unflatten(repo, flat)
    commit = new_commit(repo, [tip] if tip else [], tree, message)
    with repo.lock:
        repo.refs[ref] = commit
    status = 200 if existing else 201
    payload = {
        "content": {
            "name": path.rsplit("/", 1)[-1],
            "path": path,
            "sha": blob,
            "size": len(content_bytes),
            "type": "file",
            "encoding": "base64",
        },
        "commit": {"sha": commit, "message": message},
    }
    return status, payload


def subtree_at(repo, root_oid, path):
    current = root_oid
    parts = [p for p in path.split("/") if p != ""]
    for part in parts:
        found = repo.objects.get(current)
        if found is None or found[0] != "tree":
            return None
        nxt = None
        for _mode, name, oid in read_tree(found[1]):
            if name == part:
                nxt = oid
                break
        if nxt is None:
            return None
        current = nxt
    return current


def get_file(repo, path, ref=None):
    if ref:
        if ref.startswith("refs/heads/"):
            tip = repo.refs.get(ref)
        elif ref in repo.refs:
            tip = repo.refs[ref]
        elif ref in repo.objects:
            tip = ref
        else:
            tip = repo.refs.get("refs/heads/" + ref)
    else:
        tip = branch_tip(repo, repo.default_branch)
    if not tip:
        return None
    flat = flat_view(repo, tip)
    if path in flat:
        oid = flat[path][1]
        data = raw_bytes(repo, oid)
        return {
            "type": "file",
            "encoding": "base64",
            "content": base64.b64encode(data).decode(),
            "sha": oid,
            "size": len(data),
            "name": path.rsplit("/", 1)[-1],
            "path": path,
        }
    prefix = path.rstrip("/") + "/" if path else ""
    children = {}
    for item in flat:
        if not item.startswith(prefix):
            continue
        rest = item[len(prefix):]
        if rest == "":
            continue
        name = rest.split("/", 1)[0]
        child_path = prefix + name
        if "/" in rest:
            view = commit_view(repo, tip)
            tree_oid = subtree_at(repo, view.get("tree"), child_path) if view else None
            children[name] = {
                "name": name,
                "path": child_path,
                "type": "dir",
                "sha": tree_oid,
            }
        else:
            children[name] = {
                "name": name,
                "path": child_path,
                "type": "file",
                "sha": flat[item][1],
            }
    if not children:
        return None
    return list(children.values())


def delete_file(repo, path, message, sha=None, branch=None):
    branch = branch or repo.default_branch
    ref = "refs/heads/" + branch
    tip = repo.refs.get(ref) or branch_tip(repo, repo.default_branch)
    flat = flat_view(repo, tip)
    existing = flat.get(path)
    if not existing:
        return 404, "Not Found"
    if sha is not None and sha != existing[1]:
        return 409, "sha does not match"
    del flat[path]
    tree = unflatten(repo, flat)
    commit = new_commit(repo, [tip] if tip else [], tree, message)
    with repo.lock:
        repo.refs[ref] = commit
    return 200, {"commit": {"sha": commit}}


def body_json(body_bytes, required=False):
    if not body_bytes:
        return {}, None
    try:
        value = json.loads(body_bytes.decode())
    except Exception:
        return None, reply_error(400, "Problems parsing JSON")
    if not isinstance(value, dict):
        return None, reply_error(400, "Problems parsing JSON")
    return value, None


def page_slice(items, query, base_path, host):
    try:
        page = max(1, int((query.get("page") or ["1"])[0]))
    except Exception:
        page = 1
    try:
        per_page = min(100, max(1, int((query.get("per_page") or ["30"])[0])))
    except Exception:
        per_page = 30
    total_pages = max(1, (len(items) + per_page - 1) // per_page)
    start = (page - 1) * per_page
    selected = items[start:start + per_page]
    headers = {}
    if page < total_pages:
        nxt = ("<http://" + host + base_path + "?page=" + str(page + 1)
               + "&per_page=" + str(per_page) + '>; rel="next", ')
        last = ("<http://" + host + base_path + "?page=" + str(total_pages)
                + "&per_page=" + str(per_page) + '>; rel="last"')
        headers["link"] = nxt + last
    return selected, headers


def comment_view(comment, created):
    return {
        "id": comment["id"],
        "body": comment["body"],
        "user": comment["user"],
        "created_at": utc_text(created),
        "updated_at": utc_text(created),
    }


def by_number(items, number):
    try:
        wanted = int(number)
    except Exception:
        return None
    for item in items:
        if item["number"] == wanted:
            return item
    return None


def _route_user_repos(method, query, body_bytes, host):
    if method == "GET":
        mine = [r for r in CATALOG.repos.values() if r.owner == VIEWER["login"]]
        mine.sort(key=lambda r: r.id)
        values, headers = page_slice(mine, query, "/api/v3/user/repos", host)
        return reply_json(200, [repo_view(r) for r in values], headers)
    if method == "POST":
        data, error = body_json(body_bytes, True)
        if error:
            return error
        repo = create_repo(data.get("name"), data.get("private", False),
                           data.get("description", ""))
        if repo is None:
            return reply_error(422, "Validation Failed: name already exists on this account")
        return reply_json(201, repo_view(repo))
    return None


def _route_repo(method, rest, query, body_bytes, host, repo, owner, name):
    if not rest:
        if method == "GET":
            return reply_json(200, repo_view(repo))
        if method == "PATCH":
            data, error = body_json(body_bytes, True)
            if error:
                return error
            if "description" in data:
                repo.description = data["description"]
            return reply_json(200, repo_view(repo))
        if method == "DELETE":
            delete_repo(repo)
            return 204, {}, b""

    if rest == ["labels"]:
        if method == "GET":
            return reply_json(200, list(repo.labels.values()))
        if method == "POST":
            data, error = body_json(body_bytes, True)
            if error:
                return error
            label_name = data.get("name")
            if not label_name:
                return reply_error(422, "Validation Failed")
            label = {"name": label_name, "color": data.get("color") or "ededed"}
            repo.labels[label_name] = label
            return reply_json(201, {**label, "default": False})

    if rest == ["git", "refs"] and method == "POST":
        data, error = body_json(body_bytes, True)
        if error:
            return error
        ref = data.get("ref")
        sha = data.get("sha")
        valid = (isinstance(ref, str) and ref.startswith("refs/heads/")
                 and sha in repo.objects and repo.objects[sha][0] == "commit")
        if not valid:
            return reply_error(422, "Validation Failed")
        repo.refs[ref] = sha
        return reply_json(201, {"ref": ref, "object": {"sha": sha, "type": "commit"}})

    if len(rest) >= 3 and rest[:3] == ["git", "refs", "heads"] and method == "GET":
        branch = "/".join(rest[3:])
        tip = branch_tip(repo, branch)
        if not tip:
            return reply_error(404, "Not Found")
        return reply_json(200, {
            "ref": "refs/heads/" + branch,
            "object": {"sha": tip, "type": "commit"},
        })

    if rest == ["branches"] and method == "GET":
        branches = []
        for ref in sorted(repo.refs):
            if ref.startswith("refs/heads/"):
                branches.append({
                    "name": ref[len("refs/heads/"):],
                    "commit": {"sha": repo.refs[ref]},
                    "protected": False,
                })
        return reply_json(200, branches)

    if len(rest) >= 2 and rest[0] == "branches" and method == "GET":
        branch = "/".join(rest[1:])
        tip = branch_tip(repo, branch)
        if not tip:
            return reply_error(404, "Not Found")
        return reply_json(200, {
            "name": branch,
            "commit": {"sha": tip},
            "protected": False,
        })

    if rest == ["commits"] and method == "GET":
        value = (query.get("sha") or [repo.default_branch])[0]
        tip = repo.refs.get(value) or repo.refs.get("refs/heads/" + value)
        if tip is None and value in repo.objects:
            tip = value
        commits = []
        seen = set()
        stack = [tip] if tip else []
        while stack and len(commits) < 100:
            oid = stack.pop(0)
            if oid in seen:
                continue
            seen.add(oid)
            if not commit_view(repo, oid):
                continue
            parents = parents_of(repo, oid)
            commits.append({
                "sha": oid,
                "commit": {
                    "message": message_of(repo, oid),
                    "author": {
                        "name": author_of(repo, oid),
                        "date": utc_text(stamp_of(repo, oid)),
                    },
                    "committer": {
                        "name": author_of(repo, oid),
                        "date": utc_text(stamp_of(repo, oid)),
                    },
                },
                "parents": [{"sha": p} for p in parents],
            })
            stack.extend(parents)
        return reply_json(200, commits)

    if rest and rest[0] == "contents":
        result = _route_contents(repo, method, rest, query, body_bytes)
        if result is not None:
            return result
    if rest and rest[0] == "issues":
        result = _route_issues(repo, method, rest, query, body_bytes, owner, name, host)
        if result is not None:
            return result
    if rest and rest[0] == "pulls":
        result = _route_pulls(repo, method, rest, query, body_bytes, owner, name, host)
        if result is not None:
            return result
    return None


def route_rest(method, seg, query, body_bytes, authed, host):
    if not authed:
        return reply_error(401, "Requires authentication")

    if method == "GET" and seg in ([], [""]):
        root = {
            "current_user_url": "/api/v3/user",
            "current_user_repositories_url": "/api/v3/user/repos",
            "repository_url": "/api/v3/repos/{owner}/{repo}",
        }
        return reply_json(200, root, {"x-oauth-scopes": "repo, read:org"})

    if method == "GET" and seg == ["meta"]:
        return reply_json(200, {"installed_version": "1.0.0-forge"})

    if method == "GET" and seg == ["user"]:
        return reply_json(200, {
            "login": VIEWER["login"],
            "id": 1000,
            "name": VIEWER["name"],
            "email": VIEWER["email"],
            "type": "User",
        })

    if seg == ["user", "repos"]:
        result = _route_user_repos(method, query, body_bytes, host)
        if result is not None:
            return result

    if len(seg) >= 3 and seg[0] == "repos":
        owner, name = seg[1], seg[2]
        repo = find_repo(owner, name)
        if repo is None:
            return reply_error(404, "Not Found")
        result = _route_repo(method, seg[3:], query, body_bytes, host,
                             repo, owner, name)
        if result is not None:
            return result

    return reply_error(404, "Not Found")


def _route_contents(repo, method, rest, query, body_bytes):
    path = "/".join(rest[1:])
    if method == "GET":
        value = get_file(repo, path, (query.get("ref") or [None])[0])
        if value is None:
            return reply_error(404, "Not Found")
        return reply_json(200, value)
    if method == "PUT" or method == "DELETE":
        data, error = body_json(body_bytes, True)
        if error:
            return error
        if method == "PUT":
            try:
                content = base64.b64decode(data.get("content", ""), validate=True)
            except Exception:
                return reply_error(400, "Invalid base64")
            status, value = put_file(repo, path, content,
                                     data.get("message") or "Update " + path,
                                     data.get("branch"), data.get("sha"))
        else:
            status, value = delete_file(repo, path,
                                        data.get("message") or "Delete " + path,
                                        data.get("sha"), data.get("branch"))
        if isinstance(value, str):
            return reply_error(status, value)
        return reply_json(status, value)
    return None


def _route_issues(repo, method, rest, query, body_bytes, owner, name, host):
    tail = rest[1:]
    if not tail:
        if method == "POST":
            data, error = body_json(body_bytes, True)
            if error:
                return error
            issue, status, msg = create_issue(repo, data.get("title"),
                                              data.get("body", ""),
                                              data.get("labels", []))
            if issue is None:
                return reply_error(status, msg)
            return reply_json(201, issue_view(repo, issue))
        if method == "GET":
            state = (query.get("state") or ["open"])[0]
            issues = [i for i in repo.issues
                      if state == "all" or i["state"] == state]
            issues.sort(key=lambda i: i["seq"], reverse=True)
            if (query.get("direction") or ["desc"])[0] == "asc":
                issues.reverse()
            values, headers = page_slice(
                issues, query,
                "/api/v3/repos/" + owner + "/" + name + "/issues", host)
            return reply_json(200, [issue_view(repo, i) for i in values], headers)
        return None
    issue = by_number(repo.issues, tail[0])
    if issue is None:
        return reply_error(404, "Not Found")
    if len(tail) == 1 and method == "GET":
        return reply_json(200, issue_view(repo, issue))
    if len(tail) == 1 and method == "PATCH":
        data, error = body_json(body_bytes, True)
        if error:
            return error
        labels = data.get("labels", issue["labels"])
        for label in labels:
            if label not in repo.labels:
                return reply_error(422, "Validation Failed")
        for key in ("title", "body", "state"):
            if key in data:
                issue[key] = data[key]
        issue["labels"] = labels
        issue["seq"] = next_stamp()
        return reply_json(200, issue_view(repo, issue))
    if len(tail) == 2 and tail[1] == "comments":
        if method == "GET":
            return reply_json(200, [comment_view(c, c["seq"])
                                    for c in issue["comments"]])
        if method == "POST":
            data, error = body_json(body_bytes, True)
            if error:
                return error
            if not data.get("body"):
                return reply_error(422, "Validation Failed")
            stamp = next_stamp()
            comment = {
                "id": next(_id_counter),
                "body": data["body"],
                "user": {"login": repo.owner},
                "seq": stamp,
            }
            issue["comments"].append(comment)
            return reply_json(201, comment_view(comment, stamp))
    return None


def _route_pulls(repo, method, rest, query, body_bytes, owner, name, host):
    tail = rest[1:]
    if not tail:
        if method == "POST":
            data, error = body_json(body_bytes, True)
            if error:
                return error
            pull, status, msg = create_pull(repo, data.get("title"),
                                            data.get("body", ""),
                                            data.get("head"), data.get("base"))
            if pull is None:
                return reply_error(status, msg)
            return reply_json(201, pull_view(repo, pull))
        if method == "GET":
            state = (query.get("state") or ["open"])[0]
            pulls = []
            for p in repo.pulls:
                if state == "all":
                    pulls.append(p)
                elif state == "closed" and (p["state"] == "closed" or p["merged"]):
                    pulls.append(p)
                elif state == "open" and p["state"] == "open" and not p["merged"]:
                    pulls.append(p)
            pulls.sort(key=lambda p: p["seq"], reverse=True)
            values, headers = page_slice(
                pulls, query,
                "/api/v3/repos/" + owner + "/" + name + "/pulls", host)
            return reply_json(200, [pull_view(repo, p) for p in values], headers)
        return None
    pull = by_number(repo.pulls, tail[0])
    if pull is None:
        return reply_error(404, "Not Found")
    if len(tail) == 1 and method == "GET":
        return reply_json(200, pull_view(repo, pull))
    if len(tail) == 2 and tail[1] == "files" and method == "GET":
        return reply_json(200, changed_files(repo, pull))
    if len(tail) == 2 and tail[1] == "merge" and method == "PUT":
        sha, status, msg = merge_pull(repo, pull)
        if sha is None:
            return reply_error(status, msg)
        return reply_json(200, {
            "sha": sha,
            "merged": True,
            "message": "Pull Request successfully merged",
        })
    return None


# ---------------------------------------------------------------------------
# GraphQL: node ids, the type/field census, and the document parser.
# ---------------------------------------------------------------------------

class GqlEnum(str):
    """A GraphQL enum literal, kept distinct from a plain string."""


class GqlObj:
    """A resolved GraphQL object: a type name plus its backing data."""

    def __init__(self, type_name, data):
        self.type_name = type_name
        self.data = data


def global_id(type_name, db_id):
    raw = (type_name + ":" + str(db_id)).encode()
    return base64.b64encode(raw).decode()


def split_global_id(text):
    try:
        raw = base64.b64decode(text, validate=True).decode()
        kind, ident = raw.split(":", 1)
        return kind, int(ident)
    except Exception:
        return None


def repo_for_id(db_id):
    for repo in CATALOG.repos.values():
        if getattr(repo, "id", None) == db_id:
            return repo
    return None


def issue_for_id(db_id):
    for repo in CATALOG.repos.values():
        for issue in repo.issues:
            if issue.get("id") == db_id:
                return repo, issue
    return None


def pull_for_id(db_id):
    for repo in CATALOG.repos.values():
        for pull in repo.pulls:
            if pull.get("id") == db_id:
                return repo, pull
    return None


def comment_for_id(db_id):
    for repo in CATALOG.repos.values():
        for issue in repo.issues:
            for comment in issue.get("comments", []):
                if comment.get("id") == db_id:
                    return repo, issue, comment
        for pull in repo.pulls:
            for comment in pull.get("comments", []):
                if comment.get("id") == db_id:
                    return repo, pull, comment
    return None


def _field_map(*names):
    return {name: 1 for name in names}


FIELDS_OF_TYPE = {
    "Query": _field_map("viewer", "repository", "node", "search",
                        "__type", "__schema"),
    "Mutation": _field_map("createIssue", "closeIssue", "createPullRequest",
                           "mergePullRequest", "addComment"),
    "User": _field_map("id", "login", "name", "email"),
    "Repository": _field_map(
        "id", "databaseId", "name", "nameWithOwner", "owner",
        "defaultBranchRef", "viewerPermission", "hasIssuesEnabled",
        "isPrivate", "description", "issue", "issues", "pullRequest",
        "pullRequests", "url", "createdAt", "updatedAt"),
    "Ref": _field_map("name", "target"),
    "Commit": _field_map("oid", "message"),
    "Issue": _field_map(
        "id", "databaseId", "number", "title", "state", "body", "author",
        "labels", "comments", "createdAt", "updatedAt", "url", "closed",
        "repository"),
    "IssueConnection": _field_map("nodes", "edges", "pageInfo", "totalCount"),
    "IssueEdge": _field_map("node", "cursor"),
    "PageInfo": _field_map("hasNextPage", "hasPreviousPage",
                           "startCursor", "endCursor"),
    "Label": _field_map("name", "color"),
    "LabelConnection": _field_map("nodes", "totalCount"),
    "IssueComment": _field_map("id", "body", "author", "createdAt"),
    "CommentConnection": _field_map("nodes", "totalCount"),
    "PullRequest": _field_map(
        "id", "databaseId", "number", "title", "body", "state", "merged",
        "mergeable", "headRefName", "baseRefName", "headRefOid",
        "baseRefOid", "files", "author", "createdAt", "updatedAt",
        "mergedAt", "url", "repository", "comments"),
    "PullRequestConnection": _field_map("nodes", "totalCount"),
    "PullRequestFile": _field_map("path"),
    "PullRequestChangedFile": _field_map("path"),
    "PullRequestFilesConnection": _field_map("nodes", "totalCount"),
    "CreateIssuePayload": _field_map("issue", "clientMutationId"),
    "CloseIssuePayload": _field_map("issue", "clientMutationId"),
    "CreatePullRequestPayload": _field_map("pullRequest", "clientMutationId"),
    "MergePullRequestPayload": _field_map("pullRequest", "clientMutationId"),
    "AddCommentPayload": _field_map("commentEdge", "clientMutationId"),
    "CommentEdge": _field_map("node", "cursor"),
    "SearchResultItemConnection": _field_map("nodes", "edges", "pageInfo",
                                             "issueCount"),
    "__Type": _field_map("name", "kind", "description", "fields", "enumValues"),
    "__Field": _field_map("name", "description", "type"),
    "__EnumValue": _field_map("name", "description"),
    "__Schema": _field_map("types", "queryType", "mutationType",
                           "subscriptionType"),
}

ENUM_VALUES = {
    "SearchType": ["ISSUE", "REPOSITORY", "USER", "DISCUSSION"],
    "IssueState": ["OPEN", "CLOSED"],
    "PullRequestState": ["OPEN", "CLOSED", "MERGED"],
    "MergeableState": ["MERGEABLE", "CONFLICTING", "UNKNOWN"],
    "OrderDirection": ["ASC", "DESC"],
    "IssueOrderField": ["CREATED_AT", "UPDATED_AT", "COMMENTS"],
    "RepositoryPermission": ["ADMIN", "MAINTAIN", "WRITE", "TRIAGE", "READ"],
    "PullRequestMergeMethod": ["MERGE", "SQUASH", "REBASE"],
}


_INT_TOKEN = re.compile(r"-?\d+")
_NAME_TOKEN = re.compile(r"[_A-Za-z][_0-9A-Za-z]*")
_PUNCT = "{}()[]:@!$"


def _scan_string(text, start):
    j = start + 1
    escaped = False
    while j < len(text):
        ch = text[j]
        if ch == '"' and not escaped:
            raw = text[start:j + 1]
            return json.loads(raw), j + 1
        if ch == "\\" and not escaped:
            escaped = True
        else:
            escaped = False
        j += 1
    raise ValueError("Unterminated string")


class DocumentParser:
    """A small GraphQL document parser: operations, fields, arguments."""

    def __init__(self, text):
        self.text = text
        self.tokens = self._tokenize(text)
        self.pos = 0
        self.fragments = {}

    @staticmethod
    def _tokenize(text):
        tokens = []
        i = 0
        size = len(text)
        while i < size:
            ch = text[i]
            if ch.isspace() or ch == ",":
                i += 1
            elif ch == "#":
                stop = text.find("\n", i)
                i = size if stop < 0 else stop + 1
            elif text.startswith("...", i):
                tokens.append(("...", "..."))
                i += 3
            elif ch in _PUNCT:
                tokens.append((ch, ch))
                i += 1
            elif ch == '"':
                value, i = _scan_string(text, i)
                tokens.append(("string", value))
            else:
                match = _INT_TOKEN.match(text, i)
                if match is not None:
                    tokens.append(("int", int(match.group(0))))
                    i = match.end()
                    continue
                match = _NAME_TOKEN.match(text, i)
                if match is not None:
                    tokens.append(("name", match.group(0)))
                    i = match.end()
                    continue
                raise ValueError("Unexpected character: " + ch)
        tokens.append(("EOF", None))
        return tokens

    def peek(self, kind=None, value=None):
        kind_here, value_here = self.tokens[self.pos]
        if kind is not None and kind_here != kind:
            return False
        return value is None or value_here == value

    def take(self, kind=None, value=None):
        if not self.peek(kind, value):
            got = self.tokens[self.pos]
            expected = kind or value or "token"
            raise ValueError(f"Expected {expected}, got {got[1]!r}")
        taken = self.tokens[self.pos]
        self.pos += 1
        return taken[1]

    def parse(self):
        operations = []
        while not self.peek("EOF"):
            if self.peek("{"):
                kind, name = "query", None
            else:
                kind = self.take("name")
                if kind not in ("query", "mutation"):
                    raise ValueError("Unknown operation " + str(kind))
                name = None
                if self.peek("name"):
                    name = self.take("name")
                if self.peek("("):
                    self.skip_parens()
                if self.peek("@"):
                    self.skip_directives()
            chosen = self.selection()
            operations.append({"kind": kind, "name": name, "selection": chosen})
        return operations, self.fragments

    def skip_parens(self):
        depth = 0
        while True:
            token = self.take()
            if token == "(":
                depth += 1
            elif token == ")":
                depth -= 1
                if depth == 0:
                    return

    def skip_directives(self):
        while self.peek("@"):
            self.take("@")
            self.take("name")
            if self.peek("("):
                self.skip_parens()

    def selection(self):
        self.take("{")
        fields = []
        while not self.peek("}"):
            if self.peek("..."):
                self.take("...")
                if self.peek("name", "on"):
                    self.take("name", "on")
                    on_type = self.take("name")
                    if self.peek("@"):
                        self.skip_directives()
                    fields.append({"inline_on": on_type,
                                   "selection": self.selection()})
                else:
                    fields.append({"spread": self.take("name")})
                continue
            first = self.take("name")
            alias = None
            name = first
            if self.peek(":"):
                self.take(":")
                alias = first
                name = self.take("name")
            args = {}
            if self.peek("("):
                self.take("(")
                while not self.peek(")"):
                    arg_name = self.take("name")
                    self.take(":")
                    args[arg_name] = self.value()
                self.take(")")
            if self.peek("@"):
                self.skip_directives()
            sub = self.selection() if self.peek("{") else None
            fields.append({"name": name, "alias": alias, "args": args,
                           "selection": sub})
        self.take("}")
        return fields

    def value(self):
        if self.peek("$"):
            self.take("$")
            return ("var", self.take("name"))
        if self.peek("string"):
            return self.take("string")
        if self.peek("int"):
            return self.take("int")
        if self.peek("["):
            self.take("[")
            items = []
            while not self.peek("]"):
                items.append(self.value())
            self.take("]")
            return items
        if self.peek("{"):
            self.take("{")
            mapping = {}
            while not self.peek("}"):
                key = self.take("name")
                self.take(":")
                mapping[key] = self.value()
            self.take("}")
            return mapping
        return GqlEnum(self.take("name"))


def bind_value(value, variables):
    if isinstance(value, tuple) and len(value) == 2 and value[0] == "var":
        return variables.get(value[1])
    if isinstance(value, list):
        return [bind_value(item, variables) for item in value]
    if isinstance(value, dict):
        return {key: bind_value(item, variables)
                for key, item in value.items()}
    return value


def viewer_obj(repo=None):
    if repo is not None:
        login = getattr(repo, "owner", VIEWER)
    else:
        login = VIEWER
    if login == VIEWER:
        return GqlObj("User", {"login": VIEWER["login"], "id": 1000,
                               "name": VIEWER["name"], "email": VIEWER["email"]})
    return GqlObj("User", {"login": login, "id": 1000,
                           "name": login, "email": ""})


def repo_gql(repo):
    return GqlObj("Repository", repo)


def issue_gql(repo, issue):
    return GqlObj("Issue", {"repo": repo, "issue": issue})


def pull_gql(repo, pull):
    return GqlObj("PullRequest", {"repo": repo, "pull": pull})


def comment_gql(comment):
    return GqlObj("IssueComment", comment)


def cursor_of(issue):
    return base64.b64encode(("cursor:" + str(issue.get("seq", 0))).encode()).decode()


def seq_after(after):
    if not after:
        return None
    try:
        raw = base64.b64decode(after, validate=True).decode()
        return int(raw.split(":", 1)[1])
    except Exception:
        return None


def connection_of(type_name, items, first, after=None):
    limit = 30 if first is None else max(0, int(first))
    seq = seq_after(after)
    if seq is not None:
        for index, item in enumerate(items):
            if item.get("seq") == seq:
                items = items[index + 1:]
                break
    page = items[:limit]
    cursors = [cursor_of(item) for item in page]
    info = {
        "hasNextPage": len(items) > len(page),
        "hasPreviousPage": False,
        "startCursor": cursors[0] if cursors else None,
        "endCursor": cursors[-1] if cursors else None,
    }
    return GqlObj(type_name, {"items": page, "page": info})


def _query_field(name, args, ctx):
    if name == "viewer":
        return viewer_obj()
    if name == "repository":
        repo = find_repo(args.get("owner"), args.get("name"))
        return repo_gql(repo) if repo else None
    if name == "node":
        parsed = split_global_id(args.get("id"))
        if not parsed:
            return None
        kind, ident = parsed
        if kind == "Repository":
            repo = repo_for_id(ident)
            return repo_gql(repo) if repo else None
        if kind == "Issue":
            found = issue_for_id(ident)
            return issue_gql(*found) if found else None
        if kind == "PullRequest":
            found = pull_for_id(ident)
            return pull_gql(*found) if found else None
        return None
    if name == "search":
        return GqlObj("SearchResultItemConnection",
                      {"items": [], "edges": [], "page": {}, "issueCount": 0})
    if name == "__type":
        kind = args.get("name")
        if kind not in FIELDS_OF_TYPE and kind not in ENUM_VALUES:
            return None
        return GqlObj("__Type", {
            "name": kind,
            "kind": "ENUM" if kind in ENUM_VALUES else "OBJECT",
            "fields_list": list(FIELDS_OF_TYPE.get(kind, {})),
            "enum_values": ENUM_VALUES.get(kind),
        })
    if name == "__schema":
        names = list(FIELDS_OF_TYPE) + list(ENUM_VALUES)
        return GqlObj("__Schema", {
            "types": [{"name": x} for x in names],
            "queryType": {"name": "Query"},
            "mutationType": {"name": "Mutation"},
        })
    return None


def _mutation_field(name, args, ctx):
    inp = args.get("input") or {}
    if name == "createIssue":
        parsed = split_global_id(inp.get("repositoryId"))
        repo = repo_for_id(parsed[1]) if parsed and parsed[0] == "Repository" else None
        if not repo:
            ctx["errors"].append("Repository not found")
            return None
        issue, status, msg = create_issue(repo, inp.get("title", ""),
                                          inp.get("body", "") or "", [])
        if issue is None:
            ctx["errors"].append(msg or "Unable to create issue")
            return None
        return GqlObj("CreateIssuePayload", {
            "issue": issue_gql(repo, issue),
            "clientMutationId": inp.get("clientMutationId"),
        })
    if name == "closeIssue":
        parsed = split_global_id(inp.get("issueId"))
        found = issue_for_id(parsed[1]) if parsed and parsed[0] == "Issue" else None
        if not found:
            ctx["errors"].append("Issue not found")
            return None
        repo, issue = found
        issue["state"] = "closed"
        return GqlObj("CloseIssuePayload", {
            "issue": issue_gql(repo, issue),
            "clientMutationId": inp.get("clientMutationId"),
        })
    if name == "createPullRequest":
        parsed = split_global_id(inp.get("repositoryId"))
        repo = repo_for_id(parsed[1]) if parsed and parsed[0] == "Repository" else None
        if not repo:
            ctx["errors"].append("Repository not found")
            return None
        pull, status, msg = create_pull(repo, inp.get("title", ""),
                                        inp.get("body", "") or "",
                                        inp.get("headRefName"),
                                        inp.get("baseRefName"))
        if pull is None:
            ctx["errors"].append(msg or "Unable to create pull request")
            return None
        return GqlObj("CreatePullRequestPayload", {
            "pullRequest": pull_gql(repo, pull),
            "clientMutationId": inp.get("clientMutationId"),
        })
    if name == "mergePullRequest":
        parsed = split_global_id(inp.get("pullRequestId"))
        found = pull_for_id(parsed[1]) if parsed and parsed[0] == "PullRequest" else None
        if not found:
            ctx["errors"].append("Pull request not found")
            return None
        repo, pull = found
        method = str(inp.get("mergeMethod") or "SQUASH").lower()
        sha, status, msg = merge_pull(repo, pull, method)
        if status:
            ctx["errors"].append(msg or "Unable to merge pull request")
        return GqlObj("MergePullRequestPayload", {
            "pullRequest": pull_gql(repo, pull),
            "clientMutationId": inp.get("clientMutationId"),
        })
    if name == "addComment":
        parsed = split_global_id(inp.get("subjectId"))
        body = inp.get("body", "")
        stamp = next_stamp()
        comment = {"id": next(_id_counter), "body": body, "ts": stamp,
                   "seq": stamp, "user": {"login": VIEWER["login"]}}
        if parsed and parsed[0] == "Issue":
            found = issue_for_id(parsed[1])
            if not found:
                ctx["errors"].append("Subject not found")
                return None
            repo, issue = found
            issue.setdefault("comments", []).append(comment)
        elif parsed and parsed[0] == "PullRequest":
            found = pull_for_id(parsed[1])
            if not found:
                ctx["errors"].append("Subject not found")
                return None
            repo, pull = found
            pull.setdefault("comments", []).append(comment)
        else:
            ctx["errors"].append("Subject not found")
            return None
        return GqlObj("AddCommentPayload", {
            "commentEdge": GqlObj("CommentEdge", {
                "node": comment_gql(comment),
                "cursor": "Y3Vyc29yOjA=",
            }),
            "clientMutationId": inp.get("clientMutationId"),
        })
    return None


def _repo_field(repo, name, args, ctx):
    if name == "id":
        return global_id("Repository", repo.id)
    if name == "databaseId":
        return repo.id
    if name == "name":
        return repo.name
    if name == "nameWithOwner":
        return repo.owner + "/" + repo.name
    if name == "owner":
        return viewer_obj(repo)
    if name == "defaultBranchRef":
        branch = getattr(repo, "default_branch", "main")
        refs = getattr(repo, "refs", {})
        tip = refs.get("refs/heads/" + branch)
        return GqlObj("Ref", {"name": branch, "tip": tip}) if tip else None
    if name == "viewerPermission":
        return "ADMIN"
    if name == "hasIssuesEnabled":
        return True
    if name == "isPrivate":
        return repo.private
    if name == "description":
        return repo.description
    if name in ("createdAt", "updatedAt"):
        return utc_text(repo.seq)
    if name == "url":
        return ""
    if name == "issue":
        for issue in repo.issues:
            if issue.get("number") == args.get("number"):
                return issue_gql(repo, issue)
        return None
    if name == "issues":
        items = list(repo.issues)
        states = args.get("states")
        if states:
            wanted = {str(x).lower() for x in states}
            items = [x for x in items if x.get("state", "open") in wanted]
        order = args.get("orderBy") or {}
        reverse = str(order.get("direction", "ASC")) == "DESC"
        items.sort(key=lambda x: (x.get("seq", 0), x.get("number", 0)),
                   reverse=reverse)
        return connection_of("IssueConnection", items, args.get("first"),
                             args.get("after"))
    if name == "pullRequest":
        for pull in repo.pulls:
            if pull.get("number") == args.get("number"):
                return pull_gql(repo, pull)
        return None
    if name == "pullRequests":
        items = list(repo.pulls)
        states = args.get("states")
        if states:
            wanted = {str(x) for x in states}
            kept = []
            for p in items:
                state = ("MERGED" if p.get("merged") else
                         "CLOSED" if p.get("state") == "closed" else "OPEN")
                if state in wanted:
                    kept.append(p)
            items = kept
        items.sort(key=lambda x: x.get("number", 0))
        return connection_of("PullRequestConnection", items, args.get("first"),
                             args.get("after"))
    return None


def _issue_field(source, name, args, ctx):
    repo, issue = source["repo"], source["issue"]
    if name == "id":
        return global_id("Issue", issue["id"])
    if name == "databaseId":
        return issue["id"]
    if name in ("number", "title", "body"):
        return issue.get(name)
    if name == "state":
        return "CLOSED" if issue.get("state") == "closed" else "OPEN"
    if name == "author":
        return viewer_obj(repo)
    if name == "labels":
        items = [{"name": x, "color": ""} for x in issue.get("labels", [])]
        return GqlObj("LabelConnection", {"items": items})
    if name == "comments":
        items = [comment_gql(x) for x in issue.get("comments", [])]
        return GqlObj("CommentConnection", {"items": items})
    if name in ("createdAt", "updatedAt"):
        return utc_text(issue.get("ts"))
    if name == "closed":
        return issue.get("state") == "closed"
    if name == "repository":
        return repo_gql(repo)
    if name == "url":
        return ""
    return None


def _pull_field(source, name, args, ctx):
    repo, pull = source["repo"], source["pull"]
    if name == "id":
        return global_id("PullRequest", pull["id"])
    if name == "databaseId":
        return pull["id"]
    if name in ("number", "title", "body"):
        return pull.get(name)
    if name == "state":
        if pull.get("merged"):
            return "MERGED"
        return "CLOSED" if pull.get("state") == "closed" else "OPEN"
    if name == "merged":
        return bool(pull.get("merged"))
    if name == "mergeable":
        return "MERGEABLE" if pull.get("state") == "open" else "UNKNOWN"
    if name == "headRefName":
        return pull.get("head_ref")
    if name == "baseRefName":
        return pull.get("base_ref")
    if name in ("headRefOid", "baseRefOid"):
        ref = pull.get("head_ref" if name == "headRefOid" else "base_ref")
        return getattr(repo, "refs", {}).get("refs/heads/" + str(ref), ZERO)
    if name == "files":
        files = [{"path": x.get("filename", "")}
                 for x in changed_files(repo, pull)]
        return GqlObj("PullRequestFilesConnection", {"items": files})
    if name == "author":
        return viewer_obj(repo)
    if name in ("createdAt", "updatedAt"):
        return utc_text(pull.get("ts"))
    if name == "mergedAt":
        return utc_text(pull.get("merged_at")) if pull.get("merged_at") else None
    if name == "repository":
        return repo_gql(repo)
    if name == "comments":
        items = [comment_gql(x) for x in pull.get("comments", [])]
        return GqlObj("CommentConnection", {"items": items})
    if name == "url":
        return ""
    return None


def field_value(type_name, source, name, args, ctx):
    if type_name == "Query":
        return _query_field(name, args, ctx)
    if type_name == "Mutation":
        return _mutation_field(name, args, ctx)
    if type_name == "User":
        if name == "id":
            return global_id("User", source.get("id", 1000))
        return source.get(name)
    if type_name == "Repository":
        return _repo_field(source, name, args, ctx)
    if type_name == "Ref":
        if name == "name":
            return source.get("name")
        if name == "target":
            return GqlObj("Commit", {"oid": source.get("tip"), "message": ""})
        return None
    if type_name == "Commit":
        return source.get(name)
    if type_name == "Issue":
        return _issue_field(source, name, args, ctx)
    if type_name == "PullRequest":
        return _pull_field(source, name, args, ctx)
    if type_name == "IssueComment":
        if name == "id":
            return global_id("IssueComment", source["id"])
        if name == "author":
            return viewer_obj()
        if name == "createdAt":
            return utc_text(source.get("ts", 0))
        return source.get(name)
    if type_name in ("LabelConnection", "CommentConnection",
                     "PullRequestFilesConnection"):
        if name == "nodes":
            items = source.get("items", [])
            first = args.get("first")
            if first is not None:
                items = items[:int(first)]
            return items
        if name == "totalCount":
            return len(source.get("items", []))
        return None
    if type_name in ("IssueConnection", "PullRequestConnection"):
        items = source.get("items", [])
        if name == "nodes":
            out = []
            for item in items:
                if type_name == "IssueConnection":
                    out.append(issue_gql(source.get("repo"), item))
                else:
                    out.append(pull_gql(source.get("repo"), item))
            return out
        if name == "edges":
            return [GqlObj("IssueEdge", {
                "node": issue_gql(source.get("repo"), item),
                "cursor": cursor_of(item),
            }) for item in items]
        if name == "pageInfo":
            return GqlObj("PageInfo", source.get("page", {}))
        if name == "totalCount":
            return len(items)
        return None
    if type_name == "PageInfo":
        return source.get(name)
    if type_name in ("PullRequestFile", "PullRequestChangedFile"):
        return source.get(name)
    if type_name in ("CreateIssuePayload", "CloseIssuePayload",
                     "CreatePullRequestPayload", "MergePullRequestPayload",
                     "AddCommentPayload"):
        return source.get(name)
    if type_name == "CommentEdge":
        return source.get(name)
    if type_name == "SearchResultItemConnection":
        if name == "nodes":
            return []
        if name == "edges":
            return []
        if name == "issueCount":
            return 0
        if name == "pageInfo":
            return GqlObj("PageInfo", {})
        return None
    if type_name == "__Type":
        if name in ("name", "kind", "description"):
            return source.get(name)
        if name == "fields":
            return [GqlObj("__Field", {"name": x})
                    for x in source.get("fields_list") or []]
        if name == "enumValues":
            return [GqlObj("__EnumValue", {"name": x})
                    for x in source.get("enum_values") or []]
        return None
    if type_name == "__Field":
        return source.get(name)
    if type_name == "__EnumValue":
        return source.get(name)
    if type_name == "__Schema":
        return source.get(name)
    return None


def shape_value(value, selection, ctx, runtime_type=None):
    if value is None:
        return None
    if isinstance(value, GqlObj):
        return shape_fields(value.type_name, value.data, selection or [], ctx)
    if isinstance(value, list):
        return [shape_value(item, selection, ctx) for item in value]
    if isinstance(value, dict):
        return value
    return value


def shape_fields(type_name, source, fields, ctx):
    out = {}
    expanded = []
    for field in fields:
        if "spread" in field:
            expanded.extend(ctx["fragments"].get(field["spread"], []))
        elif "inline_on" in field:
            if field["inline_on"] == type_name:
                expanded.extend(field["selection"])
        else:
            expanded.append(field)
    for field in expanded:
        name = field["name"]
        key = field.get("alias") or name
        if name not in FIELDS_OF_TYPE.get(type_name, {}):
            ctx["errors"].append(
                "Field '" + name + "' is undefined on type '" + type_name + "'")
            out[key] = None
            continue
        bound = {k: bind_value(v, ctx["variables"])
                 for k, v in field.get("args", {}).items()}
        value = field_value(type_name, source, name, bound, ctx)
        out[key] = shape_value(value, field.get("selection"), ctx)
    return out


def run_document(document, variables=None, operation_name=None):
    parser = DocumentParser(document)
    operations, fragments = parser.parse()
    chosen = operations
    if operation_name is not None:
        chosen = [x for x in operations if x["name"] == operation_name]
        if not chosen:
            raise ValueError("Unknown operation named '" + str(operation_name) + "'")
    results = []
    for operation in chosen:
        ctx = {"variables": variables or {}, "errors": [], "fragments": fragments}
        root_type = "Mutation" if operation["kind"] == "mutation" else "Query"
        root = shape_fields(root_type, None, operation["selection"], ctx)
        result = {"data": root}
        if ctx["errors"]:
            result["errors"] = [{"message": x} for x in ctx["errors"]]
        results.append(result)
    if len(results) == 1:
        return results[0]
    return results


def route_graphql(body_bytes, authed):
    headers = {"content-type": "application/json; charset=utf-8"}
    if not authed:
        return 401, headers, json.dumps({"message": "Bad credentials"}).encode()
    try:
        body = json.loads(body_bytes)
    except Exception:
        return 400, headers, json.dumps(
            {"errors": [{"message": "Invalid JSON"}]}).encode()

    def one(item):
        try:
            return run_document(item["query"], item.get("variables") or {},
                                item.get("operationName"))
        except Exception as exc:
            return {"data": None, "errors": [{"message": str(exc)}]}

    if isinstance(body, list):
        return reply_json(200, [one(x) for x in body])
    if isinstance(body, dict) and isinstance(body.get("operations"), list):
        return reply_json(200, [one(x) for x in body["operations"]])
    if isinstance(body, dict):
        return reply_json(200, one(body))
    return reply_json(400, {"errors": [{"message": "Invalid request"}]})


# ---------------------------------------------------------------------------
# MCP: a small tool surface over the same service layer.
# ---------------------------------------------------------------------------

def _prop(kind, description):
    return {"type": kind, "description": description}


def _tool_def(name, description, properties, required):
    schema = {"type": "object", "properties": properties, "required": required}
    return {"name": name, "description": description, "inputSchema": schema}


TOOL_DEFS = [
    _tool_def("create_repo", "Create a new repository", {
        "name": _prop("string", "Repository name"),
        "description": _prop("string", "Repository description"),
        "private": _prop("boolean", "Whether the repository is private"),
    }, ["name"]),
    _tool_def("get_repo", "Get a repository", {
        "owner": _prop("string", "Repository owner"),
        "repo": _prop("string", "Repository name"),
    }, ["owner", "repo"]),
    _tool_def("create_issue", "Create an issue", {
        "owner": _prop("string", "Repository owner"),
        "repo": _prop("string", "Repository name"),
        "title": _prop("string", "Issue title"),
        "body": _prop("string", "Issue body"),
    }, ["owner", "repo", "title"]),
    _tool_def("list_issues", "List repository issues", {
        "owner": _prop("string", "Repository owner"),
        "repo": _prop("string", "Repository name"),
        "state": _prop("string", "Issue state: open, closed, all, or any"),
    }, ["owner", "repo"]),
    _tool_def("create_pull_request", "Create a pull request", {
        "owner": _prop("string", "Repository owner"),
        "repo": _prop("string", "Repository name"),
        "title": _prop("string", "Pull request title"),
        "head": _prop("string", "Source branch"),
        "base": _prop("string", "Target branch"),
        "body": _prop("string", "Pull request body"),
    }, ["owner", "repo", "title", "head", "base"]),
    _tool_def("merge_pull_request", "Merge a pull request", {
        "owner": _prop("string", "Repository owner"),
        "repo": _prop("string", "Repository name"),
        "pull_number": _prop("integer", "Pull request number"),
    }, ["owner", "repo", "pull_number"]),
]


class ToolFailure(Exception):
    """A tool call that the caller should hear about as an error."""


def _need_repo(args):
    repo = find_repo(args["owner"], args["repo"])
    if repo is None:
        raise ToolFailure("repository not found")
    return repo


def _tool_create_repo(args):
    repo = create_repo(args["name"], bool(args.get("private", False)),
                       args.get("description", "") or "")
    if repo is None:
        repo = CATALOG.repos[args["name"]]
    return repo_view(repo)


def _tool_get_repo(args):
    return repo_view(_need_repo(args))


def _tool_create_issue(args):
    repo = _need_repo(args)
    labels = args.get("labels") or []
    issue, status, msg = create_issue(repo, args["title"],
                                      args.get("body") or "", labels)
    if issue is None:
        raise ToolFailure(msg)
    return issue_view(repo, issue)


def _tool_list_issues(args):
    repo = _need_repo(args)
    state = args.get("state")
    items = list(repo.issues)
    if state in ("open", "closed"):
        items = [issue for issue in items if issue["state"] == state]
    return {
        "issues": [issue_view(repo, issue) for issue in items],
        "total_count": len(items),
    }


def _tool_create_pull(args):
    repo = _need_repo(args)
    pull, status, msg = create_pull(repo, args["title"], args.get("body") or "",
                                    args["head"], args["base"])
    if pull is None:
        raise ToolFailure(msg)
    return pull_view(repo, pull)


def _tool_merge_pull(args):
    repo = _need_repo(args)
    try:
        number = int(args["pull_number"])
    except (TypeError, ValueError, OverflowError):
        raise ToolFailure("invalid pull request number") from None
    pull = None
    for candidate in repo.pulls:
        if candidate["number"] == number:
            pull = candidate
            break
    if pull is None:
        raise ToolFailure("pull request not found")
    sha, status, msg = merge_pull(repo, pull)
    if status:
        raise ToolFailure(msg)
    return pull_view(repo, pull)


_TOOL_HANDLERS = {
    "create_repo": _tool_create_repo,
    "get_repo": _tool_get_repo,
    "create_issue": _tool_create_issue,
    "list_issues": _tool_list_issues,
    "create_pull_request": _tool_create_pull,
    "merge_pull_request": _tool_merge_pull,
}


def invoke_tool(name, args):
    handler = _TOOL_HANDLERS.get(name)
    if handler is None:
        raise ToolFailure("Unknown tool: " + str(name))
    return handler(args)


PROTOCOL_VERSIONS = [
    "2026-07-28",
    "2025-11-25",
    "2025-06-18",
    "2025-03-26",
    "2024-11-05",
]


def mcp_failure(request_id, code, message):
    return {
        "jsonrpc": "2.0",
        "id": request_id,
        "error": {"code": code, "message": message},
    }


def _mcp_envelope(request_id, result):
    return {"jsonrpc": "2.0", "id": request_id, "result": result}


def _mcp_discover(request_id):
    result = {
        "supportedVersions": PROTOCOL_VERSIONS,
        "capabilities": {"tools": {}},
        "serverInfo": {"name": "forge", "version": "1.0.0"},
        "protocolVersion": "2026-07-28",
    }
    return _mcp_envelope(request_id, result)


def _mcp_initialize(obj, extra_headers):
    request_id = obj.get("id")
    params = obj.get("params") or {}
    if not isinstance(params, dict):
        return mcp_failure(request_id, -32602, "Invalid params")
    want = params.get("protocolVersion")
    chosen = want if want in PROTOCOL_VERSIONS else "2025-11-25"
    extra_headers["Mcp-Session-Id"] = "forge-session-1"
    result = {
        "protocolVersion": chosen,
        "capabilities": {"tools": {}},
        "serverInfo": {"name": "forge", "version": "1.0.0"},
    }
    return _mcp_envelope(request_id, result)


def _mcp_call(obj):
    request_id = obj.get("id")
    params = obj.get("params") or {}
    if not isinstance(params, dict):
        return mcp_failure(request_id, -32602, "Invalid params")
    name = params.get("name")
    tool = None
    for candidate in TOOL_DEFS:
        if candidate["name"] == name:
            tool = candidate
            break
    if tool is None:
        return mcp_failure(request_id, -32602, "Unknown tool: " + str(name))
    args = params.get("arguments", {})
    if not isinstance(args, dict):
        return mcp_failure(request_id, -32602, "Invalid arguments")
    for prop in tool["inputSchema"]["required"]:
        if prop not in args:
            return mcp_failure(request_id, -32602,
                               "Missing required argument: " + prop)
    try:
        value = invoke_tool(name, args)
    except ToolFailure as exc:
        result = {
            "content": [{"type": "text", "text": str(exc)}],
            "isError": True,
        }
    else:
        result = {
            "content": [{"type": "text", "text": json.dumps(value)}],
            "structuredContent": value,
            "isError": False,
        }
    return _mcp_envelope(request_id, result)


def route_mcp(body_bytes, authed, req_headers):
    if not authed:
        return (401, {"content-type": "application/json"},
                json.dumps({"message": "Unauthorized"}).encode())
    try:
        payload = json.loads(body_bytes)
    except (ValueError, UnicodeError):
        return (400, {"content-type": "application/json"},
                json.dumps(mcp_failure(None, -32700, "Parse error")).encode())
    extra_headers = {}

    def dispatch(obj):
        method = obj.get("method")
        request_id = obj.get("id")
        if method == "server/discover":
            return _mcp_discover(request_id)
        if method == "initialize":
            return _mcp_initialize(obj, extra_headers)
        if method == "tools/list":
            return _mcp_envelope(request_id, {"tools": TOOL_DEFS})
        if method == "tools/call":
            return _mcp_call(obj)
        if method == "ping":
            return _mcp_envelope(request_id, {})
        return mcp_failure(request_id, -32601, "Method not found")

    if isinstance(payload, list):
        envelopes = [dispatch(obj) for obj in payload
                     if isinstance(obj, dict) and "id" in obj]
        status, headers, body = reply_json(200, envelopes)
        headers = dict(headers)
        headers.update(extra_headers)
        return status, headers, body
    if not isinstance(payload, dict):
        return (400, {"content-type": "application/json"},
                json.dumps(mcp_failure(None, -32600, "Invalid Request")).encode())
    if "id" not in payload:
        return 200, {}, b""
    envelope = dispatch(payload)
    headers = {"content-type": "application/json"}
    headers.update(extra_headers)
    return 200, headers, json.dumps(envelope).encode()


# ---------------------------------------------------------------------------
# HTTP transport and the competition-env registration loop.
# ---------------------------------------------------------------------------

_request_counter = itertools.count(1)
_BODY_LIMIT = 64 * 1024 * 1024
_get_cache = {}
_epoch = [0]


_HEADER_NAME_CHARS = frozenset(
    b"!#$%&'*+-.^_`|~0123456789"
    b"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ")


class _FastHeaders:
    """Minimal stand-in for http.client.HTTPMessage covering the .get()
    lookups this server performs. First occurrence wins, as with
    HTTPMessage.get, and names match case-insensitively."""

    def __init__(self, pairs):
        self._pairs = pairs

    def get(self, name, default=None):
        wanted = name.lower()
        for key, value in self._pairs:
            if key == wanted:
                return value
        return default

    def __contains__(self, name):
        wanted = name.lower()
        return any(key == wanted for key, _value in self._pairs)


class ForgeHandler(http.server.BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.1"

    def log_message(self, *args):
        pass

    def parse_request(self):
        # Fast path for the one request shape every client of this
        # server sends: a three-word HTTP/1.0 or HTTP/1.1 request line
        # followed by plain "Name: value" header lines. Anything else
        # falls through to the stock parser untouched (the header block
        # has not been read yet at that point); a header block that is
        # not plain is rejected with a 400.
        line = str(self.raw_requestline, "iso-8859-1").rstrip("\r\n")
        words = line.split()
        if len(words) != 3 or words[2] not in ("HTTP/1.1", "HTTP/1.0"):
            return super().parse_request()
        pairs = []
        total = 0
        while True:
            raw = self.rfile.readline(65537)
            if raw in (b"\r\n", b"\n", b""):
                break
            total += len(raw)
            if (len(raw) > 65536 or total > 262144
                    or not raw.endswith(b"\r\n")
                    or raw[:1] in (b" ", b"\t")):
                self.send_error(400, "Bad Request")
                return False
            name, sep, value = raw[:-2].partition(b":")
            if (not sep or not name
                    or any(c not in _HEADER_NAME_CHARS for c in name)):
                self.send_error(400, "Bad Request")
                return False
            pairs.append((name.decode("ascii").lower(),
                          value.decode("iso-8859-1").strip(" \t")))
        self.requestline = line
        self.command = words[0]
        path = words[1]
        if path.startswith("//"):
            path = "/" + path.lstrip("/")
        self.path = path
        self.request_version = words[2]
        self.headers = _FastHeaders(pairs)
        self.close_connection = words[2] == "HTTP/1.0"
        connection = self.headers.get("Connection", "")
        if connection.lower() == "close":
            self.close_connection = True
        elif connection.lower() == "keep-alive" and words[2] == "HTTP/1.0":
            self.close_connection = False
        if (words[2] == "HTTP/1.1"
                and self.headers.get("Expect", "").lower() == "100-continue"):
            if not self.handle_expect_100():
                return False
        return True

    def setup(self):
        super().setup()
        try:
            self.connection.setsockopt(socket.IPPROTO_TCP,
                                       socket.TCP_NODELAY, 1)
        except OSError:
            pass

    def _read_exact(self, size):
        chunks = []
        remaining = size
        while remaining:
            chunk = self.rfile.read(remaining)
            if not chunk:
                raise ValueError("incomplete request body")
            chunks.append(chunk)
            remaining -= len(chunk)
        return b"".join(chunks)

    def _read_chunked(self):
        chunks = []
        total = 0
        while True:
            line = self.rfile.readline(65537)
            if len(line) > 65536 or not line.endswith(b"\r\n"):
                raise ValueError("invalid chunk header")
            size = int(line[:-2].split(b";", 1)[0].strip(), 16)
            if size < 0 or total + size > _BODY_LIMIT:
                raise ValueError("request body too large")
            if size == 0:
                trailer_size = 0
                while True:
                    trailer = self.rfile.readline(65537)
                    trailer_size += len(trailer)
                    if trailer_size > 65536 or not trailer.endswith(b"\r\n"):
                        raise ValueError("invalid chunk trailer")
                    if trailer == b"\r\n":
                        return b"".join(chunks)
            chunks.append(self._read_exact(size))
            total += size
            if self._read_exact(2) != b"\r\n":
                raise ValueError("invalid chunk terminator")

    def _read_body(self):
        transfer = self.headers.get("Transfer-Encoding", "")
        encodings = [part.strip().lower() for part in transfer.split(",")]
        if "chunked" in encodings:
            return self._read_chunked()
        length = int(self.headers.get("Content-Length", "0"))
        if length < 0 or length > _BODY_LIMIT:
            raise ValueError("invalid request body length")
        return self._read_exact(length)

    def _send(self, status, headers, body):
        if status == 204:
            body = b""
        self.send_response(status)
        self.send_header("x-github-request-id",
                         "req-" + str(next(_request_counter)))
        content_type = None
        for key, value in headers.items():
            if key.lower() == "content-type":
                content_type = value
        if content_type is not None:
            self.send_header("content-type", content_type)
        elif body:
            self.send_header("content-type", "application/json; charset=utf-8")
        self.send_header("content-length", str(len(body)))
        skip = {"content-type", "content-length", "x-github-request-id"}
        for key, value in headers.items():
            if key.lower() not in skip:
                self.send_header(key, value)
        self.end_headers()
        if self.command != "HEAD" and body:
            self.wfile.write(body)

    def _authed(self):
        if TOKEN == "":
            return True
        return self.headers.get("Authorization") == "Bearer " + TOKEN

    def _handle(self, method):
        if method != "GET":
            _epoch[0] += 1
        try:
            self._route(method)
        except Exception:
            self.close_connection = True
            try:
                self._send(*reply_error(500, "Internal Server Error"))
            except Exception:
                pass

    def _route(self, method):
        url = urllib.parse.urlsplit(self.path)
        path = url.path
        query = urllib.parse.parse_qs(url.query)
        body = self._read_body()
        api_method = "GET" if method == "HEAD" else method

        if api_method == "GET" and path == "/healthz":
            self._send(*reply_json(200, {"ok": True}))
            return

        if path == "/api/v3" or path.startswith("/api/v3/"):
            seg = [urllib.parse.unquote(part)
                   for part in path[len("/api/v3"):].split("/")
                   if part != ""]
            if api_method == "GET" and not query:
                key = (self._authed(), self.headers.get("Host", ""),
                       tuple(seg))
                entry = _get_cache.get(key)
                if entry is not None and entry[0] == _epoch[0]:
                    self._send(*entry[1])
                    return
                result = route_rest(api_method, seg, query, body,
                                    self._authed(),
                                    self.headers.get("Host", ""))
                if result[0] == 200:
                    if len(_get_cache) > 512:
                        _get_cache.clear()
                    _get_cache[key] = (_epoch[0], result)
                self._send(*result)
                return
            self._send(*route_rest(api_method, seg, query, body,
                                   self._authed(),
                                   self.headers.get("Host", "")))
            return

        if path == "/api/graphql":
            if api_method == "POST":
                self._send(*route_graphql(body, self._authed()))
            else:
                self._send(*reply_error(404, "Not Found"))
            return

        if path == "/mcp":
            if method == "POST":
                self._send(*route_mcp(body, self._authed(), self.headers))
            else:
                self._send(405, {"content-type": "application/json"},
                           json.dumps(mcp_failure(
                               None, -32601, "Method not found")).encode())
            return

        if self._route_git(method, path, query, body):
            return

        self._send(*reply_error(404, "Not Found"))

    def _route_git(self, method, path, query, body):
        match = re.fullmatch(r"/([^/]+)/([^/]+)\.git(?:/(.*))?", path)
        if not match:
            return False
        owner, name, tail = match.groups()
        if not tail:
            self._send(*reply_error(404, "Not Found"))
            return True
        service = None
        if tail == "info/refs" and method == "GET":
            service = query.get("service", [None])[0]
            valid = service in ("git-upload-pack", "git-receive-pack")
        else:
            valid = method == "POST" and tail in ("git-upload-pack",
                                                  "git-receive-pack")
        if not valid:
            self._send(*reply_error(404, "Not Found"))
            return True
        if not self._authed():
            self._send(*reply_error(401, "Requires authentication"))
            return True
        repo = find_repo(urllib.parse.unquote(owner),
                         urllib.parse.unquote(name))
        if repo is None:
            self._send(*reply_error(404, "Not Found"))
            return True
        version2 = "version=2" in (self.headers.get("Git-Protocol") or "")
        if tail == "info/refs":
            status, content_type, payload = advertise(repo, service, version2)
        elif tail == "git-upload-pack":
            status, content_type, payload = upload_pack(repo, body, version2)
        else:
            status, content_type, payload = receive_pack(repo, body)
        self._send(status, {"content-type": content_type}, payload)
        return True

    def do_GET(self):
        self._handle("GET")

    def do_POST(self):
        self._handle("POST")

    def do_PUT(self):
        self._handle("PUT")

    def do_PATCH(self):
        self._handle("PATCH")

    def do_DELETE(self):
        self._handle("DELETE")

    def do_HEAD(self):
        self._handle("HEAD")


class ForgeServer(http.server.ThreadingHTTPServer):
    daemon_threads = True
    request_queue_size = 128
    allow_reuse_address = True


def _announce(env_url, port):
    payload = json.dumps({"port": port}).encode()
    request = urllib.request.Request(
        env_url + "/register",
        data=payload,
        headers={"Content-Type": "application/json"},
        method="POST",
    )
    try:
        with urllib.request.urlopen(request, timeout=30) as response:
            return response.status in (200, 409)
    except urllib.error.HTTPError as exc:
        outcome = exc.code == 409
        exc.close()
        return outcome
    except Exception:
        return False


def _register_until_accepted(env_url, port):
    delay = 0.25
    while not _announce(env_url, port):
        time.sleep(delay)
        delay = min(delay * 2, 2.0)


def _wait_until_done(env_url):
    delay = 0.35
    while True:
        try:
            request = urllib.request.Request(env_url + "/done", method="GET")
            with urllib.request.urlopen(request, timeout=30) as response:
                result = json.load(response)
            if isinstance(result, dict) and result.get("done") is True:
                return
            delay = 0.35
        except Exception:
            time.sleep(delay)
            delay = min(delay * 2, 2.0)
            continue
        time.sleep(delay)


def main():
    env_url = os.environ.get("MAKEFUN_ENV_URL", "").rstrip("/")
    if env_url == "":
        sys.stderr.write("MAKEFUN_ENV_URL must be set\n")
        return 1
    server = ForgeServer(("0.0.0.0", 0), ForgeHandler)
    port = server.server_address[1]
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    try:
        _register_until_accepted(env_url, port)
        _wait_until_done(env_url)
    finally:
        server.shutdown()
        server.server_close()
    return 0


if __name__ == "__main__":
    sys.exit(main())
