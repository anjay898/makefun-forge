#!/usr/bin/env python3
"""forge — a standalone GitHub-compatible git forge in one file.

Implements git smart HTTP (upload-pack v0/v2, receive-pack), the REST v3
API subset, GraphQL v4, and an MCP endpoint over one in-memory store.
Standard library only.
"""
import base64
import datetime
import difflib
import itertools
import json
import re
import socket
import sys
import time
import urllib.parse
import urllib.request
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer


def iso_ts(ts):
    return datetime.datetime.fromtimestamp(
        int(ts), datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


import hashlib
import zlib
import threading
import os
import struct

VIEWER = {"login": "adaiversen", "name": "ada iversen", "id": 1000, "email": "adaiversen@example.invalid"}
TOKEN = os.environ.get("MAKEFUN_SHOP_TOKEN", "")
ZERO = "0" * 40
_clock = [1735689600]
_clock_lock = threading.RLock()


def tick() -> int:
    with _clock_lock:
        _clock[0] += 1
        return _clock[0]


class Repo:
    def __init__(self, id=0, name="", owner=None, private=False, description="",
                 default_branch="main"):
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


class Store:
    def __init__(self):
        self.repos = {}
        self.next_repo_id = 1
        self.lock = threading.RLock()


STORE = Store()


def get_repo(owner, name):
    with STORE.lock:
        repo = STORE.repos.get(name)
        return repo if repo is not None and repo.owner == owner else None


def _snapshot(repo):
    with repo.lock:
        result = Repo(repo.id, repo.name, repo.owner, repo.private,
                      repo.description, repo.default_branch)
        result.objects = repo.objects.copy()
        result.refs = repo.refs.copy()
        return result


def _oid_valid(oid):
    return (isinstance(oid, str) and len(oid) == 40
            and all(c in "0123456789abcdef" for c in oid))


def hash_object(typ, data):
    header = typ.encode("ascii") + b" " + str(len(data)).encode("ascii") + b"\0"
    return hashlib.sha1(header + data).hexdigest()


def store_object(repo, typ, data):
    data = bytes(data)
    oid = hash_object(typ, data)
    with repo.lock:
        repo.objects.setdefault(oid, (typ, data))
    return oid


def parse_commit(data: bytes):
    headers, separator, message = data.partition(b"\n\n")
    result = {
        "tree": "", "parents": [], "message": message.decode("utf-8", "replace"),
        "author": "", "committer": "", "timestamp": 0,
    }
    for line in headers.split(b"\n"):
        key, sep, value = line.partition(b" ")
        if not sep:
            continue
        text = value.decode("utf-8", "replace")
        if key == b"tree":
            result["tree"] = text
        elif key == b"parent":
            result["parents"].append(text)
        elif key in (b"author", b"committer"):
            result[key.decode("ascii")] = text
    identity = result["committer"] or result["author"]
    try:
        result["timestamp"] = int(identity.rsplit(" ", 2)[-2])
    except (ValueError, IndexError):
        pass
    return result


def _mode(mode):
    value = int(str(mode), 8)
    if value not in (0o40000, 0o100644, 0o100755, 0o120000, 0o160000):
        raise ValueError("invalid tree mode")
    return format(value, "o")


def parse_tree(data):
    entries = []
    pos = 0
    while pos < len(data):
        space = data.find(b" ", pos)
        end = data.find(b"\0", space + 1) if space >= 0 else -1
        if space <= pos or end < 0 or end + 21 > len(data):
            raise ValueError("invalid tree")
        mode = _mode(data[pos:space].decode("ascii"))
        name = data[space + 1:end].decode("utf-8", "surrogateescape")
        if not name or "/" in name:
            raise ValueError("invalid tree name")
        entries.append((mode, name, data[end + 1:end + 21].hex()))
        pos = end + 21
    return entries


def build_tree(entries):
    normalized = []
    names = set()
    for mode, name, oid in entries:
        mode = _mode(mode)
        raw_name = name.encode("utf-8", "surrogateescape")
        if not raw_name or b"/" in raw_name or b"\0" in raw_name or name in names:
            raise ValueError("invalid or duplicate tree name")
        if not _oid_valid(oid):
            raise ValueError("invalid object id")
        names.add(name)
        normalized.append((mode, raw_name, oid))
    normalized.sort(key=lambda e: e[1] + (b"/" if e[0] == "40000" else b""))
    return b"".join(mode.encode("ascii") + b" " + name + b"\0" + bytes.fromhex(oid)
                    for mode, name, oid in normalized)


def flatten_tree(repo, tree_oid, prefix=""):
    with repo.lock:
        objects = repo.objects.copy()
    result = {}

    def visit(oid, base, active):
        if oid in active:
            raise ValueError("tree cycle")
        obj = objects.get(oid)
        if obj is None:
            return
        if obj[0] != "tree":
            raise ValueError("expected tree")
        active.add(oid)
        for mode, name, child in parse_tree(obj[1]):
            path = base + name
            if mode == "40000":
                visit(child, path + "/", active)
            else:
                result[path] = (mode, child)
        active.remove(oid)

    visit(tree_oid, prefix, set())
    return result


def tree_from_flat(repo, flat):
    root = {}
    for path, entry in flat.items():
        parts = path.split("/")
        if any(p in ("", ".", "..") or "\0" in p for p in parts):
            raise ValueError("invalid path")
        node = root
        for part in parts[:-1]:
            child = node.setdefault(part, {})
            if not isinstance(child, dict):
                raise ValueError("file/directory conflict")
            node = child
        if parts[-1] in node:
            raise ValueError("file/directory conflict")
        node[parts[-1]] = entry

    def build(node):
        entries = []
        for name, value in node.items():
            if isinstance(value, dict):
                entries.append(("40000", name, build(value)))
            else:
                mode, oid = value
                entries.append((mode, name, oid))
        return store_object(repo, "tree", build_tree(entries))

    with repo.lock:
        return build(root)


def _ancestors(objects, tip):
    seen = set()
    pending = [tip]
    while pending:
        oid = pending.pop()
        obj = objects.get(oid)
        if oid in seen or obj is None or obj[0] != "commit":
            continue
        seen.add(oid)
        pending.extend(parse_commit(obj[1])["parents"])
    return seen


def commit_ancestors(repo, tip):
    with repo.lock:
        objects = repo.objects.copy()
    return _ancestors(objects, tip)


def _tag_target(data):
    for line in data.split(b"\n"):
        if not line:
            break
        if line.startswith(b"object "):
            oid = line[7:].decode("ascii")
            if not _oid_valid(oid):
                raise ValueError("invalid tag target")
            return oid
    raise ValueError("missing tag target")


def _walk(objects, tips, exclude=frozenset(), stop_commits=frozenset()):
    seen = set()
    pending = list(tips)
    while pending:
        oid = pending.pop()
        if oid in seen or oid in exclude:
            continue
        obj = objects.get(oid)
        if obj is None:
            continue
        seen.add(oid)
        typ, data = obj
        if typ == "commit":
            commit = parse_commit(data)
            pending.append(commit["tree"])
            if oid not in stop_commits:
                pending.extend(commit["parents"])
        elif typ == "tree":
            pending.extend(child for mode, name, child in parse_tree(data)
                           if mode != "160000")
        elif typ == "tag":
            pending.append(_tag_target(data))
    return seen


def reachable_objects(repo, tips, exclude=frozenset()):
    with repo.lock:
        objects = repo.objects.copy()
    return _walk(objects, tips, exclude=exclude)


def closure(repo, tips, stop_commits=frozenset()):
    with repo.lock:
        objects = repo.objects.copy()
    return _walk(objects, tips, stop_commits=stop_commits)


def make_commit(repo, parents, tree_oid, message, author=None):
    identity = author if author is not None else f"{VIEWER['name']} <{VIEWER['email']}>"
    with repo.lock:
        timestamp = tick()
        lines = [f"tree {tree_oid}"]
        lines.extend(f"parent {parent}" for parent in parents)
        lines.extend((f"author {identity} {timestamp} +0000",
                      f"committer {identity} {timestamp} +0000"))
        data = ("\n".join(lines) + "\n\n" + message).encode("utf-8")
        return store_object(repo, "commit", data)


_PACK_TYPES = {1: "commit", 2: "tree", 3: "blob", 4: "tag"}
_PACK_CODES = {value: key for key, value in _PACK_TYPES.items()}


def write_pack(objs):
    result = bytearray(struct.pack(">4sII", b"PACK", 2, len(objs)))
    for oid, typ, data in objs:
        if typ not in _PACK_CODES:
            raise ValueError("invalid pack object type")
        size = len(data)
        first = (_PACK_CODES[typ] << 4) | (size & 15)
        size >>= 4
        result.append(first | (128 if size else 0))
        while size:
            byte = size & 127
            size >>= 7
            result.append(byte | (128 if size else 0))
        result.extend(zlib.compress(data))
    result.extend(hashlib.sha1(result).digest())
    return bytes(result)


def apply_delta(base: bytes, delta: bytes):
    pos = 0

    def varint():
        nonlocal pos
        value = 0
        shift = 0
        while True:
            if pos >= len(delta) or shift > 63:
                raise ValueError("invalid delta length")
            byte = delta[pos]
            pos += 1
            value |= (byte & 127) << shift
            if not byte & 128:
                return value
            shift += 7

    base_size = varint()
    target_size = varint()
    if base_size != len(base):
        raise ValueError("delta base size mismatch")
    result = bytearray()
    while pos < len(delta):
        opcode = delta[pos]
        pos += 1
        if opcode & 128:
            offset = 0
            size = 0
            for bit in range(7):
                if opcode & (1 << bit):
                    if pos >= len(delta):
                        raise ValueError("truncated delta copy")
                    if bit < 4:
                        offset |= delta[pos] << (8 * bit)
                    else:
                        size |= delta[pos] << (8 * (bit - 4))
                    pos += 1
            size = size or 0x10000
            if offset + size > len(base) or len(result) + size > target_size:
                raise ValueError("delta copy out of bounds")
            result.extend(base[offset:offset + size])
        elif opcode:
            if pos + opcode > len(delta) or len(result) + opcode > target_size:
                raise ValueError("delta insert out of bounds")
            result.extend(delta[pos:pos + opcode])
            pos += opcode
        else:
            raise ValueError("invalid delta opcode")
    if len(result) != target_size:
        raise ValueError("delta result size mismatch")
    return bytes(result)


def read_pack(data: bytes, lookup):
    try:
        return _read_pack(data, lookup)
    except ValueError:
        raise
    except Exception as exc:
        raise ValueError("corrupt pack") from exc


def _read_pack(data, lookup):
    if len(data) < 32 or data[:4] != b"PACK":
        raise ValueError("invalid pack header")
    version, count = struct.unpack(">II", data[4:12])
    if version not in (2, 3):
        raise ValueError("unsupported pack version")
    end = len(data) - 20
    if hashlib.sha1(data[:end]).digest() != data[end:]:
        raise ValueError("pack checksum mismatch")
    pos = 12
    entries = {}
    ordered = []

    def byte():
        nonlocal pos
        if pos >= end:
            raise ValueError("truncated pack")
        value = data[pos]
        pos += 1
        return value

    for unused in range(count):
        start = pos
        first = byte()
        kind = (first >> 4) & 7
        size = first & 15
        shift = 4
        current = first
        while current & 128:
            if shift > 63:
                raise ValueError("oversized pack header")
            current = byte()
            size |= (current & 127) << shift
            shift += 7
        base = None
        if kind == 6:
            current = byte()
            offset = current & 127
            while current & 128:
                if offset > len(data):
                    raise ValueError("invalid delta offset")
                current = byte()
                offset = ((offset + 1) << 7) | (current & 127)
            base = start - offset
            if offset <= 0 or base not in entries:
                raise ValueError("missing offset delta base")
        elif kind == 7:
            if pos + 20 > end:
                raise ValueError("truncated reference delta")
            base = data[pos:pos + 20].hex()
            pos += 20
        elif kind not in _PACK_TYPES:
            raise ValueError("invalid pack type")
        inflater = zlib.decompressobj()
        raw = inflater.decompress(data[pos:])
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

    resolved = {}
    objects = {}
    pending = ordered
    while pending:
        remaining = []
        for start in pending:
            kind, base, raw = entries[start]
            if kind in _PACK_TYPES:
                obj = (_PACK_TYPES[kind], raw)
            else:
                base_obj = resolved.get(base) if kind == 6 else objects.get(base)
                if base_obj is None and kind == 7:
                    try:
                        base_obj = lookup(base)
                    except KeyError:
                        base_obj = None
                    if base_obj is not None:
                        base_type, base_data = base_obj
                        if base_type not in _PACK_CODES or hash_object(base_type, base_data) != base:
                            raise ValueError("invalid external delta base")
                if base_obj is None:
                    remaining.append(start)
                    continue
                obj = (base_obj[0], apply_delta(base_obj[1], raw))
            oid = hash_object(obj[0], obj[1])
            resolved[start] = obj
            objects[oid] = obj
        if len(remaining) == len(pending):
            raise ValueError("unresolved or cyclic delta bases")
        pending = remaining
    return objects


FLUSH = b"0000"
DELIM = b"0001"


def pkt(payload: bytes):
    length = len(payload) + 4
    if length > 65520:
        raise ValueError("pkt-line too long")
    return f"{length:04x}".encode("ascii") + payload


def parse_pkt_lines(data: bytes, pos=0):
    if pos < 0 or pos > len(data):
        raise ValueError("invalid pkt-line position")
    lines = []
    while pos < len(data):
        if pos + 4 > len(data):
            raise ValueError("truncated pkt-line header")
        header = data[pos:pos + 4]
        if any(c not in b"0123456789abcdefABCDEF" for c in header):
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


_NOT_FOUND = (404, "application/json", b'{"message":"Not Found"}')


def _peel(objects, oid):
    seen = set()
    while oid in objects and objects[oid][0] == "tag":
        if oid in seen:
            raise ValueError("tag cycle")
        seen.add(oid)
        oid = _tag_target(objects[oid][1])
    return oid


def _wire(text):
    return text.encode("utf-8", "surrogateescape")


def _sideband(data):
    return b"".join(pkt(b"\x01" + data[pos:pos + 32768])
                    for pos in range(0, len(data), 32768))


def git_info_refs(repo, service, version2: bool):
    if repo is None:
        return _NOT_FOUND
    if service not in ("git-upload-pack", "git-receive-pack"):
        return 400, "application/json", b'{"message":"Unsupported service"}'
    content_type = f"application/x-{service}-advertisement"
    repo = _snapshot(repo)
    if service == "git-upload-pack" and version2:
        body = b"".join(pkt(line) for line in (
            b"version 2\n", b"agent=forge/1.0\n", b"ls-refs=unborn\n",
            b"fetch=shallow wait-for-done\n", b"object-format=sha1\n"))
        return 200, content_type, body + FLUSH

    target = "refs/heads/" + repo.default_branch
    symref = "symref=HEAD:" + target
    if service == "git-upload-pack":
        caps = f"side-band-64k thin-pack ofs-delta shallow {symref} agent=forge/1.0"
    else:
        caps = f"report-status side-band-64k delete-refs ofs-delta agent=forge/1.0 {symref}"
    first = (f"{repo.refs.get(target, ZERO)} HEAD" if repo.refs
             else f"{ZERO} capabilities^{{}}")
    body = pkt(_wire("# service=" + service + "\n")) + FLUSH
    body += pkt(_wire(first) + b"\0" + _wire(caps) + b"\n")
    for name, oid in sorted(repo.refs.items()):
        body += pkt(_wire(f"{oid} {name}\n"))
        if name.startswith("refs/tags/") and repo.objects.get(oid, (None,))[0] == "tag":
            body += pkt(_wire(f"{_peel(repo.objects, oid)} {name}^{{}}\n"))
    return 200, content_type, body + FLUSH


def _ls_refs(repo, args):
    flags = set(args)
    prefixes = [arg[11:] for arg in args if arg.startswith("ref-prefix ")]
    target = "refs/heads/" + repo.default_branch
    result = bytearray()
    for name in ["HEAD"] + sorted(repo.refs):
        if prefixes and not any(name.startswith(prefix) for prefix in prefixes):
            continue
        if name == "HEAD":
            oid = repo.refs.get(target)
            if oid is None and "unborn" in flags:
                line = f"unborn HEAD symref-target:{target}"
            else:
                line = f"{oid or ZERO} HEAD"
                if "symrefs" in flags:
                    line += f" symref-target:{target}"
        else:
            oid = repo.refs[name]
            line = f"{oid} {name}"
            if "peel" in flags and repo.objects.get(oid, (None,))[0] == "tag":
                line += f" peeled:{_peel(repo.objects, oid)}"
        result.extend(pkt(_wire(line + "\n")))
    return bytes(result) + FLUSH


def _fetch_args(args):
    wants, haves, shallow = [], [], []
    deepen = None
    done = False
    for arg in args:
        fields = arg.split()
        if not fields:
            continue
        key = fields[0]
        if key in ("want", "have", "shallow"):
            if len(fields) < 2 or not _oid_valid(fields[1]):
                raise ValueError("invalid fetch object id")
            {"want": wants, "have": haves, "shallow": shallow}[key].append(fields[1])
        elif key == "deepen":
            if len(fields) != 2:
                raise ValueError("invalid depth")
            deepen = int(fields[1])
            if deepen < 1:
                raise ValueError("invalid depth")
        elif key == "done":
            done = True
    return wants, haves, shallow, deepen, done


def _depth_selection(objects, wants, depth):
    generations = {}
    tags = set()
    pending = []
    for oid in wants:
        seen = set()
        while oid in objects and objects[oid][0] == "tag":
            if oid in seen:
                raise ValueError("tag cycle")
            seen.add(oid)
            tags.add(oid)
            oid = _tag_target(objects[oid][1])
        pending.append((oid, 1))
    direct = set()
    cursor = 0
    while cursor < len(pending):
        oid, generation = pending[cursor]
        cursor += 1
        obj = objects.get(oid)
        if obj is None:
            continue
        if obj[0] != "commit":
            direct.update(_walk(objects, [oid]))
            continue
        if generation > depth or generations.get(oid, depth + 1) <= generation:
            continue
        generations[oid] = generation
        if generation < depth:
            pending.extend((parent, generation + 1)
                           for parent in parse_commit(obj[1])["parents"])
    commits = set(generations)
    selected = _walk(objects, commits, stop_commits=commits) | direct | tags
    boundary = {
        oid for oid, generation in generations.items()
        if generation == depth
        and any(parent in objects for parent in parse_commit(objects[oid][1])["parents"])
    }
    return selected, commits, boundary


_PACK_CACHE = {}
_PACK_CACHE_LOCK = threading.Lock()


def _pack_for(objects, selected):
    # Pack bytes are a pure function of the selected oid set: object content
    # is immutable (oid = hash of content), so caching is safe.
    key = tuple(selected)
    with _PACK_CACHE_LOCK:
        pack = _PACK_CACHE.get(key)
    if pack is None:
        pack = write_pack([(oid, objects[oid][0], objects[oid][1])
                           for oid in selected])
        with _PACK_CACHE_LOCK:
            if len(_PACK_CACHE) > 128:
                _PACK_CACHE.clear()
            _PACK_CACHE[key] = pack
    return pack


def _fetch(repo, args, version2):
    wants, haves, shallow, deepen, done = _fetch_args(args)
    objects = repo.objects
    have_set = list(dict.fromkeys(h for h in haves if h in objects))
    client_shallow = {oid for oid in shallow
                      if objects.get(oid, (None,))[0] == "commit"}
    shallow_out = set()
    unshallow_out = set()
    if deepen is not None:
        selected, commits, shallow_out = _depth_selection(objects, wants, deepen)
        held = (_walk(objects, have_set, stop_commits=client_shallow)
                if version2 else set())
        selected -= held
        unshallow_out = (client_shallow & commits) - shallow_out
    elif client_shallow:
        selected = (_walk(objects, wants, stop_commits=client_shallow)
                    - _walk(objects, have_set, stop_commits=client_shallow))
        shallow_out = client_shallow
    else:
        held = _walk(objects, have_set)
        selected = _walk(objects, wants, exclude=held)
    if not any(want in objects for want in wants):
        selected = set()
        have_set = []
        shallow_out = set()
        unshallow_out = set()
    order = {"commit": 0, "tree": 1, "blob": 2, "tag": 3}
    selected = [oid for oid in selected if oid in objects]
    selected.sort(key=lambda oid: (order.get(objects[oid][0], 4), oid))
    pack = _pack_for(objects, selected)
    result = bytearray()
    if version2:
        if not done:
            # With `done` the client has finished negotiating; protocol v2
            # then forbids the acknowledgments section entirely.
            result.extend(pkt(b"acknowledgments\n"))
            if have_set:
                for oid in have_set:
                    result.extend(pkt(_wire(f"ACK {oid}\n")))
                result.extend(pkt(b"ready\n"))
            else:
                result.extend(pkt(b"NAK\n"))
            result.extend(DELIM)
        if shallow_out or unshallow_out:
            result.extend(pkt(b"shallow-info\n"))
            for oid in sorted(shallow_out):
                result.extend(pkt(_wire(f"shallow {oid}\n")))
            for oid in sorted(unshallow_out):
                result.extend(pkt(_wire(f"unshallow {oid}\n")))
            result.extend(DELIM)
        result.extend(pkt(b"packfile\n"))
    else:
        if deepen is not None:
            for oid in sorted(shallow_out):
                result.extend(pkt(_wire(f"shallow {oid}\n")))
        result.extend(pkt(b"NAK\n"))
    result.extend(_sideband(pack))
    result.extend(FLUSH)
    return bytes(result)


def git_upload_pack(repo, body: bytes, version2: bool):
    if repo is None:
        return _NOT_FOUND
    content_type = "application/x-git-upload-pack-result"
    repo = _snapshot(repo)
    try:
        lines, pos = parse_pkt_lines(body)
        if version2:
            if not lines or not isinstance(lines[0], bytes):
                raise ValueError("missing command")
            command = lines[0].rstrip(b"\n")
            if "delim" not in lines or not lines or lines[-1] != "flush":
                raise ValueError("invalid version 2 request")
            delim = lines.index("delim")
            args = []
            for line in lines[delim + 1:-1]:
                if not isinstance(line, bytes):
                    raise ValueError("unexpected marker")
                args.append(line.rstrip(b"\n").decode("utf-8", "surrogateescape"))
            if pos != len(body):
                raise ValueError("trailing request data")
            if command == b"command=ls-refs":
                result = _ls_refs(repo, args)
            elif command == b"command=fetch":
                result = _fetch(repo, args, True)
            else:
                raise ValueError("unknown command")
        else:
            args = []
            while True:
                for line in lines:
                    if isinstance(line, bytes):
                        args.append(line.rstrip(b"\n").decode("utf-8", "surrogateescape"))
                    elif line != "flush":
                        raise ValueError("unexpected delimiter")
                if pos == len(body):
                    break
                lines, pos = parse_pkt_lines(body, pos)
            result = _fetch(repo, args, False)
        return 200, content_type, result
    except (ValueError, UnicodeError, TypeError, IndexError, struct.error, zlib.error):
        return 400, content_type, b""


def _receive_report(commands, reasons, unpack, sideband, report_status):
    inner = pkt(_wire("unpack " + unpack + "\n"))
    for command, reason in zip(commands, reasons):
        ref = command[2]
        line = f"ng {ref} {reason}\n" if reason else f"ok {ref}\n"
        inner += pkt(_wire(line))
    inner += FLUSH
    if sideband:
        return _sideband(inner) + FLUSH
    return inner if report_status else b""


def _valid_ref(ref):
    if not ref.startswith("refs/") or ref.endswith(("/", ".")):
        return False
    if any(ord(c) < 32 or ord(c) == 127 or c in " ~^:?*[\\" for c in ref):
        return False
    if ".." in ref or "@{" in ref or "//" in ref:
        return False
    return all(part and not part.startswith(".") and not part.endswith(".lock")
               for part in ref.split("/"))


def git_receive_pack(repo, body):
    if repo is None:
        return _NOT_FOUND
    content_type = "application/x-git-receive-pack-result"
    commands = []
    caps = set()
    try:
        lines, pos = parse_pkt_lines(body)
        if not lines or lines[-1] != "flush":
            raise ValueError("missing command flush")
        for index, line in enumerate(lines[:-1]):
            if not isinstance(line, bytes):
                raise ValueError("invalid command marker")
            line = line.rstrip(b"\n")
            if index == 0:
                line, separator, capability_data = line.partition(b"\0")
                if separator:
                    caps = set(capability_data.decode("ascii").split())
            elif b"\0" in line:
                raise ValueError("unexpected capabilities")
            fields = line.decode("utf-8", "surrogateescape").split(" ")
            if len(fields) != 3:
                raise ValueError("invalid command")
            old, new, ref = fields
            if not _oid_valid(old) or not _oid_valid(new) or not ref:
                raise ValueError("invalid command")
            commands.append((old, new, ref))
    except (ValueError, UnicodeError, TypeError, IndexError):
        return 400, content_type, b""

    sideband = "side-band-64k" in caps
    report_status = "report-status" in caps
    with repo.lock:
        try:
            incoming = read_pack(body[pos:], repo.objects.get) if pos < len(body) else {}
        except ValueError:
            result = _receive_report(commands, ["unpack failed"] * len(commands),
                                     "error", sideband, report_status)
            return 200, content_type, result

        staged = repo.objects.copy()
        staged.update(incoming)
        refs = repo.refs.copy()
        reasons = []
        successes = 0
        for old, new, ref in commands:
            reason = None
            current = refs.get(ref, ZERO)
            if not _valid_ref(ref):
                reason = "invalid ref"
            elif old != current:
                reason = "reference already exists"
            elif new == ZERO:
                if ref not in refs:
                    reason = "reference does not exist"
            elif new not in staged:
                reason = "missing object"
            elif staged[new][0] not in ("commit", "tag"):
                reason = "bad object"
            elif old != ZERO and ref.startswith("refs/tags/") and new != old:
                reason = "already exists"
            elif (old != ZERO and staged.get(old, (None,))[0] == "commit"
                  and staged[new][0] == "commit"):
                try:
                    if old not in _ancestors(staged, new):
                        reason = "non-fast-forward"
                except (ValueError, UnicodeError):
                    reason = "bad object"
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
        result = _receive_report(commands, reasons, "ok", sideband, report_status)
    return 200, content_type, result


import base64
import difflib
import itertools
import json
import re

_ids = itertools.count(1)


def J(status, obj, extra_headers=None):
    headers = {"content-type": "application/json; charset=utf-8"}
    if extra_headers:
        headers.update(extra_headers)
    return status, headers, json.dumps(obj).encode()


def ERR(status, msg):
    return J(status, {"message": msg})


def _repo_tip(repo, branch):
    return repo.refs.get(branch if branch.startswith("refs/") else "refs/heads/" + branch)


def _commit_info(repo, oid):
    if not oid:
        return None
    obj = repo.objects.get(oid)
    if not obj or obj[0] != "commit":
        return None
    try:
        return parse_commit(obj[1])
    except Exception:
        return None


def _commit_parents(repo, oid):
    c = _commit_info(repo, oid)
    if not c:
        return []
    return c.get("parents", [])


def _commit_message(repo, oid):
    c = _commit_info(repo, oid) or {}
    return c.get("message", "")


def _commit_ts(repo, oid):
    c = _commit_info(repo, oid) or {}
    return c.get("ts", c.get("timestamp", c.get("time", repo.seq)))


def _commit_author_name(repo, oid):
    c = _commit_info(repo, oid) or {}
    author = c.get("author", VIEWER.get("name", VIEWER["login"]))
    if isinstance(author, dict):
        return author.get("name", VIEWER.get("name", VIEWER["login"]))
    return str(author)


def _normalize_ref(value):
    value = str(value or "")
    if value.startswith("refs/heads/"):
        value = value[len("refs/heads/"):]
    if ":" in value:
        value = value.split(":", 1)[1]
    return value


def _line_count(data):
    return len(data.decode("utf-8", "replace").splitlines())


def _blob_bytes(repo, oid):
    obj = repo.objects.get(oid)
    if not obj:
        return b""
    typ, data = obj
    if typ in ("blob", "tree"):
        return data if isinstance(data, bytes) else str(data).encode()
    return data if isinstance(data, bytes) else str(data).encode()


def svc_create_repo(name, private=False, description=""):
    if not isinstance(name, str):
        return None
    if not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9._-]*", name) or name.endswith(".git"):
        return None
    if name in STORE.repos:
        return None
    rid = STORE.next_repo_id
    STORE.next_repo_id += 1
    repo = Repo(
        rid,
        name,
        VIEWER["login"],
        bool(private),
        description if isinstance(description, str) else "",
    )
    repo.seq = tick()
    STORE.repos[name] = repo
    return repo


def svc_delete_repo(repo):
    STORE.repos.pop(repo.name, None)


def repo_json(repo):
    return {
        "id": repo.id,
        "name": repo.name,
        "full_name": repo.owner + "/" + repo.name,
        "owner": {"login": repo.owner, "id": 1000},
        "private": repo.private,
        "description": repo.description if repo.description is not None else "",
        "default_branch": repo.default_branch,
        "html_url": "",
        "clone_url": "",
        "created_at": iso_ts(repo.seq),
        "updated_at": iso_ts(repo.seq),
    }


def svc_create_issue(repo, title, body, label_names):
    if not isinstance(title, str) or not title.strip():
        return None, 422, "Validation Failed"
    if not isinstance(body, str):
        body = ""
    if not isinstance(label_names, list):
        label_names = []
    if any(name not in repo.labels for name in label_names):
        return None, 422, "Validation Failed"
    number = repo.next_number
    repo.next_number += 1
    ts = tick()
    issue = {
        "id": next(_ids),
        "number": number,
        "title": title,
        "body": body,
        "state": "open",
        "labels": list(label_names),
        "comments": [],
        "seq": ts,
        "ts": ts,
    }
    repo.issues.append(issue)
    return issue, None, None


def issue_json(repo, issue):
    return {
        "id": issue["id"],
        "number": issue["number"],
        "title": issue["title"],
        "body": issue["body"],
        "state": issue["state"],
        "labels": [
            {
                "name": name,
                "color": repo.labels[name]["color"]
                if name in repo.labels
                else "ededed",
            }
            for name in issue["labels"]
        ],
        "user": {"login": repo.owner},
        "comments": len(issue["comments"]),
        "created_at": iso_ts(issue["seq"]),
        "updated_at": iso_ts(issue["seq"]),
        "html_url": "",
    }


def svc_create_pull(repo, title, body, head, base):
    head = _normalize_ref(head)
    base = _normalize_ref(base)
    if not head or not base or head == base:
        return None, 422, "Validation Failed"
    if _repo_tip(repo, head) is None:
        return None, 422, "Validation Failed"
    if _repo_tip(repo, base) is None:
        return None, 422, "Validation Failed"
    number = repo.next_number
    repo.next_number += 1
    ts = tick()
    pull = {
        "id": next(_ids),
        "number": number,
        "title": title if isinstance(title, str) else "",
        "body": body if isinstance(body, str) else "",
        "state": "open",
        "merged": False,
        "head_ref": head,
        "base_ref": base,
        "merge_commit_sha": None,
        "merged_seq": None,
        "seq": ts,
        "ts": ts,
        "comments": [],
    }
    repo.pulls.append(pull)
    return pull, None, None


def pull_json(repo, pull):
    head_sha = _repo_tip(repo, pull["head_ref"]) or ZERO
    base_sha = _repo_tip(repo, pull["base_ref"]) or ZERO
    merged_at = iso_ts(pull["merged_seq"]) if pull["merged_seq"] is not None else None
    return {
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
        "created_at": iso_ts(pull["seq"]),
        "updated_at": iso_ts(pull["merged_seq"] or pull["seq"]),
        "html_url": "",
    }


def merge_base(repo, a, b):
    if not a or not b:
        return None
    distances = {}
    queue = [(a, 0)]
    while queue:
        oid, depth = queue.pop(0)
        if oid in distances:
            continue
        distances[oid] = depth
        queue.extend((parent, depth + 1) for parent in _commit_parents(repo, oid))
    queue = [b]
    seen = set()
    while queue:
        oid = queue.pop(0)
        if oid in seen:
            continue
        seen.add(oid)
        if oid in distances:
            return oid
        queue.extend(_commit_parents(repo, oid))
    return None


def flat_at(repo, commit_oid):
    if not commit_oid:
        return {}
    commit = _commit_info(repo, commit_oid)
    if not commit:
        return {}
    return flatten_tree(repo, commit.get("tree"))


def three_way_merge(repo, base_c, head_c, target_c):
    base = flat_at(repo, base_c)
    head = flat_at(repo, head_c)
    target = flat_at(repo, target_c)
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
    return (None if conflict else merged), conflict


def svc_merge_pull(repo, pull, method="squash"):
    if pull["merged"] or pull["state"] == "closed":
        return None, 405, "Pull Request is not mergeable"
    head_tip = _repo_tip(repo, pull["head_ref"])
    base_tip = _repo_tip(repo, pull["base_ref"])
    if not head_tip or not base_tip:
        return None, 405, "Pull Request is not mergeable"
    mb = merge_base(repo, head_tip, base_tip)
    merged_flat, conflict = three_way_merge(repo, mb, head_tip, base_tip)
    if conflict:
        return None, 405, "Pull Request is not mergeable"
    tree = tree_from_flat(repo, merged_flat)
    sha = make_commit(
        repo,
        [base_tip],
        tree,
        "Merge pull request #" + str(pull["number"]),
    )
    with repo.lock:
        repo.refs["refs/heads/" + pull["base_ref"]] = sha
        pull["state"] = "closed"
        pull["merged"] = True
        pull["merge_commit_sha"] = sha
        pull["merged_seq"] = tick()
    return sha, None, None


def pull_files(repo, pull):
    head = _repo_tip(repo, pull["head_ref"])
    base = _repo_tip(repo, pull["base_ref"])
    old = flat_at(repo, merge_base(repo, head, base))
    new = flat_at(repo, head)
    result = []
    for path in sorted(set(old) | set(new)):
        before = old.get(path)
        after = new.get(path)
        if before is None:
            additions = _line_count(_blob_bytes(repo, after[1]))
            result.append({
                "filename": path,
                "status": "added",
                "additions": additions,
                "deletions": 0,
                "changes": additions,
                "sha": after[1],
            })
        elif after is None:
            deletions = _line_count(_blob_bytes(repo, before[1]))
            result.append({
                "filename": path,
                "status": "removed",
                "additions": 0,
                "deletions": deletions,
                "changes": deletions,
                "sha": before[1],
            })
        elif before != after:
            a = _blob_bytes(repo, before[1]).decode("utf-8", "replace").splitlines()
            b = _blob_bytes(repo, after[1]).decode("utf-8", "replace").splitlines()
            additions = deletions = 0
            for tag, i1, i2, j1, j2 in difflib.SequenceMatcher(None, a, b).get_opcodes():
                if tag in ("replace", "delete"):
                    deletions += i2 - i1
                if tag in ("replace", "insert"):
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


def svc_put_content(repo, path, content_bytes, message, branch=None, sha=None):
    branch = branch or repo.default_branch
    ref = "refs/heads/" + branch
    tip = repo.refs.get(ref)
    if tip:
        flat = flat_at(repo, tip)
    else:
        tip = _repo_tip(repo, repo.default_branch)
        flat = flat_at(repo, tip)
    existing = flat.get(path)
    if existing and sha is not None and sha != existing[1]:
        return 409, "sha does not match"
    blob = store_object(repo, "blob", content_bytes)
    flat[path] = ("100644", blob)
    tree = tree_from_flat(repo, flat)
    commit = make_commit(repo, [tip] if tip else [], tree, message)
    with repo.lock:
        repo.refs[ref] = commit
    status = 200 if existing else 201
    return status, {
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


def _tree_oid_for_path(repo, root_oid, path):
    current = root_oid
    for part in [p for p in path.split("/") if p]:
        obj = repo.objects.get(current)
        if not obj or obj[0] != "tree":
            return None
        found = None
        for mode, name, oid in parse_tree(obj[1]):
            if name == part:
                found = oid
                break
        if not found:
            return None
        current = found
    return current


def svc_get_content(repo, path, ref=None):
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
        tip = _repo_tip(repo, repo.default_branch)
    if not tip:
        return None
    flat = flat_at(repo, tip)
    if path in flat:
        oid = flat[path][1]
        data = _blob_bytes(repo, oid)
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
        if not rest:
            continue
        name = rest.split("/", 1)[0]
        child_path = prefix + name
        if "/" in rest:
            children[name] = {
                "name": name,
                "path": child_path,
                "type": "dir",
                "sha": _tree_oid_for_path(repo, _commit_info(repo, tip).get("tree"), child_path),
            }
        else:
            children[name] = {
                "name": name,
                "path": child_path,
                "type": "file",
                "sha": flat[item][1],
            }
    return list(children.values()) if children else None


def svc_delete_content(repo, path, message, sha=None, branch=None):
    branch = branch or repo.default_branch
    ref = "refs/heads/" + branch
    tip = repo.refs.get(ref) or _repo_tip(repo, repo.default_branch)
    flat = flat_at(repo, tip)
    existing = flat.get(path)
    if not existing:
        return 404, "Not Found"
    if sha is not None and sha != existing[1]:
        return 409, "sha does not match"
    del flat[path]
    tree = tree_from_flat(repo, flat)
    commit = make_commit(repo, [tip] if tip else [], tree, message)
    with repo.lock:
        repo.refs[ref] = commit
    return 200, {"commit": {"sha": commit}}


def parse_json_body(body_bytes, required=False):
    if not body_bytes:
        return {}, None
    try:
        value = json.loads(body_bytes.decode())
    except Exception:
        return None, ERR(400, "Problems parsing JSON")
    if not isinstance(value, dict):
        return None, ERR(400, "Problems parsing JSON")
    return value, None


def paginate(items, query, base_path, host):
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
        next_page = page + 1
        headers["link"] = (
            '<http://' + host + base_path + "?page=" + str(next_page)
            + "&per_page=" + str(per_page) + '>; rel="next", '
            '<http://' + host + base_path + "?page=" + str(total_pages)
            + "&per_page=" + str(per_page) + '>; rel="last"'
        )
    return selected, headers


def _comment_json(comment, created):
    return {
        "id": comment["id"],
        "body": comment["body"],
        "user": comment["user"],
        "created_at": iso_ts(created),
        "updated_at": iso_ts(created),
    }


def _find_number(items, number):
    try:
        number = int(number)
    except Exception:
        return None
    return next((item for item in items if item["number"] == number), None)


def rest_route(method, seg, query, body_bytes, authed, host):
    if not authed:
        return ERR(401, "Requires authentication")

    if method == "GET" and seg in ([], [""]):
        return J(
            200,
            {
                "current_user_url": "/api/v3/user",
                "current_user_repositories_url": "/api/v3/user/repos",
                "repository_url": "/api/v3/repos/{owner}/{repo}",
            },
            {"x-oauth-scopes": "repo, read:org"},
        )

    if method == "GET" and seg == ["meta"]:
        return J(200, {"installed_version": "1.0.0-forge"})

    if method == "GET" and seg == ["user"]:
        return J(200, {
            "login": VIEWER["login"],
            "id": 1000,
            "name": VIEWER["name"],
            "email": VIEWER["email"],
            "type": "User",
        })

    if seg == ["user", "repos"]:
        if method == "GET":
            repos = sorted(
                [r for r in STORE.repos.values() if r.owner == VIEWER["login"]],
                key=lambda r: r.id,
            )
            values, headers = paginate(repos, query, "/api/v3/user/repos", host)
            return J(200, [repo_json(r) for r in values], headers)
        if method == "POST":
            data, error = parse_json_body(body_bytes, True)
            if error:
                return error
            repo = svc_create_repo(
                data.get("name"),
                data.get("private", False),
                data.get("description", ""),
            )
            if repo is None:
                return ERR(422, "Validation Failed: name already exists on this account")
            return J(201, repo_json(repo))

    if len(seg) >= 3 and seg[0] == "repos":
        owner, name = seg[1], seg[2]
        repo = get_repo(owner, name)
        if repo is None:
            return ERR(404, "Not Found")
        rest = seg[3:]

        if not rest:
            if method == "GET":
                return J(200, repo_json(repo))
            if method == "PATCH":
                data, error = parse_json_body(body_bytes, True)
                if error:
                    return error
                if "description" in data:
                    repo.description = data["description"]
                return J(200, repo_json(repo))
            if method == "DELETE":
                svc_delete_repo(repo)
                return 204, {}, b""

        if rest == ["labels"]:
            if method == "GET":
                return J(200, list(repo.labels.values()))
            if method == "POST":
                data, error = parse_json_body(body_bytes, True)
                if error:
                    return error
                label_name = data.get("name")
                if not label_name:
                    return ERR(422, "Validation Failed")
                color = data.get("color") or "ededed"
                label = {"name": label_name, "color": color}
                repo.labels[label_name] = label
                return J(201, {**label, "default": False})

        if rest == ["git", "refs"] and method == "POST":
            data, error = parse_json_body(body_bytes, True)
            if error:
                return error
            ref, sha = data.get("ref"), data.get("sha")
            if (
                not isinstance(ref, str)
                or not ref.startswith("refs/heads/")
                or sha not in repo.objects
                or repo.objects[sha][0] != "commit"
            ):
                return ERR(422, "Validation Failed")
            repo.refs[ref] = sha
            return J(201, {"ref": ref, "object": {"sha": sha, "type": "commit"}})

        if len(rest) >= 3 and rest[:3] == ["git", "refs", "heads"] and method == "GET":
            branch = "/".join(rest[3:])
            tip = _repo_tip(repo, branch)
            if not tip:
                return ERR(404, "Not Found")
            return J(200, {
                "ref": "refs/heads/" + branch,
                "object": {"sha": tip, "type": "commit"},
            })

        if rest == ["branches"] and method == "GET":
            branches = []
            for ref, tip in sorted(repo.refs.items()):
                if ref.startswith("refs/heads/"):
                    branches.append({
                        "name": ref[len("refs/heads/"):],
                        "commit": {"sha": tip},
                        "protected": False,
                    })
            return J(200, branches)

        if len(rest) >= 2 and rest[0] == "branches" and method == "GET":
            branch = "/".join(rest[1:])
            tip = _repo_tip(repo, branch)
            if not tip:
                return ERR(404, "Not Found")
            return J(200, {
                "name": branch,
                "commit": {"sha": tip},
                "protected": False,
            })

        if rest == ["commits"] and method == "GET":
            value = (query.get("sha") or [repo.default_branch])[0]
            tip = (
                repo.refs.get(value)
                or repo.refs.get("refs/heads/" + value)
                or (value if value in repo.objects else None)
            )
            commits = []
            seen = set()
            stack = [tip] if tip else []
            while stack and len(commits) < 100:
                oid = stack.pop(0)
                if oid in seen:
                    continue
                seen.add(oid)
                c = _commit_info(repo, oid)
                if not c:
                    continue
                parents = _commit_parents(repo, oid)
                commits.append({
                    "sha": oid,
                    "commit": {
                        "message": _commit_message(repo, oid),
                        "author": {
                            "name": _commit_author_name(repo, oid),
                            "date": iso_ts(_commit_ts(repo, oid)),
                        },
                        "committer": {
                            "name": _commit_author_name(repo, oid),
                            "date": iso_ts(_commit_ts(repo, oid)),
                        },
                    },
                    "parents": [{"sha": p} for p in parents],
                })
                stack.extend(parents)
            return J(200, commits)

        if rest and rest[0] == "contents":
            path = "/".join(rest[1:])
            if method == "GET":
                value = svc_get_content(repo, path, (query.get("ref") or [None])[0])
                return ERR(404, "Not Found") if value is None else J(200, value)
            if method in ("PUT", "DELETE"):
                data, error = parse_json_body(body_bytes, True)
                if error:
                    return error
                if method == "PUT":
                    try:
                        content = base64.b64decode(data.get("content", ""), validate=True)
                    except Exception:
                        return ERR(400, "Invalid base64")
                    status, value = svc_put_content(
                        repo,
                        path,
                        content,
                        data.get("message") or "Update " + path,
                        data.get("branch"),
                        data.get("sha"),
                    )
                else:
                    status, value = svc_delete_content(
                        repo,
                        path,
                        data.get("message") or "Delete " + path,
                        data.get("sha"),
                        data.get("branch"),
                    )
                return ERR(status, value) if isinstance(value, str) else J(status, value)

        if rest and rest[0] == "issues":
            tail = rest[1:]
            if not tail and method == "POST":
                data, error = parse_json_body(body_bytes, True)
                if error:
                    return error
                issue, status, msg = svc_create_issue(
                    repo,
                    data.get("title"),
                    data.get("body", ""),
                    data.get("labels", []),
                )
                return ERR(status, msg) if issue is None else J(201, issue_json(repo, issue))
            if not tail and method == "GET":
                state = (query.get("state") or ["open"])[0]
                issues = [
                    i for i in repo.issues
                    if state == "all" or i["state"] == state
                ]
                issues.sort(key=lambda i: i["seq"], reverse=True)
                if (query.get("direction") or ["desc"])[0] == "asc":
                    issues.reverse()
                values, headers = paginate(
                    issues,
                    query,
                    "/api/v3/repos/" + owner + "/" + name + "/issues",
                    host,
                )
                return J(200, [issue_json(repo, i) for i in values], headers)
            if tail:
                issue = _find_number(repo.issues, tail[0])
                if issue is None:
                    return ERR(404, "Not Found")
                if len(tail) == 1 and method == "GET":
                    return J(200, issue_json(repo, issue))
                if len(tail) == 1 and method == "PATCH":
                    data, error = parse_json_body(body_bytes, True)
                    if error:
                        return error
                    labels = data.get("labels", issue["labels"])
                    if any(label not in repo.labels for label in labels):
                        return ERR(422, "Validation Failed")
                    for key in ("title", "body", "state"):
                        if key in data:
                            issue[key] = data[key]
                    issue["labels"] = labels
                    issue["seq"] = tick()
                    return J(200, issue_json(repo, issue))
                if len(tail) == 2 and tail[1] == "comments":
                    if method == "GET":
                        return J(200, [
                            _comment_json(c, c["seq"]) for c in issue["comments"]
                        ])
                    if method == "POST":
                        data, error = parse_json_body(body_bytes, True)
                        if error:
                            return error
                        if not data.get("body"):
                            return ERR(422, "Validation Failed")
                        ts = tick()
                        comment = {
                            "id": next(_ids),
                            "body": data["body"],
                            "user": {"login": repo.owner},
                            "seq": ts,
                        }
                        issue["comments"].append(comment)
                        return J(201, _comment_json(comment, ts))

        if rest and rest[0] == "pulls":
            tail = rest[1:]
            if not tail and method == "POST":
                data, error = parse_json_body(body_bytes, True)
                if error:
                    return error
                pull, status, msg = svc_create_pull(
                    repo,
                    data.get("title"),
                    data.get("body", ""),
                    data.get("head"),
                    data.get("base"),
                )
                return ERR(status, msg) if pull is None else J(201, pull_json(repo, pull))
            if not tail and method == "GET":
                state = (query.get("state") or ["open"])[0]
                pulls = [
                    p for p in repo.pulls
                    if state == "all"
                    or (state == "closed" and (p["state"] == "closed" or p["merged"]))
                    or (state == "open" and p["state"] == "open" and not p["merged"])
                ]
                pulls.sort(key=lambda p: p["seq"], reverse=True)
                values, headers = paginate(
                    pulls,
                    query,
                    "/api/v3/repos/" + owner + "/" + name + "/pulls",
                    host,
                )
                return J(200, [pull_json(repo, p) for p in values], headers)
            if tail:
                pull = _find_number(repo.pulls, tail[0])
                if pull is None:
                    return ERR(404, "Not Found")
                if len(tail) == 1 and method == "GET":
                    return J(200, pull_json(repo, pull))
                if len(tail) == 2 and tail[1] == "files" and method == "GET":
                    return J(200, pull_files(repo, pull))
                if len(tail) == 2 and tail[1] == "merge" and method == "PUT":
                    sha, status, msg = svc_merge_pull(repo, pull)
                    return ERR(status, msg) if sha is None else J(
                        200,
                        {
                            "sha": sha,
                            "merged": True,
                            "message": "Pull Request successfully merged",
                        },
                    )

    return ERR(404, "Not Found")


class Enum(str):
    pass


class GObj:
    def __init__(self, type_name, data):
        self.type_name = type_name
        self.data = data


def gid(type_name, db_id):
    return base64.b64encode(f"{type_name}:{db_id}".encode()).decode()


def parse_gid(s):
    try:
        raw = base64.b64decode(s, validate=True).decode()
        typ, ident = raw.split(":", 1)
        return typ, int(ident)
    except Exception:
        return None


def repo_by_id(db_id):
    for repo in STORE.repos.values():
        if getattr(repo, "id", None) == db_id:
            return repo
    return None


def issue_by_id(db_id):
    for repo in STORE.repos.values():
        for issue in getattr(repo, "issues", []):
            if issue.get("id") == db_id:
                return repo, issue
    return None


def pull_by_id(db_id):
    for repo in STORE.repos.values():
        for pull in getattr(repo, "pulls", []):
            if pull.get("id") == db_id:
                return repo, pull
    return None


def comment_by_id(db_id):
    for repo in STORE.repos.values():
        for issue in getattr(repo, "issues", []):
            for comment in issue.get("comments", []):
                if comment.get("id") == db_id:
                    return repo, issue, comment
        for pull in getattr(repo, "pulls", []):
            for comment in pull.get("comments", []):
                if comment.get("id") == db_id:
                    return repo, pull, comment
    return None


TYPE_FIELDS = {
    "Query": {"viewer": 1, "repository": 1, "node": 1, "search": 1,
              "__type": 1, "__schema": 1},
    "Mutation": {"createIssue": 1, "closeIssue": 1,
                 "createPullRequest": 1, "mergePullRequest": 1,
                 "addComment": 1},
    "User": {"id": 1, "login": 1, "name": 1, "email": 1},
    "Repository": {
        "id": 1, "databaseId": 1, "name": 1, "nameWithOwner": 1,
        "owner": 1, "defaultBranchRef": 1, "viewerPermission": 1,
        "hasIssuesEnabled": 1, "isPrivate": 1, "description": 1,
        "issue": 1, "issues": 1, "pullRequest": 1, "pullRequests": 1,
        "url": 1, "createdAt": 1, "updatedAt": 1,
    },
    "Ref": {"name": 1, "target": 1},
    "Commit": {"oid": 1, "message": 1},
    "Issue": {
        "id": 1, "databaseId": 1, "number": 1, "title": 1, "state": 1,
        "body": 1, "author": 1, "labels": 1, "comments": 1,
        "createdAt": 1, "updatedAt": 1, "url": 1, "closed": 1,
        "repository": 1,
    },
    "IssueConnection": {"nodes": 1, "edges": 1, "pageInfo": 1, "totalCount": 1},
    "IssueEdge": {"node": 1, "cursor": 1},
    "PageInfo": {
        "hasNextPage": 1, "hasPreviousPage": 1,
        "startCursor": 1, "endCursor": 1,
    },
    "Label": {"name": 1, "color": 1},
    "LabelConnection": {"nodes": 1, "totalCount": 1},
    "IssueComment": {"id": 1, "body": 1, "author": 1, "createdAt": 1},
    "CommentConnection": {"nodes": 1, "totalCount": 1},
    "PullRequest": {
        "id": 1, "databaseId": 1, "number": 1, "title": 1, "body": 1,
        "state": 1, "merged": 1, "mergeable": 1, "headRefName": 1,
        "baseRefName": 1, "headRefOid": 1, "baseRefOid": 1, "files": 1,
        "author": 1, "createdAt": 1, "updatedAt": 1, "mergedAt": 1,
        "url": 1, "repository": 1, "comments": 1,
    },
    "PullRequestConnection": {"nodes": 1, "totalCount": 1},
    "PullRequestFile": {"path": 1},
    "PullRequestChangedFile": {"path": 1},
    "PullRequestFilesConnection": {"nodes": 1, "totalCount": 1},
    "CreateIssuePayload": {"issue": 1, "clientMutationId": 1},
    "CloseIssuePayload": {"issue": 1, "clientMutationId": 1},
    "CreatePullRequestPayload": {"pullRequest": 1, "clientMutationId": 1},
    "MergePullRequestPayload": {"pullRequest": 1, "clientMutationId": 1},
    "AddCommentPayload": {"commentEdge": 1, "clientMutationId": 1},
    "CommentEdge": {"node": 1, "cursor": 1},
    "SearchResultItemConnection": {
        "nodes": 1, "edges": 1, "pageInfo": 1, "issueCount": 1,
    },
    "__Type": {
        "name": 1, "kind": 1, "description": 1,
        "fields": 1, "enumValues": 1,
    },
    "__Field": {"name": 1, "description": 1, "type": 1},
    "__EnumValue": {"name": 1, "description": 1},
    "__Schema": {"types": 1, "queryType": 1, "mutationType": 1,
                 "subscriptionType": 1},
}

ENUMS = {
    "SearchType": ["ISSUE", "REPOSITORY", "USER", "DISCUSSION"],
    "IssueState": ["OPEN", "CLOSED"],
    "PullRequestState": ["OPEN", "CLOSED", "MERGED"],
    "MergeableState": ["MERGEABLE", "CONFLICTING", "UNKNOWN"],
    "OrderDirection": ["ASC", "DESC"],
    "IssueOrderField": ["CREATED_AT", "UPDATED_AT", "COMMENTS"],
    "RepositoryPermission": ["ADMIN", "MAINTAIN", "WRITE", "TRIAGE", "READ"],
    "PullRequestMergeMethod": ["MERGE", "SQUASH", "REBASE"],
}


class _GQLParser:
    def __init__(self, text):
        self.text = text
        self.tokens = []
        self.i = 0
        self._tokenize()
        self.fragments = {}

    def _tokenize(self):
        s = self.text
        i = 0
        while i < len(s):
            c = s[i]
            if c.isspace() or c == ",":
                i += 1
                continue
            if c == "#":
                j = s.find("\n", i)
                i = len(s) if j < 0 else j + 1
                continue
            if s.startswith("...", i):
                self.tokens.append(("...", "..."))
                i += 3
                continue
            if c in "{}()[]:@!$":
                self.tokens.append((c, c))
                i += 1
                continue
            if c == '"':
                j = i + 1
                escaped = False
                while j < len(s):
                    if not escaped and s[j] == '"':
                        break
                    if not escaped and s[j] == "\\":
                        escaped = True
                    else:
                        escaped = False
                    j += 1
                if j >= len(s):
                    raise ValueError("Unterminated string")
                raw = s[i:j + 1]
                self.tokens.append(("string", json.loads(raw)))
                i = j + 1
                continue
            m = re.match(r"-?\d+", s[i:])
            if m:
                value = int(m.group(0))
                self.tokens.append(("int", value))
                i += len(m.group(0))
                continue
            m = re.match(r"[_A-Za-z][_0-9A-Za-z]*", s[i:])
            if m:
                value = m.group(0)
                self.tokens.append(("name", value))
                i += len(value)
                continue
            raise ValueError(f"Unexpected character: {c}")
        self.tokens.append(("EOF", None))

    def peek(self, kind=None, value=None):
        token = self.tokens[self.i]
        return ((kind is None or token[0] == kind) and
                (value is None or token[1] == value))

    def take(self, kind=None, value=None):
        if not self.peek(kind, value):
            got = self.tokens[self.i]
            expected = kind or value or "token"
            raise ValueError(f"Expected {expected}, got {got[1]!r}")
        token = self.tokens[self.i]
        self.i += 1
        return token[1]

    def parse(self):
        operations = []
        while not self.peek("EOF"):
            if self.peek("{"):
                kind, name = "query", None
            else:
                kind = self.take("name")
                if kind not in ("query", "mutation"):
                    raise ValueError(f"Unknown operation {kind}")
                name = None
                if self.peek("name"):
                    name = self.take("name")
                if self.peek("("):
                    self.skip_parens()
                if self.peek("@"):
                    self.skip_directives()
            selection = self.selection()
            operations.append({"kind": kind, "name": name,
                               "selection": selection})
        return operations, self.fragments

    def skip_parens(self):
        depth = 0
        while True:
            t = self.take()
            if t == "(":
                depth += 1
            elif t == ")":
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
        result = []
        while not self.peek("}"):
            if self.peek("..."):
                self.take("...")
                if self.peek("name", "on"):
                    self.take("name", "on")
                    typ = self.take("name")
                    if self.peek("@"):
                        self.skip_directives()
                    result.append({"inline_on": typ, "selection": self.selection()})
                else:
                    result.append({"spread": self.take("name")})
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
                    arg = self.take("name")
                    self.take(":")
                    args[arg] = self.value()
                self.take(")")
            if self.peek("@"):
                self.skip_directives()
            sub = self.selection() if self.peek("{") else None
            result.append({"name": name, "alias": alias, "args": args,
                           "selection": sub})
        self.take("}")
        return result

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
            out = []
            while not self.peek("]"):
                out.append(self.value())
            self.take("]")
            return out
        if self.peek("{"):
            self.take("{")
            out = {}
            while not self.peek("}"):
                key = self.take("name")
                self.take(":")
                out[key] = self.value()
            self.take("}")
            return out
        return Enum(self.take("name"))


def _gql_value(value, variables):
    if isinstance(value, tuple) and len(value) == 2 and value[0] == "var":
        return variables.get(value[1])
    if isinstance(value, list):
        return [_gql_value(v, variables) for v in value]
    if isinstance(value, dict):
        return {k: _gql_value(v, variables) for k, v in value.items()}
    return value


def _user(repo=None):
    login = getattr(repo, "owner", VIEWER) if repo is not None else VIEWER
    if login == VIEWER:
        return GObj("User", {"login": VIEWER["login"], "id": 1000,
                             "name": VIEWER["name"], "email": VIEWER["email"]})
    return GObj("User", {"login": login, "id": 1000,
                         "name": login, "email": ""})


def _repo_obj(repo):
    return GObj("Repository", repo)


def _issue_obj(repo, issue):
    return GObj("Issue", {"repo": repo, "issue": issue})


def _pull_obj(repo, pull):
    return GObj("PullRequest", {"repo": repo, "pull": pull})


def _comment_obj(comment):
    return GObj("IssueComment", comment)


def _cursor(issue):
    return base64.b64encode(f"cursor:{issue.get('seq', 0)}".encode()).decode()


def _after_seq(after):
    if not after:
        return None
    try:
        raw = base64.b64decode(after, validate=True).decode()
        return int(raw.split(":", 1)[1])
    except Exception:
        return None


def _connection(type_name, items, first, after=None):
    first = 30 if first is None else max(0, int(first))
    seq = _after_seq(after)
    if seq is not None:
        for n, item in enumerate(items):
            if item.get("seq") == seq:
                items = items[n + 1:]
                break
    page = items[:first]
    cursors = [_cursor(x) for x in page]
    return GObj(type_name, {
        "items": page,
        "page": {
            "hasNextPage": len(items) > len(page),
            "hasPreviousPage": False,
            "startCursor": cursors[0] if cursors else None,
            "endCursor": cursors[-1] if cursors else None,
        },
    })


def _resolve_field(type_name, source, name, args, ctx):
    if type_name == "Query":
        if name == "viewer":
            return _user()
        if name == "repository":
            repo = get_repo(args.get("owner"), args.get("name"))
            return _repo_obj(repo) if repo else None
        if name == "node":
            parsed = parse_gid(args.get("id"))
            if not parsed:
                return None
            typ, ident = parsed
            if typ == "Repository":
                repo = repo_by_id(ident)
                return _repo_obj(repo) if repo else None
            if typ == "Issue":
                found = issue_by_id(ident)
                return _issue_obj(*found) if found else None
            if typ == "PullRequest":
                found = pull_by_id(ident)
                return _pull_obj(*found) if found else None
            return None
        if name == "search":
            return GObj("SearchResultItemConnection", {
                "items": [], "edges": [], "page": {}, "issueCount": 0
            })
        if name == "__type":
            typ = args.get("name")
            if typ not in TYPE_FIELDS and typ not in ENUMS:
                return None
            return GObj("__Type", {
                "name": typ,
                "kind": "ENUM" if typ in ENUMS else "OBJECT",
                "fields_list": list(TYPE_FIELDS.get(typ, {})),
                "enum_values": ENUMS.get(typ),
            })
        if name == "__schema":
            names = list(TYPE_FIELDS) + list(ENUMS)
            return GObj("__Schema", {
                "types": [{"name": x} for x in names],
                "queryType": {"name": "Query"},
                "mutationType": {"name": "Mutation"},
            })

    if type_name == "Mutation":
        inp = args.get("input") or {}
        if name == "createIssue":
            parsed = parse_gid(inp.get("repositoryId"))
            repo = repo_by_id(parsed[1]) if parsed and parsed[0] == "Repository" else None
            if not repo:
                ctx["errors"].append("Repository not found")
                return None
            issue, status, msg = svc_create_issue(
                repo, inp.get("title", ""), inp.get("body", "") or "", [])
            if issue is None:
                ctx["errors"].append(msg or "Unable to create issue")
                return None
            return GObj("CreateIssuePayload", {
                "issue": _issue_obj(repo, issue),
                "clientMutationId": inp.get("clientMutationId"),
            })
        if name == "closeIssue":
            parsed = parse_gid(inp.get("issueId"))
            found = issue_by_id(parsed[1]) if parsed and parsed[0] == "Issue" else None
            if not found:
                ctx["errors"].append("Issue not found")
                return None
            repo, issue = found
            issue["state"] = "closed"
            return GObj("CloseIssuePayload", {
                "issue": _issue_obj(repo, issue),
                "clientMutationId": inp.get("clientMutationId"),
            })
        if name == "createPullRequest":
            parsed = parse_gid(inp.get("repositoryId"))
            repo = repo_by_id(parsed[1]) if parsed and parsed[0] == "Repository" else None
            if not repo:
                ctx["errors"].append("Repository not found")
                return None
            pull, status, msg = svc_create_pull(
                repo, inp.get("title", ""), inp.get("body", "") or "",
                inp.get("headRefName"), inp.get("baseRefName"))
            if pull is None:
                ctx["errors"].append(msg or "Unable to create pull request")
                return None
            return GObj("CreatePullRequestPayload", {
                "pullRequest": _pull_obj(repo, pull),
                "clientMutationId": inp.get("clientMutationId"),
            })
        if name == "mergePullRequest":
            parsed = parse_gid(inp.get("pullRequestId"))
            found = pull_by_id(parsed[1]) if parsed and parsed[0] == "PullRequest" else None
            if not found:
                ctx["errors"].append("Pull request not found")
                return None
            repo, pull = found
            method = str(inp.get("mergeMethod") or "SQUASH").lower()
            sha, status, msg = svc_merge_pull(repo, pull, method)
            if status:
                ctx["errors"].append(msg or "Unable to merge pull request")
            return GObj("MergePullRequestPayload", {
                "pullRequest": _pull_obj(repo, pull),
                "clientMutationId": inp.get("clientMutationId"),
            })
        if name == "addComment":
            parsed = parse_gid(inp.get("subjectId"))
            body = inp.get("body", "")
            _cts = tick()
            comment = {"id": next(_ids), "body": body, "ts": _cts, "seq": _cts,
                       "user": {"login": VIEWER["login"]}}
            if parsed and parsed[0] == "Issue":
                found = issue_by_id(parsed[1])
                if found:
                    repo, issue = found
                    issue.setdefault("comments", []).append(comment)
                else:
                    ctx["errors"].append("Subject not found")
                    return None
            elif parsed and parsed[0] == "PullRequest":
                found = pull_by_id(parsed[1])
                if found:
                    repo, pull = found
                    pull.setdefault("comments", []).append(comment)
                else:
                    ctx["errors"].append("Subject not found")
                    return None
            else:
                ctx["errors"].append("Subject not found")
                return None
            return GObj("AddCommentPayload", {
                "commentEdge": GObj("CommentEdge", {
                    "node": _comment_obj(comment),
                    "cursor": "Y3Vyc29yOjA=",
                }),
                "clientMutationId": inp.get("clientMutationId"),
            })

    if type_name == "User":
        if name == "id":
            return gid("User", source.get("id", 1000))
        return source.get(name)

    if type_name == "Repository":
        repo = source
        if name == "id":
            return gid("Repository", repo.id)
        if name == "databaseId":
            return repo.id
        if name == "name":
            return repo.name
        if name == "nameWithOwner":
            return f"{repo.owner}/{repo.name}"
        if name == "owner":
            return _user(repo)
        if name == "defaultBranchRef":
            branch = getattr(repo, "default_branch", "main")
            refs = getattr(repo, "refs", {})
            tip = refs.get(f"refs/heads/{branch}")
            return GObj("Ref", {"name": branch, "tip": tip}) if tip else None
        if name == "viewerPermission":
            return "ADMIN"
        if name == "hasIssuesEnabled":
            return True
        if name == "isPrivate":
            return repo.private
        if name == "description":
            return repo.description
        if name in ("createdAt", "updatedAt"):
            return iso_ts(repo.seq)
        if name == "url":
            return ""
        if name == "issue":
            for issue in repo.issues:
                if issue.get("number") == args.get("number"):
                    return _issue_obj(repo, issue)
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
            return _connection("IssueConnection", items, args.get("first"),
                               args.get("after"))
        if name == "pullRequest":
            for pull in repo.pulls:
                if pull.get("number") == args.get("number"):
                    return _pull_obj(repo, pull)
            return None
        if name == "pullRequests":
            items = list(repo.pulls)
            states = args.get("states")
            if states:
                wanted = {str(x) for x in states}
                items = [p for p in items if (
                    ("MERGED" if p.get("merged") else
                     "CLOSED" if p.get("state") == "closed" else "OPEN")
                    in wanted)]
            items.sort(key=lambda x: x.get("number", 0))
            return _connection("PullRequestConnection", items, args.get("first"),
                               args.get("after"))

    if type_name == "Ref":
        if name == "name":
            return source.get("name")
        if name == "target":
            return GObj("Commit", {"oid": source.get("tip"), "message": ""})
    if type_name == "Commit":
        return source.get(name)

    if type_name == "Issue":
        repo, issue = source["repo"], source["issue"]
        if name == "id":
            return gid("Issue", issue["id"])
        if name == "databaseId":
            return issue["id"]
        if name in ("number", "title", "body"):
            return issue.get(name)
        if name == "state":
            return "CLOSED" if issue.get("state") == "closed" else "OPEN"
        if name == "author":
            return _user(repo)
        if name == "labels":
            return GObj("LabelConnection", {
                "items": [{"name": x, "color": ""} for x in issue.get("labels", [])]
            })
        if name == "comments":
            return GObj("CommentConnection", {
                "items": [_comment_obj(x) for x in issue.get("comments", [])]
            })
        if name in ("createdAt", "updatedAt"):
            return iso_ts(issue.get("ts"))
        if name == "closed":
            return issue.get("state") == "closed"
        if name == "repository":
            return _repo_obj(repo)
        if name == "url":
            return ""

    if type_name == "PullRequest":
        repo, pull = source["repo"], source["pull"]
        if name == "id":
            return gid("PullRequest", pull["id"])
        if name == "databaseId":
            return pull["id"]
        if name in ("number", "title", "body"):
            return pull.get(name)
        if name == "state":
            return ("MERGED" if pull.get("merged") else
                    "CLOSED" if pull.get("state") == "closed" else "OPEN")
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
            return getattr(repo, "refs", {}).get(f"refs/heads/{ref}", ZERO)
        if name == "files":
            files = [{"path": x.get("filename", "")} for x in pull_files(repo, pull)]
            return GObj("PullRequestFilesConnection", {"items": files})
        if name == "author":
            return _user(repo)
        if name in ("createdAt", "updatedAt"):
            return iso_ts(pull.get("ts"))
        if name == "mergedAt":
            return iso_ts(pull.get("merged_at")) if pull.get("merged_at") else None
        if name == "repository":
            return _repo_obj(repo)
        if name == "comments":
            return GObj("CommentConnection", {
                "items": [_comment_obj(x) for x in pull.get("comments", [])]
            })
        if name == "url":
            return ""

    if type_name in ("IssueComment",):
        if name == "id":
            return gid("IssueComment", source["id"])
        if name == "author":
            return _user()
        if name == "createdAt":
            return iso_ts(source.get("ts", 0))
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

    if type_name in ("IssueConnection", "PullRequestConnection"):
        items = source.get("items", [])
        if name == "nodes":
            return [_issue_obj(source.get("repo"), x) if type_name == "IssueConnection"
                    else _pull_obj(source.get("repo"), x) for x in items]
        if name == "edges":
            return [GObj("IssueEdge", {"node": _issue_obj(source.get("repo"), x),
                                       "cursor": _cursor(x)}) for x in items]
        if name == "pageInfo":
            return GObj("PageInfo", source.get("page", {}))
        if name == "totalCount":
            return len(items)

    if type_name == "PageInfo":
        return source.get(name)
    if type_name == "PullRequestFile" or type_name == "PullRequestChangedFile":
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
            return GObj("PageInfo", {})
    if type_name == "__Type":
        if name in ("name", "kind", "description"):
            return source.get(name)
        if name == "fields":
            return [GObj("__Field", {"name": x}) for x in source.get("fields_list") or []]
        if name == "enumValues":
            return [GObj("__EnumValue", {"name": x}) for x in source.get("enum_values") or []]
    if type_name == "__Field":
        return source.get(name)
    if type_name == "__EnumValue":
        return source.get(name)
    if type_name == "__Schema":
        return source.get(name)
    return None


def _materialize(value, selection, ctx, runtime_type=None):
    if value is None:
        return None
    if isinstance(value, GObj):
        return _resolve_fields(value.type_name, value.data, selection or [], ctx)
    if isinstance(value, list):
        return [_materialize(x, selection, ctx) for x in value]
    if isinstance(value, dict):
        return value
    return value


def _resolve_fields(type_name, source, fields, ctx):
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
        if name not in TYPE_FIELDS.get(type_name, {}):
            ctx["errors"].append(f"Field '{name}' is undefined on type '{type_name}'")
            out[key] = None
            continue
        value = _resolve_field(type_name, source, name,
                               {k: _gql_value(v, ctx["variables"])
                                for k, v in field.get("args", {}).items()}, ctx)
        out[key] = _materialize(value, field.get("selection"), ctx)
    return out


def _execute_document(document, variables=None, operation_name=None):
    parser = _GQLParser(document)
    operations, fragments = parser.parse()
    chosen = operations
    if operation_name is not None:
        chosen = [x for x in operations if x["name"] == operation_name]
        if not chosen:
            raise ValueError(f"Unknown operation named '{operation_name}'")
    results = []
    for operation in chosen:
        ctx = {"variables": variables or {}, "errors": [], "fragments": fragments}
        root = _resolve_fields(
            "Mutation" if operation["kind"] == "mutation" else "Query",
            None, operation["selection"], ctx)
        result = {"data": root}
        if ctx["errors"]:
            result["errors"] = [{"message": x} for x in ctx["errors"]]
        results.append(result)
    return results[0] if len(results) == 1 else results


def graphql_route(body_bytes, authed):
    headers = {"content-type": "application/json; charset=utf-8"}
    if not authed:
        return 401, headers, json.dumps({"message": "Bad credentials"}).encode()
    try:
        body = json.loads(body_bytes)
    except Exception:
        return 400, headers, json.dumps({"errors": [{"message": "Invalid JSON"}]}).encode()

    def one(item):
        try:
            return _execute_document(
                item["query"],
                item.get("variables") or {},
                item.get("operationName"),
            )
        except Exception as exc:
            return {"data": None, "errors": [{"message": str(exc)}]}

    if isinstance(body, list):
        return J(200, [one(x) for x in body])
    if isinstance(body, dict) and isinstance(body.get("operations"), list):
        return J(200, [one(x) for x in body["operations"]])
    if isinstance(body, dict):
        result = one(body)
        return J(200, result)
    return J(400, {"errors": [{"message": "Invalid request"}]})


import json
import os
import sys
import time
import socket
import threading
import itertools
import re
import urllib.request
import urllib.parse
import urllib.error
import http.server


TOOLS = [
    {
        "name": "create_repo",
        "description": "Create a new repository",
        "inputSchema": {
            "type": "object",
            "properties": {
                "name": {"type": "string", "description": "Repository name"},
                "description": {"type": "string", "description": "Repository description"},
                "private": {"type": "boolean", "description": "Whether the repository is private"},
            },
            "required": ["name"],
        },
    },
    {
        "name": "get_repo",
        "description": "Get a repository",
        "inputSchema": {
            "type": "object",
            "properties": {
                "owner": {"type": "string", "description": "Repository owner"},
                "repo": {"type": "string", "description": "Repository name"},
            },
            "required": ["owner", "repo"],
        },
    },
    {
        "name": "create_issue",
        "description": "Create an issue",
        "inputSchema": {
            "type": "object",
            "properties": {
                "owner": {"type": "string", "description": "Repository owner"},
                "repo": {"type": "string", "description": "Repository name"},
                "title": {"type": "string", "description": "Issue title"},
                "body": {"type": "string", "description": "Issue body"},
            },
            "required": ["owner", "repo", "title"],
        },
    },
    {
        "name": "list_issues",
        "description": "List repository issues",
        "inputSchema": {
            "type": "object",
            "properties": {
                "owner": {"type": "string", "description": "Repository owner"},
                "repo": {"type": "string", "description": "Repository name"},
                "state": {"type": "string", "description": "Issue state: open, closed, all, or any"},
            },
            "required": ["owner", "repo"],
        },
    },
    {
        "name": "create_pull_request",
        "description": "Create a pull request",
        "inputSchema": {
            "type": "object",
            "properties": {
                "owner": {"type": "string", "description": "Repository owner"},
                "repo": {"type": "string", "description": "Repository name"},
                "title": {"type": "string", "description": "Pull request title"},
                "head": {"type": "string", "description": "Source branch"},
                "base": {"type": "string", "description": "Target branch"},
                "body": {"type": "string", "description": "Pull request body"},
            },
            "required": ["owner", "repo", "title", "head", "base"],
        },
    },
    {
        "name": "merge_pull_request",
        "description": "Merge a pull request",
        "inputSchema": {
            "type": "object",
            "properties": {
                "owner": {"type": "string", "description": "Repository owner"},
                "repo": {"type": "string", "description": "Repository name"},
                "pull_number": {"type": "integer", "description": "Pull request number"},
            },
            "required": ["owner", "repo", "pull_number"],
        },
    },
]


class ToolError(Exception):
    pass


def run_tool(name, args):
    if name == "create_repo":
        repo = svc_create_repo(
            args["name"],
            bool(args.get("private", False)),
            args.get("description", "") or "",
        )
        if repo is None:
            repo = STORE.repos[args["name"]]
        return repo_json(repo)

    if name not in {
        "get_repo",
        "create_issue",
        "list_issues",
        "create_pull_request",
        "merge_pull_request",
    }:
        raise ToolError(f"Unknown tool: {name}")

    repo = get_repo(args["owner"], args["repo"])
    if repo is None:
        raise ToolError("repository not found")

    if name == "get_repo":
        return repo_json(repo)

    if name == "create_issue":
        labels = args.get("labels") or []
        issue, status, msg = svc_create_issue(
            repo, args["title"], args.get("body") or "", labels
        )
        if issue is None:
            raise ToolError(msg)
        return issue_json(repo, issue)

    if name == "list_issues":
        state = args.get("state")
        items = list(repo.issues)
        if state in ("open", "closed"):
            items = [issue for issue in items if issue["state"] == state]
        return {
            "issues": [issue_json(repo, issue) for issue in items],
            "total_count": len(items),
        }

    if name == "create_pull_request":
        pull, status, msg = svc_create_pull(
            repo,
            args["title"],
            args.get("body") or "",
            args["head"],
            args["base"],
        )
        if pull is None:
            raise ToolError(msg)
        return pull_json(repo, pull)

    try:
        number = int(args["pull_number"])
    except (TypeError, ValueError, OverflowError):
        raise ToolError("invalid pull request number") from None
    pull = next((p for p in repo.pulls if p["number"] == number), None)
    if pull is None:
        raise ToolError("pull request not found")
    sha, status, msg = svc_merge_pull(repo, pull)
    if status:
        raise ToolError(msg)
    return pull_json(repo, pull)


_MCP_VERSIONS = [
    "2026-07-28",
    "2025-11-25",
    "2025-06-18",
    "2025-03-26",
    "2024-11-05",
]


def _mcp_error(request_id, code, message):
    return {
        "jsonrpc": "2.0",
        "id": request_id,
        "error": {"code": code, "message": message},
    }


def mcp_route(body_bytes, authed, req_headers):
    if not authed:
        return (
            401,
            {"content-type": "application/json"},
            json.dumps({"message": "Unauthorized"}).encode(),
        )
    try:
        payload = json.loads(body_bytes)
    except (ValueError, UnicodeError):
        return (
            400,
            {"content-type": "application/json"},
            json.dumps(_mcp_error(None, -32700, "Parse error")).encode(),
        )

    extra_headers = {}

    def dispatch(obj):
        request_id = obj.get("id")
        method = obj.get("method")
        if method == "server/discover":
            result = {
                "supportedVersions": _MCP_VERSIONS,
                "capabilities": {"tools": {}},
                "serverInfo": {"name": "forge", "version": "1.0.0"},
                "protocolVersion": "2026-07-28",
            }
        elif method == "initialize":
            params = obj.get("params") or {}
            if not isinstance(params, dict):
                return _mcp_error(request_id, -32602, "Invalid params")
            want = params.get("protocolVersion")
            chosen = want if want in _MCP_VERSIONS else "2025-11-25"
            result = {
                "protocolVersion": chosen,
                "capabilities": {"tools": {}},
                "serverInfo": {"name": "forge", "version": "1.0.0"},
            }
            extra_headers["Mcp-Session-Id"] = "forge-session-1"
        elif method == "tools/list":
            result = {"tools": TOOLS}
        elif method == "tools/call":
            params = obj.get("params") or {}
            if not isinstance(params, dict):
                return _mcp_error(request_id, -32602, "Invalid params")
            name = params.get("name")
            tool = next((tool for tool in TOOLS if tool["name"] == name), None)
            if tool is None:
                return _mcp_error(request_id, -32602, f"Unknown tool: {name}")
            args = params.get("arguments", {})
            if not isinstance(args, dict):
                return _mcp_error(request_id, -32602, "Invalid arguments")
            for prop in tool["inputSchema"]["required"]:
                if prop not in args:
                    return _mcp_error(
                        request_id, -32602, f"Missing required argument: {prop}"
                    )
            try:
                value = run_tool(name, args)
            except ToolError as exc:
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
        elif method == "ping":
            result = {}
        else:
            return _mcp_error(request_id, -32601, "Method not found")
        return {"jsonrpc": "2.0", "id": request_id, "result": result}

    if isinstance(payload, list):
        envelopes = [
            dispatch(obj)
            for obj in payload
            if isinstance(obj, dict) and "id" in obj
        ]
        status, headers, body = J(200, envelopes)
        headers = dict(headers)
        headers.update(extra_headers)
        return status, headers, body

    if not isinstance(payload, dict):
        return (
            400,
            {"content-type": "application/json"},
            json.dumps(_mcp_error(None, -32600, "Invalid Request")).encode(),
        )
    if "id" not in payload:
        return 200, {}, b""
    envelope = dispatch(payload)
    return (
        200,
        {"content-type": "application/json", **extra_headers},
        json.dumps(envelope).encode(),
    )


_req_counter = itertools.count(1)


class Handler(http.server.BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.1"

    def log_message(self, *a):
        pass

    def setup(self):
        super().setup()
        try:
            self.connection.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        except OSError:
            pass

    def _read_body(self):
        limit = 64 * 1024 * 1024

        def read_exact(size):
            chunks = []
            while size:
                chunk = self.rfile.read(size)
                if not chunk:
                    raise ValueError("incomplete request body")
                chunks.append(chunk)
                size -= len(chunk)
            return b"".join(chunks)

        transfer = self.headers.get("Transfer-Encoding", "")
        if "chunked" in [part.strip().lower() for part in transfer.split(",")]:
            chunks = []
            total = 0
            while True:
                line = self.rfile.readline(65537)
                if len(line) > 65536 or not line.endswith(b"\r\n"):
                    raise ValueError("invalid chunk header")
                size = int(line[:-2].split(b";", 1)[0].strip(), 16)
                if size < 0 or total + size > limit:
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
                chunks.append(read_exact(size))
                total += size
                if read_exact(2) != b"\r\n":
                    raise ValueError("invalid chunk terminator")

        length = int(self.headers.get("Content-Length", "0"))
        if length < 0 or length > limit:
            raise ValueError("invalid request body length")
        return read_exact(length)

    def _send(self, status, headers, body):
        if status == 204:
            body = b""
        self.send_response(status)
        self.send_header("x-github-request-id", f"req-{next(_req_counter)}")
        content_type = next(
            (value for key, value in headers.items() if key.lower() == "content-type"),
            None,
        )
        if content_type is not None:
            self.send_header("content-type", content_type)
        elif body:
            self.send_header("content-type", "application/json; charset=utf-8")
        self.send_header("content-length", str(len(body)))
        for key, value in headers.items():
            if key.lower() not in {
                "content-type", "content-length", "x-github-request-id"
            }:
                self.send_header(key, value)
        self.end_headers()
        if self.command != "HEAD" and body:
            self.wfile.write(body)

    def _authed(self):
        return TOKEN == "" or self.headers.get("Authorization") == "Bearer " + TOKEN

    def _handle(self, method):
        try:
            self._route(method)
        except Exception:
            self.close_connection = True
            try:
                self._send(*ERR(500, "Internal Server Error"))
            except Exception:
                pass

    def _route(self, method):
        url = urllib.parse.urlsplit(self.path)
        path = url.path
        query = urllib.parse.parse_qs(url.query)
        body = self._read_body()
        api_method = "GET" if method == "HEAD" else method

        if api_method == "GET" and path == "/healthz":
            self._send(*J(200, {"ok": True}))
            return

        if path == "/api/v3" or path.startswith("/api/v3/"):
            seg = [
                urllib.parse.unquote(segment)
                for segment in path[len("/api/v3"):].split("/")
                if segment != ""
            ]
            self._send(
                *rest_route(
                    api_method,
                    seg,
                    query,
                    body,
                    self._authed(),
                    self.headers.get("Host", ""),
                )
            )
            return

        if path == "/api/graphql":
            if api_method == "POST":
                self._send(*graphql_route(body, self._authed()))
            else:
                self._send(*ERR(404, "Not Found"))
            return

        if path == "/mcp":
            if method == "POST":
                self._send(*mcp_route(body, self._authed(), self.headers))
            else:
                self._send(
                    405,
                    {"content-type": "application/json"},
                    json.dumps(_mcp_error(None, -32601, "Method not found")).encode(),
                )
            return

        match = re.fullmatch(r"/([^/]+)/([^/]+)\.git(?:/(.*))?", path)
        if match:
            owner, name, tail = match.groups()
            if not tail:
                self._send(*ERR(404, "Not Found"))
                return

            service = None
            if tail == "info/refs" and method == "GET":
                service = query.get("service", [None])[0]
                valid = service in ("git-upload-pack", "git-receive-pack")
            else:
                valid = method == "POST" and tail in (
                    "git-upload-pack", "git-receive-pack"
                )
            if not valid:
                self._send(*ERR(404, "Not Found"))
                return
            if not self._authed():
                self._send(*ERR(401, "Requires authentication"))
                return

            repo = get_repo(urllib.parse.unquote(owner), urllib.parse.unquote(name))
            if repo is None:
                self._send(*ERR(404, "Not Found"))
                return
            version2 = "version=2" in (self.headers.get("Git-Protocol") or "")
            if tail == "info/refs":
                status, content_type, response_body = git_info_refs(
                    repo, service, version2
                )
            elif tail == "git-upload-pack":
                status, content_type, response_body = git_upload_pack(
                    repo, body, version2
                )
            else:
                status, content_type, response_body = git_receive_pack(repo, body)
            self._send(status, {"content-type": content_type}, response_body)
            return

        self._send(*ERR(404, "Not Found"))

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


class Server(http.server.ThreadingHTTPServer):
    daemon_threads = True
    request_queue_size = 128
    allow_reuse_address = True


def main():
    env_url = os.environ.get("MAKEFUN_ENV_URL", "").rstrip("/")
    if not env_url:
        sys.stderr.write("MAKEFUN_ENV_URL must be set\n")
        return 1

    server = Server(("0.0.0.0", 0), Handler)
    port = server.server_address[1]
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    try:
        delay = 0.25
        while True:
            request = urllib.request.Request(
                env_url + "/register",
                data=json.dumps({"port": port}).encode(),
                headers={"Content-Type": "application/json"},
                method="POST",
            )
            registered = False
            try:
                with urllib.request.urlopen(request, timeout=30) as response:
                    registered = response.status in (200, 409)
            except urllib.error.HTTPError as exc:
                registered = exc.code == 409
                exc.close()
            except Exception:
                pass
            if registered:
                break
            time.sleep(delay)
            delay = min(delay * 2, 2.0)

        delay = 0.35
        while True:
            try:
                request = urllib.request.Request(env_url + "/done", method="GET")
                with urllib.request.urlopen(request, timeout=30) as response:
                    result = json.load(response)
                if isinstance(result, dict) and result.get("done") is True:
                    break
                delay = 0.35
            except Exception:
                time.sleep(delay)
                delay = min(delay * 2, 2.0)
                continue
            time.sleep(delay)
    finally:
        server.shutdown()
        server.server_close()
    return 0


if __name__ == "__main__":
    sys.exit(main())
