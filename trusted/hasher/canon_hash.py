"""BendVerify canonical hashing (competition v1). TRUSTED.

Every digest used by the competition is computed here, by the verifier,
from bytes it holds. Digests claimed by a competitor (manifest, certificate
chain) are only ever *compared* against these recomputed values.

* ``canonical_json(obj)``  -- UTF-8, sorted keys, no insignificant whitespace,
  integers only (floats are rejected), NFC-normalised strings.
* ``digest(data)``         -- ``"sha256:" + hex``.
* ``json_digest(obj)``     -- digest of canonical_json(obj), domain-separated.
* ``tree_digest(root)``    -- digest of a directory tree (see TREE_RULES).

TREE_RULES (the canonical candidate-repository encoding):
  - every regular file below ``root`` is included; nothing is excluded;
  - directories themselves are not hashed (empty directories are ignored);
  - symlinks, hard links, devices, FIFOs and sockets are rejected;
  - a path is its components relative to ``root`` joined by "/"; each
    component must be valid UTF-8, NFC-normalised, non-empty, not "." or
    "..", free of "/", "\\", NUL and control characters;
  - two paths equal after case-folding are rejected (case-insensitive file
    systems would otherwise merge them);
  - the only metadata recorded is the executable bit;
  - the digest is sha256 over  b"bendverify-tree-v1\\n"  followed by, for each file
    in bytewise order of its UTF-8 path,
        <path> NUL <"x" if executable else "-"> NUL <sha256 hex of content> "\\n".
"""

from __future__ import annotations

import hashlib
import json
import os
import stat
import unicodedata
from dataclasses import dataclass

TREE_DOMAIN = b"bendverify-tree-v1\n"
JSON_DOMAIN = b"bendverify-json-v1\n"
MAX_TREE_FILES = 20000
MAX_TREE_BYTES = 512 * 1024 * 1024
MAX_PATH_BYTES = 1024


class HashError(Exception):
    """A tree or document violates the canonical encoding rules."""


def digest(data: bytes) -> str:
    return "sha256:" + hashlib.sha256(data).hexdigest()


def _check_json(obj, depth=0):
    if depth > 4096:
        raise HashError("JSON nesting too deep")
    if obj is None or isinstance(obj, bool):
        return
    if isinstance(obj, int):
        return
    if isinstance(obj, float):
        raise HashError("floats are not allowed in canonical JSON")
    if isinstance(obj, str):
        if unicodedata.normalize("NFC", obj) != obj:
            raise HashError("string is not NFC-normalised")
        return
    if isinstance(obj, list):
        for x in obj:
            _check_json(x, depth + 1)
        return
    if isinstance(obj, dict):
        for k, v in obj.items():
            if not isinstance(k, str):
                raise HashError("object keys must be strings")
            _check_json(k, depth + 1)
            _check_json(v, depth + 1)
        return
    raise HashError(f"unsupported JSON value {type(obj).__name__}")


def canonical_json(obj) -> bytes:
    _check_json(obj)
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=False,
                      allow_nan=False).encode("utf-8")


def json_digest(obj) -> str:
    return digest(JSON_DOMAIN + canonical_json(obj))


def file_digest(path: str) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return "sha256:" + h.hexdigest()


def _check_component(c: str) -> None:
    if c in ("", ".", ".."):
        raise HashError(f"illegal path component {c!r}")
    if unicodedata.normalize("NFC", c) != c:
        raise HashError(f"path component not NFC-normalised: {c!r}")
    for ch in c:
        if ch in "/\\\x00" or ord(ch) < 0x20 or ord(ch) == 0x7F:
            raise HashError(f"illegal character in path component {c!r}")


@dataclass(frozen=True)
class TreeEntry:
    path: str          # "/"-joined relative path
    executable: bool
    sha256: str        # "sha256:<hex>"
    size: int


def tree_entries(root: str) -> list[TreeEntry]:
    """Walk ``root`` (never following links) and return canonical entries."""
    if os.path.islink(root) or not os.path.isdir(root):
        raise HashError(f"{root}: not a real directory")
    entries: list[TreeEntry] = []
    folded: dict[str, str] = {}
    total = 0
    stack = [("", root)]
    while stack:
        rel, full = stack.pop()
        with os.scandir(full) as it:
            items = sorted(it, key=lambda e: e.name)
        for e in items:
            try:
                name = e.name
                name.encode("utf-8")
            except UnicodeEncodeError as exc:
                raise HashError(f"non UTF-8 file name under {rel!r}") from exc
            _check_component(name)
            relp = f"{rel}/{name}" if rel else name
            if len(relp.encode("utf-8")) > MAX_PATH_BYTES:
                raise HashError(f"path too long: {relp[:80]}...")
            st = os.lstat(e.path)
            mode = st.st_mode
            if stat.S_ISLNK(mode):
                raise HashError(f"symlink not allowed: {relp}")
            if stat.S_ISDIR(mode):
                stack.append((relp, e.path))
                continue
            if not stat.S_ISREG(mode):
                raise HashError(f"special file not allowed: {relp}")
            if st.st_nlink != 1:
                raise HashError(f"hard link not allowed: {relp}")
            key = relp.casefold()
            if key in folded:
                raise HashError(f"paths collide case-insensitively: {folded[key]} / {relp}")
            folded[key] = relp
            total += st.st_size
            if len(entries) >= MAX_TREE_FILES or total > MAX_TREE_BYTES:
                raise HashError("tree too large")
            entries.append(TreeEntry(relp, bool(mode & 0o111), file_digest(e.path), st.st_size))
    entries.sort(key=lambda t: t.path.encode("utf-8"))
    return entries


def tree_digest_of(entries: list[TreeEntry]) -> str:
    h = hashlib.sha256()
    h.update(TREE_DOMAIN)
    for t in entries:
        h.update(t.path.encode("utf-8") + b"\x00" + (b"x" if t.executable else b"-") + b"\x00"
                 + t.sha256[len("sha256:"):].encode("ascii") + b"\n")
    return "sha256:" + h.hexdigest()


def tree_digest(root: str) -> tuple[str, list[TreeEntry]]:
    entries = tree_entries(root)
    return tree_digest_of(entries), entries


if __name__ == "__main__":  # pragma: no cover - convenience CLI
    import sys
    for p in sys.argv[1:]:
        if os.path.isdir(p):
            print(tree_digest(p)[0], p)
        else:
            print(file_digest(p), p)
