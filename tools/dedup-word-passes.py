#!/usr/bin/env python3
"""Share structurally identical Word DAG nodes across existing optimizer passes.

Equivalent to GenWordStages' cross-pass cache, for already generated artifacts.
Only literal declarations are factored; all compiler certificates remain checked.
Run without --write to measure. Re-running is idempotent.
"""
import argparse
import json
import re
from pathlib import Path

NODE = re.compile(r"\bword\d+_\d+_\d+\b")
DECL = re.compile(
    r"^def (word\d+_\d+_\d+) : WordLangProgHOL \(BitVec 64\) :=\n"
    r"(.*?)(?=^def |^theorem |^private theorem |^end )", re.M | re.S)
TOKEN = re.compile(r'"(?:\\.|[^"\\])*"|[A-Za-z_][A-Za-z0-9_]*|[0-9]+|[^\s]')
ROOT = Path(__file__).resolve().parents[1]


def rename_nodes(text, mapping):
    # A guest FFI string may contain a name resembling a generated identifier.
    return TOKEN.sub(lambda m: mapping.get(m[0], m[0]) if NODE.fullmatch(m[0]) else m[0], text)


def dedup(label, write=False):
    base = ROOT / "submission/InitECandidate/Proofs/WordStages"
    # Refuse incomplete pipelines before changing any files.
    for index in range(11):
        if not (base / f"Pass{label}_{index}.lean").is_file():
            raise FileNotFoundError(f"Incomplete pass pipeline for function {label}")
    # Intern exact token sequences, rather than trusting a hash of an AST.
    structures, keys, aliases = {}, {}, {}
    before_lines = after_lines = before_bytes = after_bytes = removed = 0
    for index in range(11):
        path = base / f"Pass{label}_{index}.lean"
        original = path.read_text()

        def declaration(match):
            nonlocal removed
            name, body = match.groups()
            structure = rename_nodes(body, keys)
            # Preserve token boundaries, including spaces inside string literals.
            tokens = tuple(TOKEN.findall(structure))
            if tokens in structures:
                key, canonical = structures[tokens]
                keys[name] = f"@{key}"
                aliases[name] = canonical
                removed += 1
                return ""
            key = len(structures)
            structures[tokens] = key, name
            keys[name] = f"@{key}"
            return match[0]

        result = DECL.sub(declaration, original)
        result = rename_nodes(result, aliases)
        before_lines += len(original.splitlines())
        after_lines += len(result.splitlines())
        before_bytes += len(original.encode())
        after_bytes += len(result.encode())
        if write and result != original:
            path.write_text(result)
    return dict(label=label, removed_nodes=removed, before_lines=before_lines,
                after_lines=after_lines, before_bytes=before_bytes, after_bytes=after_bytes)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("labels", type=int, nargs="*")
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    labels = args.labels or sorted(int(re.search(r"Pass(\d+)_0", p.name)[1]) for p in
        (ROOT / "submission/InitECandidate/Proofs/WordStages").glob("Pass*_0.lean"))
    for label in labels:
        print(json.dumps(dedup(label, args.write)), flush=True)
