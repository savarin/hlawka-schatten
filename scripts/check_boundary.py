#!/usr/bin/env python3
import json
import pathlib
import re
import subprocess
import sys
import tempfile

ALLOWED = ("Lean", "Mathlib", "TauCeti", "CSLib")

def fail(message):
    print(f"FAIL: {message}")
    raise SystemExit(1)

def run(*args):
    p = subprocess.run(args, text=True, capture_output=True)
    if p.returncode:
        print(p.stdout + p.stderr)
        fail("command failed: " + " ".join(args))
    return p.stdout + p.stderr

config = json.loads(pathlib.Path("comparator-existence.json").read_text())
challenge = pathlib.Path("ExistenceChallenge.lean")
solution = pathlib.Path("ExistenceSolution.lean")
if not challenge.is_file() or not solution.is_file():
    fail("ExistenceChallenge.lean or ExistenceSolution.lean missing")
raw = challenge.read_text()
imports = re.findall(r"^import\s+(\S+)", raw, re.MULTILINE)
bad = [x for x in imports if not any(x == r or x.startswith(r + ".") for r in ALLOWED)]
if bad:
    fail(f"disallowed Challenge imports: {bad}")
if len(re.findall(r"\bsorry\b", raw)) != len(config["theorem_names"]):
    fail("Challenge must have exactly one deliberate theorem hole")
if len(raw.splitlines()) > 300:
    fail("Challenge exceeds 300 lines")
run("lake", "env", "lean", "ExistenceChallenge.lean")
run("lake", "env", "lean", "ExistenceSolution.lean")
run("lake", "build", "ExistenceSolution")
with tempfile.NamedTemporaryFile(mode="w", suffix=".lean", dir=".", delete=False) as f:
    f.write("import ExistenceSolution\n")
    for name in config["theorem_names"]:
        f.write(f"#print axioms {name}\n")
    scratch = pathlib.Path(f.name)
try:
    out = run("lake", "env", "lean", str(scratch))
finally:
    scratch.unlink(missing_ok=True)
permitted = set(config["permitted_axioms"])
found = set(re.findall(r"'([^']+)'", out))
unexpected = found - permitted
if unexpected:
    fail(f"unexpected axioms: {sorted(unexpected)}")
print("PASS: Mathlib-only boundary, one theorem hole, Solution builds, axioms permitted")
