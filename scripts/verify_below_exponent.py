#!/usr/bin/env python3
"""Check the below-exponent Solution and a strengthened Challenge against one export."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
CONFIG = "comparator-construction-diagonal-below-exponent.json"
ORIGINAL = "p ≤ Real.log 3 / Real.log (3 / 2) →"
STRONGER = "p ≤ Real.log 3 / Real.log (3 / 2) + 1 →"


def digest(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def seed_names(prefix, config):
    """Read the primitive export roots from the installed Lake used by Comparator."""
    source = prefix / "src/lean/lake/Lake/CLI/Check.lean"
    text = source.read_text().split("def primitiveTargets ", 1)[1].split("\ndef ", 1)[0]
    body = re.sub(r"--[^\n]*", "", text).split("return #[", 1)[1].split("]", 1)[0]
    names = [re.sub(r"^set_option\s+linter\.deprecated\s+false\s+in\s+", "", name.strip())
             for name in body.split(",") if name.strip()]
    if not names or any(not re.fullmatch(r"``[\w.']+", name) for name in names):
        raise ValueError(f"Unrecognized primitive export roots in {source}")
    axioms = config["permitted_axioms"]
    quotient = ["Quot", "Quot.mk", "Quot.lift", "Quot.ind"] if "Quot.sound" in axioms else []
    return [*quotient, *config["theorem_names"], *axioms, *(x[2:] for x in names),
            *config.get("definition_names", [])]


def command_log(args, path, *, cwd=ROOT, env=None, check=True):
    start = time.monotonic()
    with path.open("wb") as output:
        result = subprocess.run(args, stdout=output, stderr=subprocess.STDOUT, cwd=cwd, env=env)
    print(f"{path.name}: exit {result.returncode}, {time.monotonic()-start:.1f} s", flush=True)
    if check and result.returncode:
        raise RuntimeError(f"Command failed. See {path}")
    return result.returncode


def export_module(prefix, name, seeds, output, env, cwd):
    with output.open("wb") as stream, output.with_suffix(".stderr").open("wb") as errors:
        subprocess.run([prefix / "bin/leanexport", name, "--", *seeds], stdout=stream,
                       stderr=errors, cwd=cwd, env=env, check=True)


def lean_environment():
    prefix = Path(subprocess.check_output(["lake", "env", "lean", "--print-prefix"],
                                          cwd=ROOT, text=True).strip()).resolve()
    paths = subprocess.check_output(["lake", "env", "printenv", "LEAN_PATH"], cwd=ROOT, text=True)
    imports = [(ROOT / item).resolve() for item in paths.strip().split(os.pathsep) if item]
    env = dict(os.environ, PATH=os.pathsep.join([str(prefix / "bin"), os.environ["PATH"]]),
               LEAN_PATH=os.pathsep.join(map(str, imports)), LEAN_ABORT_ON_PANIC="1")
    return prefix, imports, env


def make_challenge(out, variant, source, prefix, imports, seeds, env):
    folder = out / variant
    folder.mkdir()
    independent = folder / "IndependentChallenge.lean"
    independent.write_text(source)
    # The standalone Challenge is built against the pinned dependencies and toolchain.
    project_lib = (ROOT / ".lake/build/lib/lean").resolve()
    paths = [folder, *(p for p in imports if p != project_lib)]
    isolated_env = dict(env, LEAN_PATH=os.pathsep.join(map(str, paths)))
    command_log([prefix / "bin/lean", "-R", folder, "-o", folder / "IndependentChallenge.olean",
                 independent], folder / "build.log", cwd=folder, env=isolated_env)
    exported = folder / "challenge.ndjson"
    export_module(prefix, "IndependentChallenge", seeds, exported, isolated_env, folder)
    return exported


def compare_pair(out, config, solution, original, stronger, env, local):
    cfg = out / "comparator-with-nanoda.json"
    # Lake invokes its stock kernel as well as the configured four-thread NanoDa checker.
    cfg.write_text(json.dumps(dict(config, enable_nanoda=True), indent=2) + "\n")
    args = ["lake", "comparator", "--config", str(cfg), "--solution-from-export", str(solution)]
    if local:
        args.append("--inadvisably-no-sandbox")
    baseline = out / "positive.log"
    command_log([*args, "--challenge-from-export", str(original)], baseline, env=env)
    if "Your solution is okay!" not in baseline.read_text().splitlines():
        raise RuntimeError(f"Missing positive Comparator verdict in {baseline}")
    return reject_strengthening(out, args, stronger, config["theorem_names"][0], env)


def reject_strengthening(out, args, stronger, theorem, env):
    log = out / "negative.log"
    code = command_log([*args, "--challenge-from-export", str(stronger)], log, env=env, check=False)
    message = f"error: Challenge and solution theorem statement do not match: '{theorem}'"
    if code != 1 or message not in log.read_text().splitlines():
        raise RuntimeError(f"Expected rejection of the strengthened theorem. See {log}")
    return message


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--config", type=Path, default=ROOT / CONFIG,
                        help="the below-exponent Comparator configuration")
    parser.add_argument("--output", type=Path, help="new directory for exports, logs and the receipt")
    parser.add_argument("--local", action="store_true",
                        help="use Lake's unsandboxed development mode on a trusted checkout")
    args = parser.parse_args()
    out = args.output.resolve() if args.output else Path(tempfile.mkdtemp(prefix="hlawka-below-"))
    if args.output:
        out.mkdir(parents=True, exist_ok=False)
    print(f"Verification artifacts: {out}", flush=True)
    config_path = args.config.resolve()
    config = json.loads(config_path.read_text())
    expected_modules = ("ConstructionDiagonalBelowExponentChallenge", "ConstructionDiagonalBelowExponentSolution")
    if (config["challenge_module"], config["solution_module"]) != expected_modules or config["theorem_names"] != [
        "HlawkaSchatten.LpThreshold.hlawka_holds_below_exponent"
    ]:
        parser.error("The control is specific to the published below-exponent boundary")
    command_log([sys.executable, ROOT / "scripts/check_boundary.py", config_path], out / "boundary.log")
    prefix, imports, env = lean_environment()
    seeds = seed_names(prefix, config)
    source = (ROOT / (config["challenge_module"] + ".lean")).read_text()
    if source.count(ORIGINAL) != 1:
        raise ValueError("Expected exactly one upper-endpoint mutation target")
    original = make_challenge(out, "original", source, prefix, imports, seeds, env)
    stronger = make_challenge(out, "strengthened", source.replace(ORIGINAL, STRONGER),
                              prefix, imports, seeds, env)
    solution = out / "solution.ndjson"
    export_module(prefix, config["solution_module"], seeds, solution, env, ROOT)
    expected = digest(solution)
    rejection = compare_pair(out, config, solution, original, stronger, env, args.local)
    if digest(solution) != expected:
        raise RuntimeError("Solution export changed during verification")
    receipt = {"theorems": config["theorem_names"], "solution_sha256": expected,
               "solution_bytes": solution.stat().st_size, "export_seeds": seeds,
               "challenge_sha256": digest(original), "strengthened_sha256": digest(stronger),
               "permitted_axioms": config["permitted_axioms"], "kernel": "accepted",
               "nanoda": "accepted", "strengthened_rejection": rejection}
    (out / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(f"Verified the published theorem and rejected its strengthening on {expected}.")


if __name__ == "__main__":
    main()
