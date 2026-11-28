#!/usr/bin/env python3
"""Reproduce the exact source and axiom audit using Lean 4.34.1."""
from pathlib import Path
import json, os, re, subprocess
root = Path(__file__).resolve().parent
os.chdir(root)
work = root / ".replay"
work.mkdir(exist_ok=True)
out = work / "oleans"
out.mkdir(exist_ok=True)

def run(argv, **kwargs):
    return subprocess.run(argv, check=True, text=True, **kwargs)

def git(path, *args, **kws):
    return subprocess.run(["git", "-C", str(path), *args], text=True, **kws)

def checkout(path, url, rev):
    path.mkdir(parents=True, exist_ok=True)
    if not (path / ".git").exists():
        git(path, "init", "-q", check=True)
    cur = git(path, "rev-parse", "--verify", "HEAD", capture_output=True).stdout.strip()
    if cur and cur != rev:
        raise SystemExit(f"{path}: expected {rev}, found {cur}")
    if not cur:
        git(path, "remote", "remove", "origin", capture_output=True)
        git(path, "remote", "add", "origin", url, check=True)
        git(path, "fetch", "--depth=1", "--no-tags", "origin", rev, check=True)
        git(path, "checkout", "--detach", "FETCH_HEAD", check=True)
    assert git(path, "rev-parse", "HEAD", check=True, capture_output=True).stdout.strip() == rev

ver = run(["lean", "--version"], capture_output=True).stdout.strip()
if not re.match(r"Lean \(version 4\.34\.1,", ver):
    raise SystemExit("Expected Lean 4.34.1, got: " + ver)
print(ver, flush=True)
oai = work / "openai-math"
lemmata = work / "lemmata"
checkout(oai, "https://github.com/openai/math.git", "3344da59991ed94f9ba711217b29c1d760badfa6")
checkout(lemmata, "https://github.com/ZIB-IOL/lemmata.git", "a20ff2d299b36e7357170ddd584eb4e462e95b06")
packages = root / ".lake/packages"
manifest = json.loads((root / "lake-manifest.json").read_text())
for p in manifest["packages"]:
    checkout(packages / p["name"].strip("«»"), p["url"], p["rev"])
fixed = packages / "fixed-point-theorems"
patch = str(root / "fixed-point-theorems-lean4341.patch")
if git(fixed, "apply", "--reverse", "--check", patch, capture_output=True).returncode:
    git(fixed, "apply", "--check", patch, check=True)
    git(fixed, "apply", patch, check=True)
run(["lake", "--no-cache", "exe", "cache", "get", "Mathlib"])
env = dict(os.environ)
env["LEAN_PATH"] = ":".join(map(str, [out, *sorted(packages.glob("*/.lake/build/lib/lean"))]))
seen = set()
def build(name):
    if name in seen:
        return
    seen.add(name)
    base = oai / "lean" if name.startswith("OAI.") else (
        lemmata / "lean" if name.startswith("Lemmata.") else (
        fixed if name.startswith("FixedPointTheorems.") else root / "src"))
    stem = Path(*name.split(".")).with_suffix(".lean")
    src = base / stem
    if not src.is_file():
        if base == root / "src" and name.split(".")[0] in {
            "Mathlib","Lean","Init","Std","Batteries","Qq","Aesop","Cli","Plausible","ProofWidgets"}:
            return
        raise SystemExit(f"Unresolved import: {name}")
    for line in re.findall(r"^(?:(?:public|private|meta) )*import (.+)$", src.read_text(), re.M):
        for dep in line.split("--")[0].split(): build(dep)
    dest = out / stem.with_suffix(".olean")
    dest.parent.mkdir(parents=True, exist_ok=True)
    args = [] if base == root / "src" else ["-DautoImplicit=false"]
    print("Building", name, flush=True)
    run(["lean", "-j1", *args, "--root="+str(base), "-o", str(dest), str(src)], env=env)
audit = (root / "AuditBeyondMaxCut.lean").read_text()
for mod in re.findall(r"^import (\S+)", audit, re.M): build(mod)
result = run(["lean", "-j1", "AuditBeyondMaxCut.lean"], env=env, capture_output=True)
allowed = {"propext", "Classical.choice", "Quot.sound"}
found = re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", result.stdout, re.S)
if [name for name,_ in found] != re.findall(r"^#print axioms (\S+)", audit, re.M):
    raise SystemExit("Audit output did not account for every selected declaration:\n" + result.stdout)
for name, axioms in found:
    extra = set(filter(None, map(str.strip, axioms.split(",")))) - allowed
    if extra:
        raise SystemExit(f"{name}: unexpected axioms: {sorted(extra)}")
(root / "axioms.log").write_text(result.stdout)
print(result.stdout, end="")
