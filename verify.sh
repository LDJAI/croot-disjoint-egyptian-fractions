#!/usr/bin/env bash
# Run from a checkout of this repository with elan available.
set -euo pipefail
proof_dir=$(cd "$(dirname "$0")" && pwd)
work_dir=$(mktemp -d)
fc_rev=9097e2f90e66d2f6244209cb1c07f7120d17ec53
croot_rev=8822f7ddef30fadbd92e1c6ab4ed897af356af5e

fetch_pin() {
  git init -q "$2"
  git -C "$2" fetch -q --depth=1 "$1" "$3"
  git -C "$2" checkout -q --detach FETCH_HEAD
  test "$(git -C "$2" rev-parse HEAD)" = "$3"
}

fetch_pin https://github.com/google-deepmind/formal-conjectures.git "$work_dir/formal-conjectures" "$fc_rev"
fetch_pin https://github.com/plby/lean-proofs.git "$work_dir/lean-proofs" "$croot_rev"
cd "$work_dir/formal-conjectures"
published="$work_dir/lean-proofs/src/latest"
cp -r "$published/UnitFractions" .
mkdir ErdosProblems
cp "$published/ErdosProblems/Erdos298.lean" ErdosProblems/
# Avoid the name collision with formal-conjectures' statement-only theorem.
sed 's/Erdos46/CrootBase/g' "$published/ErdosProblems/Erdos46.lean" > PublishedCroot.lean
cp "$proof_dir/CrootDisjoint.lean" .
for lib in UnitFractions ErdosProblems PublishedCroot; do
  printf '\n[[lean_lib]]\nname = "%s"\n[lean_lib.leanOptions]\nautoImplicit = true\n' "$lib" >> lakefile.toml
done
lake exe cache get
lake build PublishedCroot FormalConjectures.ErdosProblems.«46»
lake env lean CrootDisjoint.lean | tee "$work_dir/axioms.log"
python3 - "$work_dir/axioms.log" <<'PY'
import pathlib, re, sys
out = pathlib.Path(sys.argv[1]).read_text()
match = re.search(r"'OMA\.solution' depends on axioms: \[([^\]]*)\]", out, re.S)
if not match:
    raise SystemExit("The kernel did not report an axiom audit for OMA.solution")
axioms = {part.strip() for part in match[1].split(",")}
if axioms - {"propext", "Classical.choice", "Quot.sound"}:
    raise SystemExit(f"Unexpected axiom set: {axioms}")
print("Verified the exact LeftToSolve target.")
PY
