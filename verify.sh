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
# Fetch the precise review files by commit, then compile them without editing their contents.
raw_fork=https://raw.githubusercontent.com/LDJAI/open-math-agents
reduction_rev=e6dc7663f0dada971031cc846e56fc6cf6dd54d1
sequence_rev=45ee05ce40cea56fa932e2d1e206130fb6c6cd30
catalog_id=Erdos46.erdos_46.variants.infinitely_many_disjoint.R2
reduction_module=R_Erdos46_erdos_46_variants_infinitely_many_disjoint_R2
mkdir -p OMAReductions
curl -fsSL --retry 3 "$raw_fork/$reduction_rev/reductions/$catalog_id.lean" -o "OMAReductions/$reduction_module.lean"
curl -fsSL --retry 3 "$raw_fork/$sequence_rev/proofs/$catalog_id.H2.lean" -o CatalogSequence.lean
cp "$proof_dir/CatalogAssembly.lean" .
for lib in OMAReductions CatalogSequence; do
  printf '\n[[lean_lib]]\nname = "%s"\n' "$lib" >> lakefile.toml
done

lake env lean CrootDisjoint.lean | tee "$work_dir/full.log"
lake build CatalogSequence
lake env lean CatalogAssembly.lean | tee "$work_dir/catalog.log"
python3 - "$work_dir/full.log" "$work_dir/catalog.log" <<'PYTHON'
import pathlib
import re
import sys

allowed = {"propext", "Classical.choice", "Quot.sound"}
for path, names in [(sys.argv[1], ["OMA.solution"]),
                    (sys.argv[2], ["CrootCatalog.firstBlock", "OMA.solution", "CrootCatalog.verified"])]:
    output = pathlib.Path(path).read_text()
    for name in names:
        match = re.search(rf"'{re.escape(name)}' depends on axioms: \[([^\]]*)\]", output, re.S)
        if not match:
            raise SystemExit(f"The kernel did not report an axiom audit for {name}")
        axioms = {part.strip() for part in match[1].split(",")}
        if axioms - allowed:
            raise SystemExit(f"Unexpected axioms in {name}: {axioms - allowed}")
print("Verified the exact LeftToSolve target, both steps, and the assembled reduction.")
PYTHON
