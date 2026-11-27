import PublishedCroot
import CatalogSequence

/-! Instantiate both hypotheses of the reduction submitted in LeftToSolve PR #5096. -/

namespace CrootCatalog

open OMA.R_Erdos46_erdos_46_variants_infinitely_many_disjoint_R2

theorem firstBlock : H1 := by
  intro d hd
  let : Finite (Set.range d) := hd
  let color (z : ℤ) : Set.range d := ⟨d z.toNat, z.toNat, rfl⟩
  obtain ⟨s, hs, hsum, a, ha⟩ := CrootBase.erdos_46 color
  refine ⟨s, hs, hsum, ?_⟩
  rintro _ ⟨m, hm, rfl⟩ _ ⟨n, hn, rfl⟩
  simpa [color] using congrArg Subtype.val ((ha m hm).trans (ha n hn).symm)

theorem verified : type_of% @Erdos46.erdos_46.variants.infinitely_many_disjoint :=
  main firstBlock OMA.solution

#print axioms CrootCatalog.firstBlock
#print axioms OMA.solution
#print axioms CrootCatalog.verified

end CrootCatalog
