import FormalConjectures.ErdosProblems.«46»
import PublishedCroot

/-!
# Croot's disjoint Egyptian fractions

The finite-color, one-block theorem is Croot's. We use the Lean 4 port
in plby/lean-proofs of the Bloom–Mehta density proof to supply that input.
The argument below upgrades one block to a sequence of disjoint blocks.
-/

open scoped BigOperators

namespace CrootDisjoint

/-- Repeatedly choose a witness above the largest denominator previously used. -/
theorem separated_sequence (P : Finset ℕ → Prop)
    (beyond : ∀ b : ℕ, ∃ s : Finset ℕ, P s ∧ ∀ n ∈ s, b < n) :
    ∃ S : ℕ → Finset ℕ, (∀ i j, i ≠ j → Disjoint (S i) (S j)) ∧ ∀ i, P (S i) := by
  classical
  choose block good above using beyond
  let bound : ℕ → ℕ := Nat.rec 0 (fun _ b => max b ((block b).sup id) + 1)
  have step (i : ℕ) : bound (i + 1) = max (bound i) ((block (bound i)).sup id) + 1 := rfl
  have inc : StrictMono bound := strictMono_nat_of_lt_succ (fun i => by
    rw [step]
    exact Nat.lt_succ_of_le (le_max_left _ _))
  have disj {i j : ℕ} (hij : i < j) : Disjoint (block (bound i)) (block (bound j)) := by
    apply Finset.disjoint_left.mpr
    intro n hi hj
    have hs : n ≤ (block (bound i)).sup id := Finset.le_sup (f := id) hi
    have hbefore : n < bound (i + 1) := by
      rw [step]
      exact Nat.lt_succ_of_le (hs.trans (le_max_right _ _))
    exact (Nat.not_lt_of_ge ((hbefore.le).trans (inc.monotone hij))) (above _ _ hj)
  exact ⟨fun i => block (bound i), fun i j h => (lt_or_gt_of_ne h).elim
    (fun hij => disj hij) (fun hji => (disj hji).symm), fun i => good _⟩

/-- A finite coloring can give every denominator up to a cutoff its own private color.
A singleton denominator at least two cannot have reciprocal sum one. -/
theorem disjoint_of_one
    (oneBlock : ∀ c : ℕ → ℕ, (Set.range c).Finite →
      ∃ s : Finset ℕ, (∀ n ∈ s, 2 ≤ n) ∧ (∑ n ∈ s, (1 / n : ℚ)) = 1 ∧
        (c '' (s : Set ℕ)).Subsingleton)
    (c : ℕ → ℕ) (hc : (Set.range c).Finite) :
    ∃ S : ℕ → Finset ℕ, (∀ i j, i ≠ j → Disjoint (S i) (S j)) ∧
      ∀ i, (∀ n ∈ S i, 2 ≤ n) ∧ (∑ n ∈ S i, (1 / n : ℚ)) = 1 ∧
        (c '' (S i : Set ℕ)).Subsingleton := by
  classical
  apply separated_sequence (fun s => (∀ n ∈ s, 2 ≤ n) ∧
    (∑ n ∈ s, (1 / n : ℚ)) = 1 ∧ (c '' (s : Set ℕ)).Subsingleton)
  intro b
  let d (n : ℕ) := if n ≤ b then n else b + 1 + c n
  have hd : (Set.range d).Finite := by
    apply (((Finset.range (b + 1)).finite_toSet).union (hc.image (fun a => b + 1 + a))).subset
    rintro _ ⟨n, rfl⟩
    by_cases h : n ≤ b
    · exact Or.inl (by simpa [d, h] using Nat.lt_succ_of_le h)
    · exact Or.inr ⟨c n, ⟨n, rfl⟩, by simp [d, h]⟩
  obtain ⟨s, hden, hsum, hmono⟩ := oneBlock d hd
  have same {m n : ℕ} (hm : m ∈ s) (hn : n ∈ s) : d m = d n :=
    hmono ⟨m, hm, rfl⟩ ⟨n, hn, rfl⟩
  have above (n : ℕ) (hn : n ∈ s) : b < n := by
    by_contra! hnlow
    have heq : s = {n} := by
      ext m
      rw [Finset.mem_singleton]
      constructor
      · intro hm
        have h := same hm hn
        by_cases hmlow : m ≤ b
        · simpa [d, hmlow, hnlow] using h
        · simp only [d, if_neg hmlow, if_pos hnlow] at h
          omega
      · rintro rfl
        exact hn
    have hone : (1 : ℚ) / n = 1 := by simpa [heq] using hsum
    have hgt : (1 : ℚ) < n := by exact_mod_cast (hden n hn : 1 < n)
    exact ((div_lt_one (lt_trans zero_lt_one hgt)).2 hgt).ne hone
  refine ⟨s, ⟨hden, hsum, ?_⟩, above⟩
  rintro _ ⟨m, hm, rfl⟩ _ ⟨n, hn, rfl⟩
  have h : b + 1 + c m = b + 1 + c n := by
    simpa only [d, if_neg (above m hm).not_ge, if_neg (above n hn).not_ge] using same hm hn
  omega

end CrootDisjoint

namespace CrootDisjoint
/-- For every finite coloring, infinitely many pairwise disjoint monochromatic
finite sets of denominators at least two have reciprocal sum exactly one. -/
theorem disjoint_from_integer_colors
    (one : ∀ {α : Type} [Finite α] (color : ℤ → α),
       ∃ s : Finset ℕ, (∀ n ∈ s, 2 ≤ n) ∧ (∑ n ∈ s, (1 / n : ℚ)) = 1 ∧
         ∃ a : α, ∀ n ∈ s, color (n : ℤ) = a) (c : ℕ → ℕ) (hc : (Set.range c).Finite) :
    ∃ S : ℕ → Finset ℕ, (∀ i j, i ≠ j → Disjoint (S i) (S j)) ∧
      ∀ i, (∀ n ∈ S i, 2 ≤ n) ∧ (∑ n ∈ S i, (1 / n : ℚ)) = 1 ∧
        (c '' (S i : Set ℕ)).Subsingleton := by
  refine disjoint_of_one ?_ c hc
  intro d hd
  let : Finite (Set.range d) := hd
  let color (z : ℤ) : Set.range d := ⟨d z.toNat, z.toNat, rfl⟩
  obtain ⟨s, hs, hsum, a, ha⟩ := one color
  refine ⟨s, hs, hsum, ?_⟩
  rintro _ ⟨m, hm, rfl⟩ _ ⟨n, hn, rfl⟩
  simpa [color] using congrArg Subtype.val ((ha m hm).trans (ha n hn).symm)

end CrootDisjoint

theorem OMA.solution : type_of% @Erdos46.erdos_46.variants.infinitely_many_disjoint := by
  intro c hc
  refine CrootDisjoint.disjoint_from_integer_colors ?_ c hc
  intro α _ color
  exact CrootBase.erdos_46 color

#print axioms OMA.solution
