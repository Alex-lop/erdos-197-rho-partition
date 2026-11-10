module

public import Solution
public import Mathlib.Algebra.Module.NatInt

public section

section FC

/-! Verbatim copies of the formal-conjectures definitions (commit
5d8b04d3d41b745cc3f2f3cdd5ed04b60c500983,
FormalConjecturesForMathlib/Combinatorics/AP/Basic.lean, lines 36, 51-52, 129-130, 246-247),
at top level as there (Mathlib defines none of these names). -/

variable {α : Type*} [AddCommMonoid α]

def List.IsAPOfLengthWith (s : List α) (l : ℕ) (a d : α) : Prop :=
  s = (List.range l).map (fun n ↦ a + n • d) ∨ s = (List.range l).reverse.map (fun n ↦ a + n • d)

def List.IsAPOfLength (s : List α) (l : ℕ) : Prop :=
  ∃ a d : α, s.IsAPOfLengthWith l a d

def HasMonotoneAP {β : Type*} [Preorder β] (f : β → α) (k : ℕ) : Prop :=
  ∃ l : List β, (l.map f).IsAPOfLength k ∧ l.Pairwise (· < ·)

end FC

/-- Theorem 7.2 restated with the formal-conjectures predicate itself; accepted by `exact`
(definitional unfolding only), so the inlined predicate of `Challenge.lean` is the same
proposition. -/
theorem fc_main (k : ℕ) (hk : 1 ≤ k) (φ : ℝ) (c : ℕ) (hc : c < 2) :
    ¬ ∃ f : ℕ ≃ {n : ℕ | 1 ≤ n ∧ (Int.floor ((2 * k + 1) * (Real.logb 2 n - φ))) % 2 = c},
      ¬HasMonotoneAP (Subtype.val ∘ f) 3 := by
  exact Erdos197Rho.main_result k hk φ c hc

/-- The link with formal-conjectures' `Erdos197.erdos_197`, whose witness would be a pair
`A, B` with `IsCompl A B`, `∃ f : ℕ ≃ A, ¬HasMonotoneAP (Subtype.val ∘ f) 3` and
`∃ g : ℕ ≃ B, ¬HasMonotoneAP (Subtype.val ∘ g) 3`. If the positive integers in `A` are exactly
those of the class `c = 0` of an exact ρ-partition (the point `0` may lie in `A` or in `B`), then
neither enumeration exists, so `A, B` is not a witness. (From `Erdos197Rho.rho_sub`, the superset
form of Theorem 7.2, proved in `Erdos197Rho/Basic.lean`.) -/
theorem fc_erdos197_rho (k : ℕ) (hk : 1 ≤ k) (φ : ℝ) (A B : Set ℕ) (hAB : IsCompl A B)
    (hA : ∀ n : ℕ, 1 ≤ n →
      (n ∈ A ↔ (Int.floor ((2 * k + 1) * (Real.logb 2 n - φ))) % 2 = 0)) :
    (¬ ∃ f : ℕ ≃ A, ¬HasMonotoneAP (Subtype.val ∘ f) 3) ∧
      ¬ ∃ g : ℕ ≃ B, ¬HasMonotoneAP (Subtype.val ∘ g) 3 := by
  refine ⟨fun ⟨f, hf⟩ => Erdos197Rho.rho_sub k hk φ 0 (by norm_num) A
    (fun n hn h => (hA n hn).2 h) f hf, fun ⟨g, hg⟩ => ?_⟩
  refine Erdos197Rho.rho_sub k hk φ 1 (by norm_num) B (fun n hn h => ?_) g hg
  have hn' : n ∈ Aᶜ := fun hnA => by have := (hA n hn).1 hnA; omega
  rwa [hAB.compl_eq] at hn'

#print axioms fc_main
#print axioms fc_erdos197_rho
