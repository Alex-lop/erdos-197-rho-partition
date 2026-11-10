module

public import Erdos197Rho

public section

/-!
# Proved solution

Comparator checks that the declarations below have exactly the statements of their
counterparts in `Challenge.lean` and use only the permitted axioms. The proofs live in
`Erdos197Rho/Basic.lean`, which builds on the ladder toolkit (`Erdos197Interval.Good.alt`,
`Good.ruleA`, `Good.ruleB`, `Good.par`, `Good.lead_iff`) of `Erdos197Interval/Basic.lean`, a
verbatim copy of the module of <https://github.com/Alex-lop/erdos-197-interval-gadget>.
-/

theorem Erdos197Rho.quarter (α β : ℕ) (hαβ : α + 8 ≤ β) (σ : ℕ → ℕ)
    (hσ : Set.InjOn σ (Set.Icc α β))
    (hAP : ∀ x y z : ℕ, x ∈ Set.Icc α β → z ∈ Set.Icc α β →
      x < y → y < z → y - x = z - y →
        ¬ (σ x < σ y ∧ σ y < σ z) ∧ ¬ (σ z < σ y ∧ σ y < σ x))
    (π Q : ℕ)
    (hπ : ∀ x, α ≤ x → x + 1 ≤ β → (σ x < σ (x + 1) ↔ x % 2 = π))
    (hQ : ∀ x, α ≤ x → x + 2 ≤ β → x % 2 = π → (σ x < σ (x + 2) ↔ x % 4 = Q))
    (q z : ℕ) (hq : q ∈ Set.Icc (α + 4) (β - 4)) (hz : z ∈ Set.Icc (α + 4) (β - 4))
    (hqQ : q % 4 = Q) (hzπ : z % 2 ≠ π) :
    σ q < σ z :=
  Erdos197Rho.quarter_thm α β hαβ σ hσ hAP π Q hπ hQ q z hq hz hqQ hzπ

theorem Erdos197Rho.main_result (k : ℕ) (hk : 1 ≤ k) (φ : ℝ) (c : ℕ) (hc : c < 2) :
    ¬ ∃ f : ℕ ≃ {n : ℕ | 1 ≤ n ∧ (Int.floor ((2 * k + 1) * (Real.logb 2 n - φ))) % 2 = c},
      ¬ ∃ l : List ℕ, (∃ a d : ℕ,
        l.map (Subtype.val ∘ f) = (List.range 3).map (fun n => a + n • d) ∨
          l.map (Subtype.val ∘ f) = (List.range 3).reverse.map (fun n => a + n • d)) ∧
        l.Pairwise (· < ·) :=
  Erdos197Rho.rho_thm k hk φ c hc
