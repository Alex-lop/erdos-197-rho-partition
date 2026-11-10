module

public import Mathlib.Logic.Equiv.Set
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Base

public section

/-!
# Advertised statements

Partial progress on Erdős Problem #197 (<https://www.erdosproblems.com/197>), which remains open.

Erdős #197 asks whether `ℕ` can be split into two sets, each admitting an enumeration (a listing
of order type `ω`) with no monotone 3-term arithmetic progression. A set with such an
enumeration is called *permutable*. The two statements below are Lemma 3.1 (Quarter Lemma) and
Theorem 7.2 of `docs/proof.md`.

**Quarter Lemma (`Erdos197Rho.quarter`).** A linear order of the interval `[α, β]` is given by
an injective ranking `σ` (`x` comes before `y` when `σ x < σ y`); "no monotone 3-term AP" means:
for every 3-term AP `x < y < z` of the interval, `σ y` is not strictly between `σ x` and `σ z`.
Such an order has a *leading parity* `π`: `x` comes before `x + 1` exactly when `x ≡ π (mod 2)`
(hypothesis `hπ`), and a *leading quarter* `Q`: a point `x ≡ π` comes before `x + 2` exactly
when `x ≡ Q (mod 4)` (hypothesis `hQ`). Both exist for every such order (the zigzag lemma,
`Erdos197Rho.phases` in `Erdos197Rho/Basic.lean`). The lemma says that for `β - α ≥ 8` every
point `q ≡ Q (mod 4)` of `[α + 4, β - 4]` comes before every point `z ≢ π (mod 2)` of
`[α + 4, β - 4]`.

**Theorem 7.2 (`Erdos197Rho.main_result`).** For `k ≥ 1` and a real phase `φ`, the *exact
ρ-partition* colours `n ≥ 1` by the parity of `⌊(2k + 1)(log₂ n - φ)⌋`: the runs
`[⌈2 ^ (φ + i / (2k + 1))⌉, ⌈2 ^ (φ + (i + 1) / (2k + 1))⌉)`, `2k + 1` runs per octave, get
alternating colours. Neither colour class (`c = 0`: the even runs; `c = 1`: the odd runs) is
permutable. No assumption is made on the enumeration (no lag hypothesis).

**Encoding.**
* `log₂` is `Real.logb 2`, the floor is `Int.floor`, and `% 2` is `Int.emod`, so
  `⌊(2k + 1)(log₂ n - φ)⌋ % 2 ∈ {0, 1}` also for negative floors; the class of `c` is
  `{n : ℕ | 1 ≤ n ∧ ⌊(2k + 1)(log₂ n - φ)⌋ % 2 = c}`.
* An enumeration of a set `S ⊆ ℕ` is a bijection `f : ℕ ≃ S`, read as the list
  `f 0, f 1, f 2, …`.
* "No monotone 3-term AP" is the predicate `¬HasMonotoneAP (Subtype.val ∘ f) 3` of
  google-deepmind/formal-conjectures (`FormalConjecturesForMathlib/Combinatorics/AP/Basic.lean`),
  written out by unfolding `HasMonotoneAP`, `List.IsAPOfLength` and `List.IsAPOfLengthWith`: no
  strictly increasing list of indices `l` is mapped by `Subtype.val ∘ f` onto `a, a + d, a + 2d`
  or onto `a + 2d, a + d, a`. This is the condition used in formal-conjectures'
  `Erdos197.erdos_197`; writing it out keeps this file Mathlib-only and free of new definitions.
  It is written exactly as in `Erdos197Interval.main_result`
  (<https://github.com/Alex-lop/erdos-197-interval-gadget>); `checks/fidelity.lean` checks by
  `exact` that it agrees with formal-conjectures' predicate.
* `β - 4` is truncated subtraction in `ℕ`; it is the true value since `β ≥ 8`.
-/

/-- **Quarter Lemma.** Let `σ` be an injective ranking of `[α, β]` (`β ≥ α + 8`) without
monotone 3-term APs, with leading parity `π` and leading quarter `Q`. Then every `q ≡ Q (mod 4)`
in `[α + 4, β - 4]` comes before every `z ≢ π (mod 2)` in `[α + 4, β - 4]`. -/
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
    σ q < σ z := by
  sorry

/-- **Theorem 7.2.** For `k ≥ 1`, every real `φ` and `c ∈ {0, 1}`, the colour class
`{n ≥ 1 : ⌊(2k + 1)(log₂ n - φ)⌋ ≡ c (mod 2)}` of the exact ρ-partition has no enumeration
without monotone 3-term arithmetic progressions (formal-conjectures' predicate, unfolded). -/
theorem Erdos197Rho.main_result (k : ℕ) (hk : 1 ≤ k) (φ : ℝ) (c : ℕ) (hc : c < 2) :
    ¬ ∃ f : ℕ ≃ {n : ℕ | 1 ≤ n ∧ (Int.floor ((2 * k + 1) * (Real.logb 2 n - φ))) % 2 = c},
      ¬ ∃ l : List ℕ, (∃ a d : ℕ,
        l.map (Subtype.val ∘ f) = (List.range 3).map (fun n => a + n • d) ∨
          l.map (Subtype.val ∘ f) = (List.range 3).reverse.map (fun n => a + n • d)) ∧
        l.Pairwise (· < ·) := by
  sorry
