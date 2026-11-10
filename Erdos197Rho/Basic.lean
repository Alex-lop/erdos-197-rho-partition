module

public import Erdos197Interval.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

public section

/-!
# The Quarter Lemma and Theorem L\* for the exact ρ-partitions

The proof follows `docs/proof.md`. A linear order of a set is given by an injective ranking
(`x` comes before `y` when `σ x < σ y`), as in `Erdos197Interval/Basic.lean`.

* `quarter_good` (Quarter Lemma = Lemma 3.1, local form): in an order `Good L R σ` of `[L, R]`
  (`R ≥ L + 8`), an interior point `q` with `q ≺ q + 1` and `q ≺ q + 2` precedes every interior
  point `z` with `z + 1 ≺ z`. Two floods: Rule A at `q`, or Rule B and Rule A at a centre
  `c ≡ q + 2 (mod 4)` (`Erdos197Interval.Good.ruleA`, `Good.ruleB`, `Good.alt`, `Good.par`).
* `phases` (zigzag): every such order has a leading parity `π` and a leading quarter `Q`.
  `quarter_thm` is the Quarter Lemma in the residue form of `Challenge.lean`.
* `Adm S ρ`: `ρ` ranks `S` injectively, obeys the midpoint rule on `S`, and only finitely many
  points have a position `≤ N` (order type `ω`). `adm_of_enum` builds it from an enumeration
  `f : ℕ ≃ S` with no monotone 3-term AP (formal-conjectures' predicate, unfolded).
* `anchor` (Lemma 4.1) and `single_anchor` (Lemma 4.2).
* `link` (one step of Theorem L\*): anchors `e, e + 1` before `y`, and `2y - e - 1, 2y - e` in
  the 4-interior of an interval `[α, β] ⊆ S`; then some point of a given 4-window of the
  4-interior comes before `y` (anchor rule plus Quarter Lemma).
* `chain` (Theorem L\* for one anchor pair `e, e + 1` and the bottom windows of a sequence of
  intervals): an infinite descending chain of positions, which is impossible.
* `blink` (Lemma 6.1, B-link), `runs_int` (Theorem 7.2 for integer run boundaries with slivers
  in `{0, 1}` and run lengths tending to infinity), `rho_runs` (the runs of the exact
  ρ-partition, `r j = ⌈2 ^ (φ + j / (2k + 1))⌉`, characterised through `Real.logb 2`), and
  `rho_adm`, `rho_sub`, `rho_thm` (Theorem 7.2).

All arithmetic side conditions are discharged by `omega`; the real analysis is confined to
`rho_runs`.
-/

namespace Erdos197Rho

open Erdos197Interval

variable {L R : ℕ} {σ : ℕ → ℕ}

/-- Four consecutive integers contain one of every residue class mod 4. -/
theorem exists_mod4 (a b : ℕ) : ∃ c, a ≤ c ∧ c ≤ a + 3 ∧ c % 4 = b % 4 :=
  ⟨a + (b + 4 - a % 4) % 4, by omega, by omega, by omega⟩

/-- **Quarter Lemma (Lemma 3.1)**, local form. Let `σ` be an order of `[L, R]` without monotone 3-term
APs, `R ≥ L + 8`. If `q` and `z` lie in `[L + 4, R - 4]`, `q` precedes `q + 1` and `q + 2`, and
`z + 1` precedes `z`, then `q` precedes `z`. -/
theorem quarter_good (hσ : Good L R σ) (hLR : L + 8 ≤ R) {q z : ℕ}
    (hq : L + 4 ≤ q ∧ q + 4 ≤ R) (hz : L + 4 ≤ z ∧ z + 4 ≤ R)
    (hq1 : σ q < σ (q + 1)) (hq2 : σ q < σ (q + 2)) (hz1 : ¬ σ z < σ (z + 1)) :
    σ q < σ z := by
  -- `z` and `q` have different parities (zigzag)
  have hpar : (z + q) % 2 = 1 := by
    by_contra h
    exact hz1 ((hσ.par (x := z) (x₁ := z + 1) (y := q) (y₁ := q + 1) rfl rfl (by omega)
      (by omega) (by omega) (by omega) (by omega)).mpr hq1)
  by_cases h1 : L + z ≤ 2 * q ∧ 2 * q ≤ R + z
  · -- Case 1: `2q - z ∈ [L, R]`; Rule A at `q`
    exact (hσ.ruleA (x := q) (x₁ := q + 1) (w := z) rfl
      ⟨by omega, by omega, h1.1, h1.2, hpar⟩).mpr hq1
  · -- a centre `c ≡ q + 2 (mod 4)` that 2-trails gives `q ≺ c` (Rule B) and `c ≺ z` (Rule A)
    have key : ∀ c, c % 4 = (q + 2) % 4 → L + 2 ≤ c → c + 2 ≤ R →
        L + q ≤ 2 * c → 2 * c ≤ R + q → L + z ≤ 2 * c → 2 * c ≤ R + z →
        ¬ σ c < σ (c + 2) → σ q < σ z := by
      intro c hc hc1 hc2 h3 h4 h5 h6 htr
      have lc : σ c < σ (c + 1) := (hσ.par (x := c) (x₁ := c + 1) (y := q) (y₁ := q + 1) rfl rfl
        (by omega) (by omega) (by omega) (by omega) (by omega)).mpr hq1
      have B := hσ.ruleB (x := c) (x₂ := c + 2) (w := q) rfl ⟨by omega, by omega, h3, h4, by omega⟩
      have A := hσ.ruleA (x := c) (x₁ := c + 1) (w := z) rfl ⟨by omega, by omega, h5, h6, by omega⟩
      have hne := hσ.ne (x := c) (y := q) (by omega)
      have := A.mpr lc
      have : ¬ σ c < σ q := fun h => htr (B.mp h)
      omega
    rcases Nat.lt_or_ge (2 * q) (L + z) with h2 | h2
    · -- Case 2: `z > 2q - L`; the centre lies in `[(z + L) / 2, (R + q) / 2]`, above `q`
      obtain ⟨c, hc1, hc2, hc3⟩ := exists_mod4 ((z + L + 1) / 2) (q + 2)
      refine key c hc3 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) ?_
      -- the rungs `(q + 2, q + 4)` and `(c, c + 2)` of the 2-ladder have the same orientation
      have A := hσ.alt (g := 2) two_pos ((c - (q + 2)) / 4) (q + 2) (q + 4) c (c + 2) (by omega)
        (by omega) rfl (by omega) (by omega)
      have m := hσ.mid q (q + 2) (q + 4) (by omega) (by omega) (by omega) (by omega)
      have n := hσ.ne (x := q) (y := q + 2) (by omega)
      omega
    · -- Case 3: `z < 2q - R`; the centre lies in `[(L + q) / 2, (z + R) / 2]`, below `q`
      obtain ⟨c, hc1, hc2, hc3⟩ := exists_mod4 ((L + q + 1) / 2) (q + 2)
      refine key c hc3 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) ?_
      -- the rungs `(c, c + 2)` and `(q - 2, q)` of the 2-ladder have the same orientation
      have A := hσ.alt (g := 2) two_pos ((q - 2 - c) / 4) c (c + 2) (q - 2) q rfl
        (by omega) (by omega) (by omega) (by omega)
      have m := hσ.mid (q - 2) q (q + 2) (by omega) (by omega) (by omega) (by omega)
      have n := hσ.ne (x := q - 2) (y := q) (by omega)
      omega

/-- **Zigzag** (the phases of `docs/proof.md` §1): every order of `[L, R]` without monotone
3-term APs (`R ≥ L + 8`) has a *leading parity* `π` (the points `x` with `x ≺ x + 1` are those
with `x ≡ π`) and a *leading quarter* `Q` (the points `x ≡ π` with `x ≺ x + 2` are those with
`x ≡ Q (mod 4)`). -/
theorem phases (hσ : Good L R σ) (hLR : L + 8 ≤ R) :
    ∃ π Q : ℕ, (∀ x, L ≤ x → x + 1 ≤ R → (σ x < σ (x + 1) ↔ x % 2 = π)) ∧
      (∀ x, L ≤ x → x + 2 ≤ R → x % 2 = π → (σ x < σ (x + 2) ↔ x % 4 = Q)) := by
  obtain ⟨π, hπ2, hπ⟩ : ∃ π, π < 2 ∧
      ∀ x, L ≤ x → x + 1 ≤ R → (σ x < σ (x + 1) ↔ x % 2 = π) := by
    by_cases h : σ L < σ (L + 1)
    · exact ⟨L % 2, by omega, fun x h1 h2 => by
        have := hσ.lead_iff (by omega) (x := x) (x₁ := x + 1) rfl h1 h2
        omega⟩
    · exact ⟨(L + 1) % 2, by omega, fun x h1 h2 => by
        have := hσ.lead_iff (by omega) (x := x) (x₁ := x + 1) rfl h1 h2
        omega⟩
  obtain ⟨p, hp1, hp2, hpπ⟩ : ∃ p, L ≤ p ∧ p ≤ L + 1 ∧ p % 2 = π := by
    by_cases h : L % 2 = π
    · exact ⟨L, le_rfl, by omega, h⟩
    · exact ⟨L + 1, by omega, le_rfl, by omega⟩
  refine ⟨π, if σ p < σ (p + 2) then p % 4 else (p + 2) % 4, hπ, fun x h1 h2 hx => ?_⟩
  have m := hσ.mid p (p + 2) (p + 4) (by omega) (by omega) (by omega) (by omega)
  have n := hσ.ne (x := p) (y := p + 2) (by omega)
  by_cases hx4 : x % 4 = p % 4
  · have A := hσ.alt (g := 2) two_pos ((x - p) / 4) p (p + 2) x (x + 2) rfl (by omega) rfl
      (by omega) (by omega)
    split_ifs <;> omega
  · have A := hσ.alt (g := 2) two_pos ((x - (p + 2)) / 4) (p + 2) (p + 4) x (x + 2) (by omega)
      (by omega) rfl (by omega) (by omega)
    split_ifs <;> omega

/-- An injective ranking of `[L, R]` without monotone 3-term APs (the hypotheses of
`Erdos197Interval.gadget`) is `Good`. -/
theorem good_of_injOn (hσ : Set.InjOn σ (Set.Icc L R))
    (hAP : ∀ x y z : ℕ, x ∈ Set.Icc L R → z ∈ Set.Icc L R →
      x < y → y < z → y - x = z - y →
        ¬ (σ x < σ y ∧ σ y < σ z) ∧ ¬ (σ z < σ y ∧ σ y < σ x)) :
    Good L R σ := by
  have inj : ∀ x y, L ≤ x → x ≤ R → L ≤ y → y ≤ R → σ x = σ y → x = y :=
    fun x y hx hx' hy hy' h => hσ (Set.mem_Icc.2 ⟨hx, hx'⟩) (Set.mem_Icc.2 ⟨hy, hy'⟩) h
  refine ⟨inj, fun x y z hx hz hxy hxz => ?_⟩
  have h := hAP x y z (Set.mem_Icc.2 ⟨hx, by omega⟩) (Set.mem_Icc.2 ⟨by omega, hz⟩) hxy
    (by omega) (by omega)
  have n₁ : σ y ≠ σ x := fun e => by have := inj y x (by omega) (by omega) hx (by omega) e; omega
  have n₂ : σ y ≠ σ z := fun e => by have := inj y z (by omega) (by omega) (by omega) hz e; omega
  omega

/-- **Quarter Lemma (Lemma 3.1)** (the statement of `Erdos197Rho.quarter` in `Challenge.lean`). -/
theorem quarter_thm (α β : ℕ) (hαβ : α + 8 ≤ β) (σ : ℕ → ℕ)
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
  have hg : Good α β σ := good_of_injOn hσ hAP
  rw [Set.mem_Icc] at hq hz
  -- `q` has the leading parity: otherwise a 1-step or a 2-step of the zigzag is monotone
  have hqπ : q % 2 = π := by
    by_contra h
    have a := hπ q (by omega) (by omega)
    have b := hπ (q + 1) (by omega) (by omega)
    by_cases h' : (q + 1) % 2 = π
    · have c := hQ (q - 1) (by omega) (by omega) (by omega)
      have d := hQ (q + 1) (by omega) (by omega) h'
      rw [show q - 1 + 2 = q + 1 by omega] at c
      have m := hg.mid (q - 1) (q + 1) (q + 1 + 2) (by omega) (by omega) (by omega) (by omega)
      have n := hg.ne (x := q - 1) (y := q + 1) (by omega)
      omega
    · have m := hg.mid q (q + 1) (q + 1 + 1) (by omega) (by omega) (by omega) (by omega)
      have n₁ := hg.ne (x := q) (y := q + 1) (by omega)
      have n₂ := hg.ne (x := q + 1) (y := q + 1 + 1) (by omega)
      omega
  exact quarter_good hg hαβ ⟨hq.1, by omega⟩ ⟨hz.1, by omega⟩
    ((hπ q (by omega) (by omega)).mpr hqπ) ((hQ q (by omega) (by omega) hqπ).mpr hqQ)
    (fun h => hzπ ((hπ z (by omega) (by omega)).mp h))

/-- `ρ` ranks the elements of `S` injectively, obeys the *midpoint rule* on `S` (the middle term
`y` of every 3-term AP `x < y < z` of `S` comes before both ends or after both), and only
finitely many elements of `S` have a position `≤ N`, for every `N` (an order of type `ω`). -/
structure Adm (S : Set ℕ) (ρ : ℕ → ℕ) : Prop where
  inj : ∀ x y, x ∈ S → y ∈ S → ρ x = ρ y → x = y
  mid : ∀ x y z, x ∈ S → y ∈ S → z ∈ S → x < y → x + z = 2 * y → (ρ y < ρ x ↔ ρ y < ρ z)
  fin : ∀ N, ∃ B, ∀ x, x ∈ S → ρ x ≤ N → x ≤ B

/-- The positions `f.symm` of an enumeration `f : ℕ ≃ S` with no monotone 3-term AP
(formal-conjectures' predicate, unfolded) form an admissible ranking of `S`. -/
theorem adm_of_enum (S : Set ℕ) (f : ℕ ≃ S)
    (hf : ¬ ∃ l : List ℕ, (∃ a d : ℕ,
        l.map (Subtype.val ∘ f) = (List.range 3).map (fun n => a + n • d) ∨
          l.map (Subtype.val ∘ f) = (List.range 3).reverse.map (fun n => a + n • d)) ∧
        l.Pairwise (· < ·)) :
    ∃ ρ : ℕ → ℕ, Adm S ρ := by
  classical
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℕ → ℕ, ∀ x (hx : x ∈ S), ρ x = f.symm ⟨x, hx⟩ :=
    ⟨fun x => if hx : x ∈ S then f.symm ⟨x, hx⟩ else 0, fun x hx => by simp [hx]⟩
  have hfρ : ∀ x, x ∈ S → (f (ρ x) : ℕ) = x := fun x hx => by simp [hρ x hx]
  have inj : ∀ x y, x ∈ S → y ∈ S → ρ x = ρ y → x = y := fun x y hx hy h => by
    rw [← hfρ x hx, ← hfρ y hy, h]
  refine ⟨ρ, ⟨inj, fun x y z hx hy hz hxy hxz => ?_, fun N => ?_⟩⟩
  · have ex := hfρ x hx
    have ey := hfρ y hy
    have ez := hfρ z hz
    have n₁ : ρ y ≠ ρ x := fun e => by have := inj y x hy hx e; omega
    have n₂ : ρ y ≠ ρ z := fun e => by have := inj y z hy hz e; omega
    constructor
    · intro h
      by_contra h'
      exact no_ap hf (p := ρ z) (q := ρ y) (r := ρ x) (by omega) h
        (by simp only [Function.comp_apply, ex, ey, ez]; omega)
    · intro h
      by_contra h'
      exact no_ap hf (p := ρ x) (q := ρ y) (r := ρ z) (by omega) h
        (by simp only [Function.comp_apply, ex, ey, ez]; omega)
  · -- everything listed at positions `≤ N` is at most `B`
    have key : ∀ N, ∃ B, ∀ i, i ≤ N → (f i : ℕ) ≤ B := by
      intro N
      induction N with
      | zero => exact ⟨f 0, fun i hi => by rw [show i = 0 by omega]⟩
      | succ N ih =>
        obtain ⟨B, hB⟩ := ih
        refine ⟨max B (f (N + 1)), fun i hi => ?_⟩
        rcases Nat.lt_or_ge i (N + 1) with h | h
        · exact le_max_of_le_left (hB i (by omega))
        · obtain rfl : i = N + 1 := by omega
          exact le_max_right _ _
    obtain ⟨B, hB⟩ := key N
    exact ⟨B, fun x hx hxN => by rw [← hfρ x hx]; exact hB _ hxN⟩

variable {S : Set ℕ} {ρ : ℕ → ℕ}

/-- An admissible ranking of `S` restricts to an order of every interval `[α, β] ⊆ S`. -/
theorem good_of_adm (hρ : Adm S ρ) {α β : ℕ} (hI : ∀ x, α ≤ x → x ≤ β → x ∈ S) :
    Good α β ρ :=
  ⟨fun x y h1 h2 h3 h4 h => hρ.inj x y (hI x h1 h2) (hI y h3 h4) h,
    fun x y z h1 h2 h3 h4 => hρ.mid x y z (hI x h1 (by omega)) (hI y (by omega) (by omega))
      (hI z (by omega) h2) h3 h4⟩

/-- **Lemma 4.1 (anchor).** If `a ≺ w` and `z = 2w - a ∈ S` with `a < w`, then `z ≺ w`:
otherwise `a ≺ w ≺ z` is a monotone 3-term AP. -/
theorem anchor (hρ : Adm S ρ) {a w z : ℕ} (ha : a ∈ S) (hw : w ∈ S) (hz : z ∈ S) (haw : a < w)
    (hawz : a + z = 2 * w) (h : ρ a < ρ w) : ρ z < ρ w := by
  have m := hρ.mid a w z ha hw hz haw hawz
  have n : ρ z ≠ ρ w := fun e => by have := hρ.inj z w hz hw e; omega
  omega

/-- **Lemma 4.2 (single anchor).** Let `[α, β] ⊆ S` with `β ≥ α + 8`, let `y` lie in the
leading quarter of `ρ` on `[α, β]` (`y ≺ y + 1` and `y ≺ y + 2`), and let `t ∈ S` be such that
`z = 2y - t` has the trailing parity (`z + 1 ≺ z`), with `y, z ∈ [α + 4, β - 4]`. Then `y ≺ t`.
(Not needed for Theorem 7.2; it is the step behind Corollary Q of the working notes.) -/
theorem single_anchor (hρ : Adm S ρ) {α β y t z : ℕ} (hI : ∀ x, α ≤ x → x ≤ β → x ∈ S)
    (hαβ : α + 8 ≤ β) (ht : t ∈ S) (htz : t + z = 2 * y)
    (hy : α + 4 ≤ y ∧ y + 4 ≤ β) (hz : α + 4 ≤ z ∧ z + 4 ≤ β)
    (hy1 : ρ y < ρ (y + 1)) (hy2 : ρ y < ρ (y + 2)) (hz1 : ¬ ρ z < ρ (z + 1)) :
    ρ y < ρ t := by
  have hq := quarter_good (good_of_adm hρ hI) hαβ hy hz hy1 hy2 hz1
  have hyS := hI y (by omega) (by omega)
  have hzS := hI z (by omega) (by omega)
  rcases lt_trichotomy t y with h | h | h
  · -- `t < y < z`: if `t ≺ y`, the anchor rule gives `z ≺ y`, against `y ≺ z`
    by_contra hc
    have hne : ρ t ≠ ρ y := fun e => by have := hρ.inj t y ht hyS e; omega
    have := anchor hρ ht hyS hzS h htz (by omega)
    omega
  · -- `t = y` forces `z = y`, against `y ≺ z`
    subst h
    obtain rfl : z = t := by omega
    exact absurd hq (lt_irrefl _)
  · -- `z < y < t`: the midpoint rule turns `y ≺ z` into `y ≺ t`
    exact (hρ.mid z y t hzS hyS ht (by omega) (by omega)).mp hq

/-- **One link of Theorem L\*** (`docs/proof.md` Lemma 5.1). Let the
anchors `e, e + 1 ∈ S` come before `y ∈ S` (`e + 1 < y`), let `[α, β] ⊆ S` contain
`2y - e - 1` and `2y - e` in its 4-interior, and let `[w, w + 3]` lie in its 4-interior. Then some
point of `[w, w + 3]` comes before `y`. -/
theorem link (hρ : Adm S ρ) {e y α β w : ℕ} (he : e ∈ S) (he1 : e + 1 ∈ S) (hy : y ∈ S)
    (hey : e + 1 < y) (h0 : ρ e < ρ y) (h1 : ρ (e + 1) < ρ y)
    (hI : ∀ x, α ≤ x → x ≤ β → x ∈ S)
    (hz1 : α + 4 + e + 1 ≤ 2 * y) (hz2 : 2 * y + 4 ≤ β + e)
    (hw1 : α + 4 ≤ w) (hw2 : w + 7 ≤ β) :
    ∃ y', w ≤ y' ∧ y' ≤ w + 3 ∧ ρ y' < ρ y := by
  have hg : Good α β ρ := good_of_adm hρ hI
  -- the anchor `t ∈ {e, e + 1}` whose reflection `z = 2y - t` has the trailing parity
  obtain ⟨t, z, ht, htz, hz, hztr⟩ : ∃ t z, (t = e ∨ t = e + 1) ∧ t + z = 2 * y ∧
      (α + 4 ≤ z ∧ z + 4 ≤ β) ∧ ¬ ρ z < ρ (z + 1) := by
    have l₀ := hg.lead_iff (by omega) (x := 2 * y - e) (x₁ := 2 * y - e + 1) rfl (by omega)
      (by omega)
    have l₁ := hg.lead_iff (by omega) (x := 2 * y - (e + 1)) (x₁ := 2 * y - (e + 1) + 1) rfl
      (by omega) (by omega)
    by_cases h : ρ (2 * y - e) < ρ (2 * y - e + 1)
    · exact ⟨e + 1, 2 * y - (e + 1), Or.inr rfl, by omega, ⟨by omega, by omega⟩, by omega⟩
    · exact ⟨e, 2 * y - e, Or.inl rfl, by omega, ⟨by omega, by omega⟩, h⟩
  -- the anchor rule at `(t, y, z)`: `z ≺ y`
  have htS : t ∈ S := by rcases ht with rfl | rfl <;> assumption
  have hzS : z ∈ S := hI z (by omega) (by omega)
  have hty : ρ t < ρ y := by rcases ht with rfl | rfl <;> assumption
  have hzy : ρ z < ρ y := anchor hρ htS hy hzS (by omega) htz hty
  -- a point `y'` of the leading quarter in `[w, w + 3]`
  obtain ⟨y', hy'1, hy'2, hl1, hl2⟩ : ∃ y', w ≤ y' ∧ y' ≤ w + 3 ∧ ρ y' < ρ (y' + 1) ∧
      ρ y' < ρ (y' + 2) := by
    obtain ⟨u, hu1, hu2, hu⟩ : ∃ u, w ≤ u ∧ u ≤ w + 1 ∧ ρ u < ρ (u + 1) := by
      by_cases h : ρ w < ρ (w + 1)
      · exact ⟨w, le_rfl, by omega, h⟩
      · refine ⟨w + 1, by omega, le_rfl, ?_⟩
        have m := hg.mid w (w + 1) (w + 1 + 1) (by omega) (by omega) (by omega) (by omega)
        have n := hg.ne (x := w) (y := w + 1) (by omega)
        omega
    have hpar := hg.par (x := u) (x₁ := u + 1) (y := u + 2) (y₁ := u + 2 + 1) rfl rfl (by omega)
      (by omega) (by omega) (by omega) (by omega)
    by_cases h : ρ u < ρ (u + 2)
    · exact ⟨u, hu1, by omega, hu, h⟩
    · refine ⟨u + 2, by omega, by omega, hpar.mp hu, ?_⟩
      have m := hg.mid u (u + 2) (u + 2 + 2) (by omega) (by omega) (by omega) (by omega)
      have n := hg.ne (x := u) (y := u + 2) (by omega)
      omega
  -- the Quarter Lemma in `[α, β]`: `y' ≺ z`
  have hq := quarter_good hg (by omega) ⟨by omega, by omega⟩ hz hl1 hl2 hztr
  exact ⟨y', hy'1, hy'2, by omega⟩

/-- **Theorem L\*** (`docs/proof.md` Theorem 5.2) for one anchor pair `e, e + 1 ∈ S` and the
intervals `[a m, b m] ⊆ S` with windows `[a m + 4, a m + 7]`: if `a m ≥ m`, `b m ≥ a m + 11`
and `2 [a m + 4, a m + 7] - {e, e + 1} ⊆ [a (m + 1) + 4, b (m + 1) - 4]` for every `m`, then `S`
has no admissible ranking of type `ω`. -/
theorem chain (hρ : Adm S ρ) {e : ℕ} (he : e ∈ S) (he1 : e + 1 ∈ S) (a b : ℕ → ℕ)
    (hI : ∀ m x, a m ≤ x → x ≤ b m → x ∈ S) (hgrow : ∀ m, m ≤ a m)
    (hlen : ∀ m, a m + 11 ≤ b m)
    (hlo : ∀ m, a (m + 1) + e + 5 ≤ 2 * a m + 8)
    (hhi : ∀ m, 2 * a m + 18 ≤ b (m + 1) + e) : False := by
  -- every point above `B` comes after both anchors
  obtain ⟨B, hB⟩ := hρ.fin (ρ e + ρ (e + 1))
  have hBe : e + 1 ≤ B := hB (e + 1) he1 (by omega)
  have late : ∀ x, x ∈ S → B < x → ρ e < ρ x ∧ ρ (e + 1) < ρ x := by
    intro x hx hBx
    by_contra h
    have := hB x hx (by omega)
    omega
  -- the positions of the chosen window points drop by at least one per link
  have desc : ∀ n, ∃ y, a (B + 1 + n) + 4 ≤ y ∧ y ≤ a (B + 1 + n) + 7 ∧
      ρ y + n ≤ ρ (a (B + 1 + 0) + 4) := by
    intro n
    induction n with
    | zero => exact ⟨a (B + 1 + 0) + 4, le_rfl, by omega, by omega⟩
    | succ n ih =>
      obtain ⟨y, hy1, hy2, hy3⟩ := ih
      have hl := hlen (B + 1 + n)
      have hl' := hlen (B + 1 + n + 1)
      have hg := hgrow (B + 1 + n)
      have ho := hlo (B + 1 + n)
      have hh := hhi (B + 1 + n)
      have hyS : y ∈ S := hI (B + 1 + n) y (by omega) (by omega)
      have hy := late y hyS (by omega)
      obtain ⟨y', h1, h2, h3⟩ := link hρ he he1 hyS (by omega) hy.1 hy.2
        (hI (B + 1 + n + 1)) (by omega) (by omega) (w := a (B + 1 + n + 1) + 4) le_rfl
        (by omega)
      rw [show B + 1 + (n + 1) = B + 1 + n + 1 by omega]
      exact ⟨y', h1, h2, by omega⟩
  obtain ⟨y, -, -, hy⟩ := desc (ρ (a (B + 1 + 0) + 4) + 1)
  omega

/-- **Lemma 6.1 (B-link)**, in integers. Let the run `J_i = [a, a' - 1]` have length
`a' - a ≥ 12` and let `J_{i+K-1} = [p, s - 1]` (so `s = r_{i+K}`). If the sliver `δ = 2a - s`
satisfies `e - 3 - (s - p) ≤ δ ≤ e - 19` (written `p + e ≤ 2a + 3` and `2a + 19 ≤ s + e`), then
the window `W = [a + 4, a + 7]` lies in the 4-interior of `J_i`, and `2y - t` lies in the
4-interior `[p + 4, s - 5]` of `J_{i+K-1}` for all `y ∈ W` and `t ∈ {e, e + 1}`. -/
theorem blink {a a' p s e : ℕ} (hlen : a + 12 ≤ a') (hδ1 : 2 * a + 19 ≤ s + e)
    (hδ2 : p + e ≤ 2 * a + 3) :
    a + 7 ≤ a' - 1 - 4 ∧ ∀ y t, a + 4 ≤ y → y ≤ a + 7 → e ≤ t → t ≤ e + 1 →
      p + 4 ≤ 2 * y - t ∧ 2 * y - t ≤ s - 1 - 4 :=
  ⟨by omega, fun y t h1 h2 h3 h4 => ⟨by omega, by omega⟩⟩

/-- **Theorem 7.2, integer core.** Let `k ≥ 1`, and let `r : ℕ → ℕ` be run boundaries with
slivers `δ j = 2 r j - r (j + 2k + 1) ∈ {0, 1}` and run lengths `r (j + 1) - r j → ∞`. If `S`
contains every run `[r j, r (j + 1))` with `j ≡ c (mod 2)`, then `S` has no admissible ranking of
type `ω`. The anchors are `e = r j₁, e + 1` (one run of colour `c`, `e ≥ 20`); the chain is the
runs `J (i₀ + 2k m)` with the B-link of Lemma 6.1, windows `[r i + 4, r i + 7]`. -/
theorem runs_int (k : ℕ) (hk : 1 ≤ k) (r : ℕ → ℕ) (c : ℕ) (hc : c < 2)
    (mem : ∀ j n, j % 2 = c → r j ≤ n → n < r (j + 1) → n ∈ S)
    (dbl : ∀ j, r (j + 2 * k + 1) ≤ 2 * r j ∧ 2 * r j ≤ r (j + 2 * k + 1) + 1)
    (gap : ∀ G, ∃ j₀, ∀ j, j₀ ≤ j → r j + G ≤ r (j + 1))
    (hρ : Adm S ρ) : False := by
  -- the anchors `e = r j₁` and `e + 1`, in a run of colour `c`, with `e ≥ 20`
  obtain ⟨j₀, hj₀⟩ := gap 20
  obtain ⟨j₁, hj₁a, hj₁b⟩ : ∃ j₁, j₀ + 1 ≤ j₁ ∧ j₁ % 2 = c :=
    ⟨j₀ + 1 + (j₀ + 1 + c) % 2, by omega, by omega⟩
  have hea := hj₀ (j₁ - 1) (by omega)
  rw [show j₁ - 1 + 1 = j₁ by omega] at hea
  have heb := hj₀ j₁ (by omega)
  obtain ⟨e, he⟩ : ∃ e, e = r j₁ := ⟨_, rfl⟩
  have heS : e ∈ S := mem j₁ e hj₁b (by omega) (by omega)
  have he1S : e + 1 ∈ S := mem j₁ (e + 1) hj₁b (by omega) (by omega)
  -- the chain of runs `J (i₀ + 2k m)`, all of colour `c`, all of length `≥ e + 12`
  obtain ⟨j₂, hj₂⟩ := gap (e + 12)
  obtain ⟨i₀, hi₀a, hi₀b⟩ : ∃ i₀, j₂ ≤ i₀ ∧ i₀ % 2 = c :=
    ⟨j₂ + (j₂ + c) % 2, by omega, by omega⟩
  have up : ∀ t, t ≤ r (i₀ + t) := by
    intro t
    induction t with
    | zero => omega
    | succ t ih =>
      have := hj₂ (i₀ + t) (by omega)
      rw [show i₀ + (t + 1) = i₀ + t + 1 by omega]
      omega
  have shift : ∀ m, i₀ + 2 * (k * (m + 1)) = i₀ + 2 * (k * m) + 2 * k := fun m => by ring
  refine chain hρ heS he1S (fun m => r (i₀ + 2 * (k * m))) (fun m => r (i₀ + 2 * (k * m) + 1) - 1)
    (fun m n h1 h2 => ?_) (fun m => ?_) (fun m => ?_) (fun m => ?_) (fun m => ?_)
  · have := hj₂ (i₀ + 2 * (k * m)) (by omega)
    exact mem (i₀ + 2 * (k * m)) n (by omega) h1 (by omega)
  · have h1 := up (2 * (k * m))
    have h2 : m ≤ k * m := Nat.le_mul_of_pos_left m hk
    show m ≤ r (i₀ + 2 * (k * m))
    omega
  · have := hj₂ (i₀ + 2 * (k * m)) (by omega)
    show r (i₀ + 2 * (k * m)) + 11 ≤ r (i₀ + 2 * (k * m) + 1) - 1
    omega
  -- the B-link of Lemma 6.1 from `J i` to `J (i + 2k)`, `i = i₀ + 2km`: `δ i ∈ {0, 1}`,
  -- `e ≥ 20` and `ℓ (i + 2k) ≥ e + 12`
  · show r (i₀ + 2 * (k * (m + 1))) + e + 5 ≤ 2 * r (i₀ + 2 * (k * m)) + 8
    rw [shift]
    have h1 := hj₂ (i₀ + 2 * (k * m) + 2 * k) (by omega)
    have h2 := dbl (i₀ + 2 * (k * m))
    have h3 := hj₂ (i₀ + 2 * (k * m)) (by omega)
    have := ((blink (a := r (i₀ + 2 * (k * m))) (a' := r (i₀ + 2 * (k * m) + 1))
      (p := r (i₀ + 2 * (k * m) + 2 * k)) (s := r (i₀ + 2 * (k * m) + 2 * k + 1)) (e := e)
      (by omega) (by omega) (by omega)).2 (r (i₀ + 2 * (k * m)) + 4) (e + 1)
      le_rfl (by omega) (by omega) le_rfl).1
    omega
  · show 2 * r (i₀ + 2 * (k * m)) + 18 ≤ r (i₀ + 2 * (k * (m + 1)) + 1) - 1 + e
    rw [shift]
    have h1 := hj₂ (i₀ + 2 * (k * m) + 2 * k) (by omega)
    have h2 := dbl (i₀ + 2 * (k * m))
    have h3 := hj₂ (i₀ + 2 * (k * m)) (by omega)
    have := ((blink (a := r (i₀ + 2 * (k * m))) (a' := r (i₀ + 2 * (k * m) + 1))
      (p := r (i₀ + 2 * (k * m) + 2 * k)) (s := r (i₀ + 2 * (k * m) + 2 * k + 1)) (e := e)
      (by omega) (by omega) (by omega)).2 (r (i₀ + 2 * (k * m)) + 7) e
      (by omega) le_rfl le_rfl (by omega)).2
    omega

/-- **The runs of the exact ρ-partition** (`docs/proof.md` Lemma 7.1).
Let `K = 2k + 1` and `r j = ⌈2 ^ (φ + j / K)⌉₊` for `j : ℕ`. Then
* for `n ≥ 1`: `⌊K (log₂ n - φ)⌋ = j` iff `r j ≤ n < r (j + 1)` (the run `J j`);
* `r j ≥ 1`;
* the slivers `2 r j - r (j + K)` lie in `{0, 1}`;
* the run lengths `r (j + 1) - r j` tend to infinity. -/
theorem rho_runs (k : ℕ) (φ : ℝ) :
    ∃ r : ℕ → ℕ, (∀ j, r j = ⌈(2 : ℝ) ^ (φ + (j : ℝ) / (2 * k + 1))⌉₊) ∧
      (∀ j n : ℕ, 1 ≤ n →
        (Int.floor ((2 * k + 1) * (Real.logb 2 n - φ)) = j ↔ r j ≤ n ∧ n < r (j + 1))) ∧
      (∀ j, 1 ≤ r j) ∧
      (∀ j, r (j + 2 * k + 1) ≤ 2 * r j ∧ 2 * r j ≤ r (j + 2 * k + 1) + 1) ∧
      (∀ G, ∃ j₀, ∀ j, j₀ ≤ j → r j + G ≤ r (j + 1)) := by
  have hK : (0 : ℝ) < 2 * k + 1 := by positivity
  obtain ⟨x, hx⟩ : ∃ x : ℕ → ℝ, ∀ j, x j = (2 : ℝ) ^ (φ + (j : ℝ) / (2 * k + 1)) :=
    ⟨_, fun _ => rfl⟩
  have hpos : ∀ j, 0 < x j := fun j => by rw [hx]; exact Real.rpow_pos_of_pos two_pos _
  -- `x (j + 1) = x j · 2 ^ (1 / K)` and `x (j + K) = 2 x j`
  have hstep : ∀ j, x (j + 1) = x j * 2 ^ ((1 : ℝ) / (2 * k + 1)) := by
    intro j
    rw [hx, hx, ← Real.rpow_add two_pos]
    congr 1
    push_cast
    ring
  have hdouble : ∀ j, x (j + 2 * k + 1) = 2 * x j := by
    intro j
    rw [hx, hx]
    have e : φ + ((j + 2 * k + 1 : ℕ) : ℝ) / (2 * k + 1) = (φ + (j : ℝ) / (2 * k + 1)) + 1 := by
      push_cast
      field_simp
      ring
    rw [e, Real.rpow_add two_pos, Real.rpow_one, mul_comm]
  have hmono : ∀ i j, i ≤ j → x i ≤ x j := by
    intro i j h
    rw [hx, hx]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have : (i : ℝ) ≤ j := by exact_mod_cast h
    have := div_le_div_of_nonneg_right this hK.le
    linarith
  have hpow : ∀ M : ℕ, x ((2 * k + 1) * M) = 2 ^ M * x 0 := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      rw [show (2 * k + 1) * (M + 1) = (2 * k + 1) * M + 2 * k + 1 by ring, hdouble, ih, pow_succ]
      ring
  have hθ : (1 : ℝ) < 2 ^ ((1 : ℝ) / (2 * k + 1)) := Real.one_lt_rpow (by norm_num) (by positivity)
  -- the gaps `x (j + 1) - x j = x j (2 ^ (1 / K) - 1)` tend to infinity
  have hgap : ∀ T : ℝ, ∃ j₀, ∀ j, j₀ ≤ j → x j + T ≤ x (j + 1) := by
    intro T
    have hd : 0 < x 0 * (2 ^ ((1 : ℝ) / (2 * k + 1)) - 1) := mul_pos (hpos 0) (by linarith)
    obtain ⟨M, hM⟩ := exists_nat_ge (T / (x 0 * (2 ^ ((1 : ℝ) / (2 * k + 1)) - 1)))
    refine ⟨(2 * k + 1) * M, fun j hj => ?_⟩
    have hT : T ≤ M * (x 0 * (2 ^ ((1 : ℝ) / (2 * k + 1)) - 1)) := (div_le_iff₀ hd).mp hM
    have hM2 : (M : ℝ) ≤ 2 ^ M := by exact_mod_cast (Nat.lt_two_pow_self).le
    have hxj : 2 ^ M * x 0 ≤ x j := hpow M ▸ hmono _ _ hj
    have e1 := mul_le_mul_of_nonneg_right hxj
      (by linarith : (0 : ℝ) ≤ 2 ^ ((1 : ℝ) / (2 * k + 1)) - 1)
    have e2 := mul_le_mul_of_nonneg_right hM2 hd.le
    rw [hstep j]
    nlinarith
  refine ⟨fun j => ⌈x j⌉₊, fun j => by show ⌈x j⌉₊ = _; rw [hx], fun j n hn => ?_, fun j => ?_, fun j => ?_,
    fun G => ?_⟩
  · -- the runs: `⌊K (log₂ n - φ)⌋ = j ↔ x j ≤ n < x (j + 1)`
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have aux : ∀ y : ℝ, ((j : ℝ) ≤ (2 * k + 1) * y ↔ (j : ℝ) / (2 * k + 1) ≤ y) ∧
        ((2 * k + 1) * y < (j : ℝ) + 1 ↔ y < ((j : ℝ) + 1) / (2 * k + 1)) := fun y =>
      ⟨by rw [div_le_iff₀ hK, mul_comm], by rw [lt_div_iff₀ hK, mul_comm]⟩
    dsimp only
    rw [Int.floor_eq_iff, Nat.ceil_le, Nat.lt_ceil, hx, hx,
      ← Real.le_logb_iff_rpow_le one_lt_two hn', ← Real.logb_lt_iff_lt_rpow one_lt_two hn']
    push_cast
    rw [(aux _).1, (aux _).2]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  · exact Nat.one_le_ceil_iff.mpr (hpos j)
  · -- the slivers: `⌈2 x⌉ ∈ {2 ⌈x⌉ - 1, 2 ⌈x⌉}`
    have e : ⌈x (j + 2 * k + 1)⌉₊ = ⌈2 * x j⌉₊ := by rw [hdouble]
    have h1 := Nat.le_ceil (x j)
    have h2 := Nat.ceil_lt_add_one (hpos j).le
    have h3 := Nat.le_ceil (2 * x j)
    dsimp only
    rw [e]
    constructor
    · exact Nat.ceil_le.mpr (by push_cast; linarith)
    · have h4 : ((2 * ⌈x j⌉₊ : ℕ) : ℝ) < ((⌈2 * x j⌉₊ + 2 : ℕ) : ℝ) := by push_cast; linarith
      have := Nat.cast_lt.mp h4
      omega
  · -- the run lengths
    obtain ⟨j₀, hj₀⟩ := hgap (G + 1)
    refine ⟨j₀, fun j hj => ?_⟩
    have h1 := hj₀ j hj
    have h2 := Nat.ceil_lt_add_one (hpos j).le
    have h3 := Nat.le_ceil (x (j + 1))
    have h4 : ((⌈x j⌉₊ + G : ℕ) : ℝ) < ((⌈x (j + 1)⌉₊ : ℕ) : ℝ) := by push_cast; linarith
    have := Nat.cast_lt.mp h4
    dsimp only
    omega

/-- **Theorem 7.2** for an admissible ranking of any set `S` containing the colour class `c` of
the exact ρ-partition with `K = 2k + 1` runs per octave and phase `φ`. -/
theorem rho_adm (k : ℕ) (hk : 1 ≤ k) (φ : ℝ) (c : ℕ) (hc : c < 2) (S : Set ℕ)
    (hS : ∀ n : ℕ, 1 ≤ n → (Int.floor ((2 * k + 1) * (Real.logb 2 n - φ))) % 2 = c → n ∈ S)
    (hρ : Adm S ρ) : False := by
  obtain ⟨r, -, hrun, hr1, hdbl, hgap⟩ := rho_runs k φ
  refine runs_int k hk r c hc (fun j n hj h1 h2 => ?_) hdbl hgap hρ
  have hn : 1 ≤ n := (hr1 j).trans h1
  refine hS n hn ?_
  rw [(hrun j n hn).mpr ⟨h1, h2⟩]
  omega

/-- Superset form of **Theorem 7.2**: a set `S ⊆ ℕ` containing the colour class `c` of the
exact ρ-partition (`k ≥ 1`, any phase `φ`) has no enumeration without monotone 3-term APs
(formal-conjectures' predicate, unfolded). -/
theorem rho_sub (k : ℕ) (hk : 1 ≤ k) (φ : ℝ) (c : ℕ) (hc : c < 2) (S : Set ℕ)
    (hS : ∀ n : ℕ, 1 ≤ n → (Int.floor ((2 * k + 1) * (Real.logb 2 n - φ))) % 2 = c → n ∈ S)
    (f : ℕ ≃ S)
    (hf : ¬ ∃ l : List ℕ, (∃ a d : ℕ,
        l.map (Subtype.val ∘ f) = (List.range 3).map (fun n => a + n • d) ∨
          l.map (Subtype.val ∘ f) = (List.range 3).reverse.map (fun n => a + n • d)) ∧
        l.Pairwise (· < ·)) :
    False := by
  obtain ⟨ρ, hρ⟩ := adm_of_enum S f hf
  exact rho_adm k hk φ c hc S hS hρ

/-- **Theorem 7.2** (the statement of `Erdos197Rho.main_result` in `Challenge.lean`). -/
theorem rho_thm (k : ℕ) (hk : 1 ≤ k) (φ : ℝ) (c : ℕ) (hc : c < 2) :
    ¬ ∃ f : ℕ ≃ {n : ℕ | 1 ≤ n ∧ (Int.floor ((2 * k + 1) * (Real.logb 2 n - φ))) % 2 = c},
      ¬ ∃ l : List ℕ, (∃ a d : ℕ,
        l.map (Subtype.val ∘ f) = (List.range 3).map (fun n => a + n • d) ∨
          l.map (Subtype.val ∘ f) = (List.range 3).reverse.map (fun n => a + n • d)) ∧
        l.Pairwise (· < ·) := by
  rintro ⟨f, hf⟩
  exact rho_sub k hk φ c hc {n : ℕ | 1 ≤ n ∧ (Int.floor ((2 * k + 1) * (Real.logb 2 n - φ))) % 2 = c}
    (fun n h1 h2 => ⟨h1, h2⟩) f hf

end Erdos197Rho
