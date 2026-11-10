module

public import Solution
public import Mathlib.Order.OrderIsoNat

public section

/-! Non-vacuity of the two statements of `Challenge.lean`.

* `quarter_hyps`: every hypothesis of `Erdos197Rho.quarter` holds for an explicit order: the
  bit-reversal order of `[0, 15]` (`σ x` = the binary digits of `x` reversed) has no monotone
  3-term AP, leading parity `π = 0` and leading quarter `Q = 0`, and `q = 4`, `z = 5` lie in
  `[4, 11]`. The kernel checks the finite facts by `decide` (16 points). In general the
  hypotheses `hπ`, `hQ` are satisfiable for every order without monotone 3-term APs:
  `Erdos197Rho.phases` (the zigzag lemma) provides `π` and `Q`.
* `hf_sat`: the enumeration predicate, unfolded exactly as in `Challenge.lean`, is satisfiable:
  the powers of two, listed in increasing order, have no monotone 3-term AP. So
  `Erdos197Rho.main_result` is not true merely because the predicate is unsatisfiable.
* `class_infinite`, `class_enumerable`: every colour class of every exact ρ-partition is
  infinite, hence has enumerations `ℕ ≃ C`; so the conclusion of `Erdos197Rho.main_result`
  (no enumeration without monotone 3-term APs) is not trivially true.
* `class_one`, `class_two`: for `k = 1`, `φ = 0` the point `1` lies in the class `c = 0`
  (`⌊3 log₂ 1⌋ = 0`) and `2` in the class `c = 1` (`⌊3 log₂ 2⌋ = 3`). -/

/-- The bit-reversal ranking of `[0, 15]`. -/
def rev : List ℕ := [0, 8, 4, 12, 2, 10, 6, 14, 1, 9, 5, 13, 3, 11, 7, 15]

/-- `σ x` = the 4 binary digits of `x` reversed. -/
def σr (x : ℕ) : ℕ := rev.getD x 0

/-- All hypotheses of `Erdos197Rho.quarter` hold for `α = 0`, `β = 15`, `σ = σr`, `π = 0`,
`Q = 0`, `q = 4`, `z = 5`. -/
theorem quarter_hyps : 0 + 8 ≤ 15 ∧ Set.InjOn σr (Set.Icc 0 15) ∧
    (∀ x y z : ℕ, x ∈ Set.Icc 0 15 → z ∈ Set.Icc 0 15 → x < y → y < z → y - x = z - y →
      ¬ (σr x < σr y ∧ σr y < σr z) ∧ ¬ (σr z < σr y ∧ σr y < σr x)) ∧
    (∀ x, 0 ≤ x → x + 1 ≤ 15 → (σr x < σr (x + 1) ↔ x % 2 = 0)) ∧
    (∀ x, 0 ≤ x → x + 2 ≤ 15 → x % 2 = 0 → (σr x < σr (x + 2) ↔ x % 4 = 0)) ∧
    4 ∈ Set.Icc (0 + 4) (15 - 4) ∧ 5 ∈ Set.Icc (0 + 4) (15 - 4) ∧ 4 % 4 = 0 ∧ 5 % 2 ≠ 0 := by
  have inj : ∀ x < 16, ∀ y < 16, σr x = σr y → x = y := by decide
  have ap : ∀ x < 16, ∀ d < 8, 0 < d ∧ x + 2 * d ≤ 15 →
      ¬ (σr x < σr (x + d) ∧ σr (x + d) < σr (x + 2 * d)) ∧
      ¬ (σr (x + 2 * d) < σr (x + d) ∧ σr (x + d) < σr x) := by decide
  have hπ : ∀ x < 15, (σr x < σr (x + 1) ↔ x % 2 = 0) := by decide
  have hQ : ∀ x < 14, x % 2 = 0 → (σr x < σr (x + 2) ↔ x % 4 = 0) := by decide
  refine ⟨by norm_num, fun x hx y hy h => ?_, fun x y z hx hz hxy hyz hd => ?_,
    fun x _ h => hπ x (by omega), fun x _ h => hQ x (by omega), by simp, by simp, by norm_num,
    by norm_num⟩
  · rw [Set.mem_Icc] at hx hy
    exact inj x (by omega) y (by omega) h
  · rw [Set.mem_Icc] at hx hz
    obtain ⟨d, rfl⟩ : ∃ d, y = x + d := ⟨y - x, by omega⟩
    obtain rfl : z = x + 2 * d := by omega
    exact ap x (by omega) d (by omega) ⟨by omega, by omega⟩

/-- The conclusion of `Erdos197Rho.quarter` for that instance: `4` comes before `5`. -/
example : σr 4 < σr 5 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := quarter_hyps
  exact Erdos197Rho.quarter 0 15 h0 σr h1 h2 0 0 h3 h4 4 5 h5 h6 h7 h8

/-- The enumeration predicate of `Challenge.lean` is satisfiable: `f k = 2 ^ k` enumerates the
powers of two, and they have no 3-term AP at all. -/
theorem hf_sat : ∃ S : Set ℕ, ∃ f : ℕ ≃ S, ¬ ∃ l : List ℕ, (∃ a d : ℕ,
        l.map (Subtype.val ∘ f) = (List.range 3).map (fun n => a + n • d) ∨
          l.map (Subtype.val ∘ f) = (List.range 3).reverse.map (fun n => a + n • d)) ∧
        l.Pairwise (· < ·) := by
  refine ⟨_, Equiv.ofInjective (2 ^ ·) (Nat.pow_right_injective le_rfl), ?_⟩
  rintro ⟨l, ⟨a, d, h⟩, hl⟩
  rcases l with _ | ⟨i, _ | ⟨j, _ | ⟨k, _ | ⟨_, _⟩⟩⟩⟩ <;> simp [List.range_succ] at h
  simp at hl
  have hij : 2 ^ i < 2 ^ j := Nat.pow_lt_pow_right Nat.one_lt_two hl.1.1
  have hjk : 2 ^ (j + 1) ≤ 2 ^ k := Nat.pow_le_pow_right Nat.two_pos hl.2
  rw [pow_succ] at hjk
  have := Nat.one_le_two_pow (n := i)
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> omega

/-- Every colour class of every exact ρ-partition is infinite. -/
theorem class_infinite (k : ℕ) (φ : ℝ) (c : ℕ) (hc : c < 2) :
    Set.Infinite {n : ℕ | 1 ≤ n ∧ (Int.floor ((2 * k + 1) * (Real.logb 2 n - φ))) % 2 = c} := by
  obtain ⟨r, -, hrun, hr1, -, hgap⟩ := Erdos197Rho.rho_runs k φ
  obtain ⟨j₀, hj₀⟩ := hgap 1
  have up : ∀ t, t ≤ r (j₀ + t) := by
    intro t
    induction t with
    | zero => omega
    | succ t ih =>
      have := hj₀ (j₀ + t) (by omega)
      rw [show j₀ + (t + 1) = j₀ + t + 1 by omega]
      omega
  refine Set.infinite_of_forall_exists_gt fun N => ?_
  obtain ⟨j, hj1, hj2⟩ : ∃ j, j₀ + N + 1 ≤ j ∧ j % 2 = c :=
    ⟨j₀ + N + 1 + (j₀ + N + 1 + c) % 2, by omega, by omega⟩
  have hl := hj₀ j (by omega)
  have hu := up (j - j₀)
  rw [show j₀ + (j - j₀) = j by omega] at hu
  refine ⟨r j, ⟨hr1 j, ?_⟩, by omega⟩
  rw [(hrun j (r j) (hr1 j)).mpr ⟨le_rfl, by omega⟩]
  omega

/-- Every colour class of every exact ρ-partition has enumerations. -/
theorem class_enumerable (k : ℕ) (φ : ℝ) (c : ℕ) (hc : c < 2) :
    Nonempty (ℕ ≃ {n : ℕ | 1 ≤ n ∧ (Int.floor ((2 * k + 1) * (Real.logb 2 n - φ))) % 2 = c}) := by
  have := (class_infinite k φ c hc).to_subtype
  exact ⟨(Nat.Subtype.orderIsoOfNat _).toEquiv⟩

/-- For `k = 1`, `φ = 0`: `1` lies in the class `c = 0`. -/
theorem class_one :
    1 ∈ {n : ℕ | 1 ≤ n ∧ (Int.floor ((2 * (1 : ℕ) + 1) * (Real.logb 2 n - 0))) % 2 = 0} := by
  refine ⟨le_rfl, ?_⟩
  norm_num

/-- For `k = 1`, `φ = 0`: `2` lies in the class `c = 1`. -/
theorem class_two :
    2 ∈ {n : ℕ | 1 ≤ n ∧ (Int.floor ((2 * (1 : ℕ) + 1) * (Real.logb 2 n - 0))) % 2 = 1} := by
  refine ⟨by norm_num, ?_⟩
  have h : Real.logb 2 ((2 : ℕ) : ℝ) = 1 := by
    rw [Nat.cast_ofNat]; exact Real.logb_self_eq_one one_lt_two
  rw [h]
  norm_num

#print axioms quarter_hyps
#print axioms hf_sat
#print axioms class_infinite
#print axioms class_enumerable
#print axioms class_one
#print axioms class_two
