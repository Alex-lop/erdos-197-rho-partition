# Erdős #197: the Quarter Lemma, and the exact ρ-partitions are not permutable

> **Status: PARTIAL result toward Erdős #197, NOT a solution.** This repository does **not** solve [Erdős Problem #197](https://www.erdosproblems.com/197), which is still open. It proves, and formally verifies in Lean 4, a rigidity lemma for orders of intervals without monotone 3-term APs (the Quarter Lemma) and its consequence that a whole family of colourings with short runs fails (Theorem 7.2).

## The result

Erdős #197 (Erdős–Graham) asks whether $\mathbb N$ can be partitioned into two sets, each with an enumeration (a listing of order type $\omega$) that contains no monotone 3-term arithmetic progression. Call such a set *permutable*. Davis–Entringer–Graham–Simmons (1977) showed that $\mathbb N$ itself is not permutable. Kasel (arXiv:2609.02939, 2026) showed that the dyadic partition fails.

**Quarter Lemma.** Let $\prec$ be a linear order of an integer interval $[\alpha,\beta]$, $\beta-\alpha\ge8$, with no monotone 3-term AP. It has a *leading parity* $\pi$ ($x\prec x+1$ exactly when $x\equiv\pi\bmod 2$) and a *leading quarter* $Q$ (a point $x\equiv\pi$ comes before $x+2$ exactly when $x\equiv Q\bmod 4$). Then
$$q\prec z\qquad\text{for all }q,z\in[\alpha+4,\beta-4]\text{ with }q\equiv Q\ (\mathrm{mod}\ 4)\text{ and }z\not\equiv\pi\ (\mathrm{mod}\ 2).$$

**Theorem 7.2** (main result). For $k\ge1$ and a real phase $\varphi$, the *exact ρ-partition* colours $n\ge1$ by the parity of $\lfloor(2k+1)(\log_2n-\varphi)\rfloor$: every octave consists of $2k+1$ runs $[\lceil2^{\varphi+i/(2k+1)}\rceil,\lceil2^{\varphi+(i+1)/(2k+1)}\rceil)$ of alternating colours. **Neither** colour class is permutable. There is no assumption on the enumeration (no lag hypothesis).

**What it kills.** Every exact ρ-partition, for every $k\ge1$, every phase and both colours. Its runs have ratio $2^{1/(2k+1)}\le2^{1/3}$, below the ratio $7/4$ that the tower obstruction of [Alex-lop/erdos-197-tower-obstruction](https://github.com/Alex-lop/erdos-197-tower-obstruction) needs, so that theorem does not cover them. More precisely, no set containing a colour class is permutable (`Erdos197Rho.rho_sub`), and the proof (`Erdos197Rho.runs_int`) works for any integer run boundaries $r_j$ with slivers $2r_j-r_{j+2k+1}\in\{0,1\}$ and run lengths tending to infinity, not only for $r_j=\lceil2^{\varphi+j/(2k+1)}\rceil$. **What it does not reach:** ρ-type colourings whose run boundaries drift, so that the slivers $2r_i-r_{i+2k+1}$ are unbounded (some of these are killed in the working notes, but not here), log-periodic colourings with more arcs per period, and non-interval colourings; see [`docs/proof.md`](docs/proof.md), Section 8.

**Idea of the proof.** Kasel's ladder lemmas (zigzag and flood) turn into two rules (Rule A for odd distances, Rule B for distances $\equiv2\bmod4$) that relate a far comparison $x\prec w$ to the comparison of $x$ with a neighbour. For the Quarter Lemma, either Rule A applies directly at $q$, or a centre $c\equiv q+2\pmod 4$ is found halfway towards $z$ (or away from it) with $q\prec c$ by Rule B and $c\prec z$ by Rule A: two floods. For Theorem 7.2, fix consecutive anchors $e,e+1$ ($e\ge20$) inside one run. In the exact ρ-partition, the double of the bottom of each run $J_i$ lands zero or one above the bottom of $J_{i+2k+1}$ (the *sliver* $2r_i-r_{i+2k+1}$ is $0$ or $1$), so the window $W$ at the bottom of $J_i$ has $2W-\{e,e+1\}$ inside the run $J_{i+2k}$ of the same colour (the B-link). The anchor rule ($e\prec y\Rightarrow 2y-e\prec y$) and the Quarter Lemma in $J_{i+2k}$ then give a point of the next window before the current one: an infinite descending chain of positions, impossible for an enumeration. The whole argument is in [`docs/proof.md`](docs/proof.md).

## Lean formalization

| File | Contents |
| --- | --- |
| [`Challenge.lean`](Challenge.lean) | The two statements to audit (Mathlib-only, proofs `sorry`). |
| [`Solution.lean`](Solution.lean) | The same statements, proved. |
| [`Erdos197Rho/Basic.lean`](Erdos197Rho/Basic.lean) | The proof: phases, Quarter Lemma, anchor lemmas, Theorem L\* for one anchor pair, B-link, the runs of the exact ρ-partition, Theorem 7.2. |
| [`Erdos197Interval/Basic.lean`](Erdos197Interval/Basic.lean) | Theorem I and the ladder toolkit (zigzag, flood, Rules A and B), a verbatim copy of the module of [Alex-lop/erdos-197-interval-gadget](https://github.com/Alex-lop/erdos-197-interval-gadget) (same content and namespace). |
| [`checks/`](checks) | Fidelity and non-vacuity checks (not part of the build). |

```lean
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
    σ q < σ z

theorem Erdos197Rho.main_result (k : ℕ) (hk : 1 ≤ k) (φ : ℝ) (c : ℕ) (hc : c < 2) :
    ¬ ∃ f : ℕ ≃ {n : ℕ | 1 ≤ n ∧ (Int.floor ((2 * k + 1) * (Real.logb 2 n - φ))) % 2 = c},
      ¬ ∃ l : List ℕ, (∃ a d : ℕ,
        l.map (Subtype.val ∘ f) = (List.range 3).map (fun n => a + n • d) ∨
          l.map (Subtype.val ∘ f) = (List.range 3).reverse.map (fun n => a + n • d)) ∧
        l.Pairwise (· < ·)
```

How to read them:

- In `quarter`, a linear order of $[\alpha,\beta]$ is an injective ranking `σ`: $x$ comes before $y$ when `σ x < σ y`. `hAP` says that no 3-term AP $x<y<z$ of the interval has `σ y` strictly between `σ x` and `σ z`. `hπ` and `hQ` say that `π` is the leading parity and `Q` the leading quarter. Such `π` and `Q` exist for every order without monotone 3-term APs: this is the zigzag lemma, proved as `Erdos197Rho.phases` in `Erdos197Rho/Basic.lean`.
- In `main_result`, `Real.logb 2` is $\log_2$, the floor is `Int.floor`, and `% 2` on `ℤ` is `Int.emod`, so the class of `c ∈ {0, 1}` is $\{n\ge1:\lfloor(2k+1)(\log_2n-\varphi)\rfloor\equiv c\pmod2\}$ (the even-indexed runs for `c = 0`, its complement in the positive integers for `c = 1`). An enumeration of the class is `f : ℕ ≃ C`, listing `f 0, f 1, f 2, …`. The `¬ ∃ l …` clause is `¬HasMonotoneAP (Subtype.val ∘ f) 3` from [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures/blob/5d8b04d3d41b745cc3f2f3cdd5ed04b60c500983/FormalConjectures/ErdosProblems/197.lean) with the definitions unfolded: no strictly increasing list of indices is mapped onto $a,a+d,a+2d$ or onto $a+2d,a+d,a$. It is the predicate of formal-conjectures' `Erdos197.erdos_197`, written exactly as in `Erdos197Interval.main_result`. The conclusion says that the class has no enumeration without monotone 3-term APs.
- Inside the proof the run boundaries are the integers $r_j=\lceil2^{\varphi+j/(2k+1)}\rceil$; `Erdos197Rho.rho_runs` proves that for $n\ge1$, $\lfloor(2k+1)(\log_2n-\varphi)\rfloor=j$ iff $r_j\le n<r_{j+1}$, so the statement is about the `Real.logb` definition itself.
- $\mathbb N$ is Lean's $\{0,1,2,\dots\}$, as in formal-conjectures; `β - 4` is truncated subtraction, the true value since $\beta\ge8$.

Checks performed (Lean `v4.35.0`, Mathlib `v4.35.0`):

- `lake build` succeeds. Its only warnings are the two deliberate `sorry`s in `Challenge.lean`. There is no `sorry`, `admit`, `native_decide`, `decide`, `implemented_by`, `opaque` or `axiom` anywhere else in the build (the non-vacuity check uses `decide` on 16 explicit points; it is not part of the build).
- `#print axioms` lists only `propext`, `Classical.choice` and `Quot.sound` for both theorems.
- The statements in `Challenge.lean` and `Solution.lean` elaborate to identical terms (checked with `pp.all`; the outputs are byte-identical).
- In [`checks/fidelity.lean`](checks/fidelity.lean), verbatim copies of formal-conjectures' `HasMonotoneAP`, `List.IsAPOfLength` and `List.IsAPOfLengthWith` are used to restate Theorem 7.2 (`fc_main`), proved by `exact` from the Challenge statement, i.e. by definitional unfolding alone. The file also proves `fc_erdos197_rho`: if `IsCompl A B` and the positive integers in $A$ are exactly those of the class `c = 0` (the point $0$ on either side), then neither $A$ nor $B$ has an enumeration $f$ with `¬HasMonotoneAP (Subtype.val ∘ f) 3`, so $(A,B)$ is not a witness for `Erdos197.erdos_197`.
- Non-vacuity ([`checks/nonvacuity.lean`](checks/nonvacuity.lean)): every hypothesis of `quarter` holds for an explicit order (the bit-reversal order of $[0,15]$, with $\pi=Q=0$, checked by `decide`), and `Erdos197Rho.phases` provides `π`, `Q` for every order; the enumeration predicate, unfolded exactly as in `Challenge.lean`, is satisfiable (`hf_sat`: the powers of two in increasing order); every colour class of every exact ρ-partition is infinite and has enumerations, so the conclusion of `main_result` is not trivially true (`class_infinite`, `class_enumerable`); and for $k=1$, $\varphi=0$ the point $1$ lies in the class `c = 0` and $2$ in the class `c = 1` (`class_one`, `class_two`).
- The formalizer ran `check-lean-sources.py` and `validate-formalization.rb` from the [Palomar template](https://github.com/PalomarRegistry/PalomarTemplate) (commit `2891de4`); both passed. The scripts are not vendored here; copy them from the template to rerun them.

The repository follows the [Palomar](https://palomar-registry.org) layout, with `comparator.json` and `formalization.yaml`. It has **not** been submitted to the registry.

To build:

```sh
lake exe cache get   # download Mathlib build files
lake build
```

## Reproducing the checks

After `lake build`, run `lake env lean checks/fidelity.lean` and `lake env lean checks/nonvacuity.lean` from the repository root. Both end with `#print axioms`, which reports only `propext`, `Classical.choice` and `Quot.sound`. The first copies formal-conjectures' definitions verbatim from commit [`5d8b04d3`](https://github.com/google-deepmind/formal-conjectures/blob/5d8b04d3d41b745cc3f2f3cdd5ed04b60c500983/FormalConjecturesForMathlib/Combinatorics/AP/Basic.lean).

## Related repositories

- [Alex-lop/erdos-197-interval-gadget](https://github.com/Alex-lop/erdos-197-interval-gadget): Theorem I (the anchored gadget $[M,2M+6]$ is infeasible for $M\ge8$) and Corollary I. Its Lean module, which contains the ladder toolkit used by the Quarter Lemma (zigzag, flood, Rules A and B), is included here verbatim.
- [Alex-lop/erdos-197-tower-obstruction](https://github.com/Alex-lop/erdos-197-tower-obstruction): Theorem R\* (tower obstruction) and Corollary R2\*: alternating run colourings with ratios tending to $2$ fail. Theorem 7.2 here covers runs of ratio $2^{1/(2k+1)}$, which R\* does not reach; its integer form covers any run boundaries $r_j$ with slivers $2r_j-r_{j+2k+1}\in\{0,1\}$ and run lengths tending to infinity.
- [Alex-lop/erdos-197-bounded-lag](https://github.com/Alex-lop/erdos-197-bounded-lag): an earlier, independent partial result on #197 from the same project (no two-set solution with eventual lag ratio below $2$).

## Credits

- A. Sharma, *Enumerating permutations that avoid three term arithmetic progressions*, Electron. J. Combin. 16 (2009), #R63: Theorems 2.1 and 2.4 imply the Quarter Lemma. The proof formalized here is the two-flood argument; the derivation from Sharma's theorems is not formalized.
- W. Kasel, *Structural rigidity in the Erdős–Graham two-set permutation problem*, arXiv:2609.02939: the ladder toolkit (zigzag and flood, Lemmas 23–26).
- Theorem I ([Alex-lop/erdos-197-interval-gadget](https://github.com/Alex-lop/erdos-197-interval-gadget)): Rules A and B and their Lean proofs.

## Use of AI

This work was produced by **Claude Fable 5.1** and **Claude Opus 5.5** (Anthropic), running in Claude Code, under the direction of **Alex Lopez**. Claude Opus 5.5 wrote the Lean formalization and this repository. The informal proof was verified by three adversarial AI referees (proof, computation and scope lenses; none refuted it), and the Lean kernel checks both theorems. The refereed text is the project's working note `work/p197_m2_r3/rho/proof.md`, which is not included here; `docs/proof.md` is a rewrite of it, and its introduction lists the parts that were not refereed (each is mirrored by the kernel-checked Lean proof). Neither text has been refereed by a human. On 2026-11-10 an AI audit's documentation corrections were applied by Claude Sonnet 5.5 and Claude Fable 5.2: theorem numbers in this README, the Lean docstrings and `formalization.yaml` now follow `docs/proof.md`, and three sentences were corrected. No Lean statement or proof was changed.

## License

Apache-2.0; see [LICENSE](LICENSE).
