import Erdos320.Lemmas.LaurentEval
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Convergence of the reference functions (§6, `lem:backward-reference-convergence`)

The convergence half of the paper's Lemma "Convergence of the reference
functions": the finite reference functions
`Q_s^{[R]} = 𝓛_s ⋯ 𝓛_{R−1} J_R` (eq. `finite-reference`) converge as the
terminal depth `R → ∞`, with a quantitative super-exponential tail.

Contents, following the paper's proof of `lem:backward-reference-convergence`:

* **Formal Laurent representation of `Q_s^{[R]}`** — `QrefComb` mirrors the
  recursion of `Qref` at the level of `LaurentComb`, with the eval bridge
  `Qref_eq_evalComb` and the derivative bridge `hasDerivAt_Qref`.
* **The exact increment identity** (eq. `reference-defect`):
  `Q_s^{[R+1]} − Q_s^{[R]} = 𝓛_s ⋯ 𝓛_{R−1} R_R`, formalized as
  `Qref_succ_sub_eval` with the increment comb `DeltaComb s R`
  (`DeltaComb R R = RdefectComb R`, one backward step per depth below `R`).
* **The `U`/`V` split** — `DeltaComb` decomposes as `UCombAux + VCombAux`,
  the backward images of the two halves `A_{R−2}` and `A_{R−1}/E_{R−2}` of
  the defect `R_R` (`DeltaCombAux_eq_UCombAux_add_VCombAux`).
* **The size induction** (inside the paper's proof of
  `lem:backward-reference-convergence`): the bundled invariant
  `CombSizeBound` (largest variable index, positive-exponent indices,
  exponent height, coefficient ℓ¹-norm) is preserved by every backward step
  and by formal differentiation (`UCombAux_sizeBound`, `VCombAux_sizeBound`),
  and the terminal inverse factors `x_{R−3}^{−1}` (for `U`) and `x_{R−2}^{−1}`
  (for `V`) persist (`UCombAux_apply_le_neg_one`, `VCombAux_apply_le_neg_one`).
* **The evaluation bounds** (eqs. `late-U-bound`, `late-V-bound`):
  `abs_evalComb_derivIter_UCombAux_le`, `abs_evalComb_derivIter_VCombAux_le`.
* **The clean exponential increment bound** (eq. `reference-increment`):
  `abs_evalComb_derivIter_DeltaComb_le` —
  `|∂_u^k (Q_s^{[R+1]} − Q_s^{[R]})| ≤ 2 exp(−E_{R−4}/2)` for `k ≤ 2`,
  `R ≥ 8`, `4 ≤ s < R` (via `R_cubed_le_E_sub_five` and
  `poly_factor_le_exp_half`, the paper's "take logarithms" step).
* **The limit** — `QrefLimit s = Q_s^*` as `Q_s^{[s+1]}` plus the convergent
  series of increments; `Qref_tendsto_QrefLimit` (pointwise convergence) and
  the quantitative tail `abs_QrefLimit_sub_Qref`
  (`|Q_s^* − Q_s^{[R]}| ≤ 4 exp(−E_{R−4}/2)`).

**Not in this file** (done in `BackwardReferenceLimit.lean`): the
`A_s`-proximity bounds
eq. `reference-derivative-bound`, the recurrence `(Q_{s+1}^*)' = a_s Q_s^*`
for the limit, `C²`-convergence as such, and the numeric `R = 7` tail
eq. `R7-tail`.

Paper-vs-Lean notes:
* The paper's uniform bounds are stated on `u ∈ [1, e]`; the Lean statements
  need only `1 ≤ u` (monotonicity of `E` in the depth index replaces the
  endpoint evaluation), which is strictly stronger.
* The paper's coefficient-norm invariant `‖·‖₁ ≤ 2R(2R²)^{t+k} ≤ (2R²)^R` is
  tracked here with exponent `k + m` (backward steps plus formal
  derivatives) under the hypothesis `k + m + 1 ≤ R`, which holds with room
  to spare in every use (`k ≤ R − 5`, `m ≤ 2`).
* The increment identity `Qref_succ_sub_eval` requires `4 ≤ s` (through
  `hasDerivAt_J_succ`, whose defect identity fails at `r = 3`), matching the
  paper's "take `r ≥ 5`" remark; the hypothesis `4 ≤ R` in the paper's
  statement is implied by `4 ≤ s ≤ R` and is therefore not a separate
  hypothesis here.
-/

namespace Erdos320

/-! ## Additivity of the formal operations

Comb-level linearity of `derivComb` and `shiftComb`, needed to split the
increment `DeltaComb` into its `U`- and `V`-halves. -/

/-- Formal differentiation is additive on combinations (it is defined
coefficient-linearly from `derivMon`). -/
theorem derivComb_add (P Q : LaurentComb) :
    derivComb (P + Q) = derivComb P + derivComb Q := by
  have h : ∀ S : LaurentComb, derivComb S = S.sum fun ν c => c • derivMon ν :=
    fun _ => rfl
  rw [h, h, h]
  exact Finsupp.sum_add_index' (fun _ => zero_smul ℤ _)
    fun _ c₁ c₂ => add_smul c₁ c₂ _

/-- The division shift is additive on combinations (`Finsupp.mapDomain_add`). -/
theorem shiftComb_add (μ : ExpVec) (P Q : LaurentComb) :
    shiftComb μ (P + Q) = shiftComb μ P + shiftComb μ Q :=
  Finsupp.mapDomain_add

/-- Iterated formal differentiation is additive. -/
theorem derivComb_iterate_add (m : ℕ) (P Q : LaurentComb) :
    derivComb^[m] (P + Q) = derivComb^[m] P + derivComb^[m] Q := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        Function.iterate_succ_apply', ih, derivComb_add]

/-! ## Support bookkeeping helpers -/

/-- Every monomial of a shifted combination is a shifted monomial of the
original combination. -/
theorem mem_shiftComb_support {μ : ExpVec} {P : LaurentComb} {ν' : ExpVec}
    (hν' : ν' ∈ (shiftComb μ P).support) : ∃ ν ∈ P.support, ν' = ν - μ := by
  have h : ν' ∈ (Finsupp.mapDomain (fun ν => ν - μ) P).support := hν'
  rw [Finsupp.mapDomain_support_of_injective (sub_const_injective μ) P] at h
  obtain ⟨ν, hν, hνe⟩ := Finset.mem_image.mp h
  exact ⟨ν, hν, hνe.symm⟩

/-- A coordinate where `derivShift i` is positive lies strictly below `i`
(the stair of `x_i` touches only indices `1, …, i−1`; the `x₀`-shift is
nonpositive everywhere). -/
theorem derivShift_pos_index_lt {i j : ℕ} (h : 0 < derivShift i j) : j < i := by
  cases i with
  | zero =>
      exfalso
      have h0 : derivShift 0 j ≤ 0 := derivShift_apply_nonpos (Nat.zero_le j)
      omega
  | succ k =>
      have h' : (0 : ℤ) < stairVec k j := h
      by_cases hmem : j ∈ Finset.Icc 1 k
      · exact Nat.lt_succ_of_le (Finset.mem_Icc.mp hmem).2
      · rw [stairVec_apply, if_neg hmem] at h'
        omega

/-- All variable indices of the denominator monomial `aVec r` are at most
`r − 2`. -/
theorem vecMaxIdx_aVec_le (r : ℕ) : vecMaxIdx (aVec r) ≤ r - 2 :=
  Finset.sup_le fun _ hj =>
    (Finset.mem_Icc.mp (stairVec_support_subset (r - 2) hj)).2

/-- The single-variable monomial `x_j^n` has largest index at most `j`. -/
theorem vecMaxIdx_single_le (j : ℕ) (n : ℤ) :
    vecMaxIdx (Finsupp.single j n) ≤ j :=
  Finset.sup_le fun i hi => by
    have h : i ∈ ({j} : Finset ℕ) := Finsupp.support_single_subset hi
    rw [Finset.mem_singleton] at h
    exact le_of_eq h

/-- The principal monomial `x₀⋯x_{k−1}` has exponent height at most `k`. -/
theorem height_rangeVec_le (k : ℕ) : height (rangeVec k) ≤ k :=
  calc height (rangeVec k)
      = ∑ j ∈ Finset.range k, ((rangeVec k) j).natAbs :=
        height_eq_sum_superset (rangeVec_support_subset k)
    _ ≤ ∑ _j ∈ Finset.range k, 1 :=
        Finset.sum_le_sum fun j hj => by rw [rangeVec_apply, if_pos hj]; omega
    _ = k := by
        rw [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_range]

/-- Structure of the monomials of `AComb s`: the constant `1` or a principal
monomial `x₀⋯x_{j−3}` with `3 ≤ j ≤ s` (eq. `D-identity`). -/
theorem mem_AComb_support {s : ℕ} {ν : ExpVec} (hν : ν ∈ (AComb s).support) :
    ν = 0 ∨ ∃ j ∈ Finset.Icc 3 s, ν = rangeVec (j - 2) := by
  unfold AComb at hν
  rcases Finset.mem_union.mp (Finsupp.support_add hν) with h | h
  · exact Or.inl (Finset.mem_singleton.mp (Finsupp.support_single_subset h))
  · right
    obtain ⟨j, hj, hνj⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum h)
    refine ⟨j, hj, ?_⟩
    have h1 : ν ∈ (Finsupp.single (rangeVec (j - 2)) (1 : ℤ)).support := hνj
    exact Finset.mem_singleton.mp (Finsupp.support_single_subset h1)

/-- Every variable index occurring in a monomial of `AComb s` satisfies
`j + 3 ≤ s` (the top monomial is `x₀⋯x_{s−3}`). -/
theorem AComb_support_index_le {s : ℕ} {ν : ExpVec}
    (hν : ν ∈ (AComb s).support) : ∀ j ∈ ν.support, j + 3 ≤ s := by
  intro j hj
  rcases mem_AComb_support hν with rfl | ⟨i, hi, rfl⟩
  · simp at hj
  · have h1 := Finset.mem_range.mp (rangeVec_support_subset (i - 2) hj)
    have h2 := Finset.mem_Icc.mp hi
    omega

/-- Monomials of `AComb s` have coordinate `0` at every index `t ≥ s − 2`. -/
theorem AComb_apply_eq_zero {s : ℕ} {ν : ExpVec} (hν : ν ∈ (AComb s).support)
    {t : ℕ} (ht : s ≤ t + 2) : ν t = 0 := by
  by_contra h
  have h1 := AComb_support_index_le hν t (Finsupp.mem_support_iff.mpr h)
  omega

/-- Largest variable index of `AComb s` is at most `s − 3`. -/
theorem maxIdx_AComb_le (s : ℕ) : maxIdx (AComb s) ≤ s - 3 := by
  refine Finset.sup_le fun ν hν => Finset.sup_le fun j hj => ?_
  have h := AComb_support_index_le hν j hj
  show j ≤ s - 3
  omega

/-- Exponent height of `AComb s` is at most `s − 2`. -/
theorem combHeight_AComb_le (s : ℕ) : combHeight (AComb s) ≤ s - 2 := by
  refine Finset.sup_le fun ν hν => ?_
  rcases mem_AComb_support hν with rfl | ⟨j, hj, rfl⟩
  · simp [height]
  · have h1 := height_rangeVec_le (j - 2)
    have h2 := Finset.mem_Icc.mp hj
    omega

/-- Coefficient ℓ¹-norm of `AComb s` is at most `s − 1` (all coefficients
are `1`; there are `1 + (s − 2)` monomials). -/
theorem l1Norm_AComb_le {s : ℕ} (hs : 2 ≤ s) : l1Norm (AComb s) ≤ s - 1 := by
  unfold AComb
  refine le_trans (l1Norm_add_le _ _) ?_
  have h1 : l1Norm (Finsupp.single (0 : ExpVec) (1 : ℤ)) = 1 := by
    rw [l1Norm_single]
    rfl
  have h2 : l1Norm (∑ j ∈ Finset.Icc 3 s, DComb j) ≤ s - 2 := by
    refine le_trans (l1Norm_finsetSum_le _ _) (le_of_eq ?_)
    have h3 : ∀ j ∈ Finset.Icc 3 s, l1Norm (DComb j) = 1 := fun j _ => by
      show l1Norm (Finsupp.single (rangeVec (j - 2)) (1 : ℤ)) = 1
      rw [l1Norm_single]
      rfl
    calc ∑ j ∈ Finset.Icc 3 s, l1Norm (DComb j)
        = ∑ _j ∈ Finset.Icc 3 s, 1 := Finset.sum_congr rfl h3
      _ = s - 2 := by
          rw [Finset.sum_const, smul_eq_mul, mul_one, Nat.card_Icc]
          omega
  omega

/-- Iterated formal differentiation never raises the largest variable
index. -/
theorem maxIdx_derivComb_iterate_le (P : LaurentComb) (m : ℕ) :
    maxIdx (derivComb^[m] P) ≤ maxIdx P := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply']
      exact le_trans (maxIdx_derivComb_le _) ih

/-- Persistence of a terminal inverse factor through iterated formal
differentiation (the paper's "these terminal inverse factors persist …
under ordinary differentiation"). -/
theorem derivComb_iterate_apply_le_neg_one {P : LaurentComb} {t : ℕ}
    (hmax : maxIdx P ≤ t) (hP : ∀ ν ∈ P.support, ν t ≤ -1) (m : ℕ) :
    ∀ μ ∈ (derivComb^[m] P).support, μ t ≤ -1 := by
  induction m with
  | zero => simpa using hP
  | succ m ih =>
      rw [Function.iterate_succ_apply']
      exact derivComb_apply_le_neg_one
        (le_trans (maxIdx_derivComb_iterate_le P m) hmax) ih

/-! ## The reference functions as formal Laurent combinations
(eq. `finite-reference`) -/

/-- Auxiliary recursion mirroring `QrefAux` at the comb level:
`QrefCombAux k R` applies the last `k` backward operators
`𝓛_{R−k} ⋯ 𝓛_{R−1}` — each one "differentiate formally, then shift by
`aVec`" (eq. `laurent-derivative`) — to the seed `JComb R`. -/
noncomputable def QrefCombAux : ℕ → ℕ → LaurentComb
  | 0, R => JComb R
  | k + 1, R => shiftComb (aVec (R - (k + 1))) (derivComb (QrefCombAux k R))

theorem QrefCombAux_zero (R : ℕ) : QrefCombAux 0 R = JComb R := by
  rw [QrefCombAux]

theorem QrefCombAux_succ (k R : ℕ) :
    QrefCombAux (k + 1) R
      = shiftComb (aVec (R - (k + 1))) (derivComb (QrefCombAux k R)) := rfl

/-- `QrefComb s R`: the finite backward reference function
`Q_s^{[R]} = 𝓛_s ⋯ 𝓛_{R−1} J_R` (eq. `finite-reference`) as a formal
Laurent combination; meaningful for `s ≤ R` (and degenerating to `JComb R`
for `s ≥ R`, like `Qref`). -/
noncomputable def QrefComb (s R : ℕ) : LaurentComb := QrefCombAux (R - s) R

/-- The auxiliary eval bridge: on positive phase, `QrefAux` evaluates its
comb representation (downward induction through `Lop_evalComb`). -/
theorem QrefAux_eq_evalComb (k R : ℕ) :
    ∀ {u : ℝ}, 0 < u → QrefAux k R u = evalComb (QrefCombAux k R) u := by
  induction k with
  | zero =>
      intro u _
      rw [QrefAux_zero, QrefCombAux_zero, evalComb_JComb]
  | succ k ih =>
      intro u hu
      have hev : QrefAux k R =ᶠ[nhds u] evalComb (QrefCombAux k R) := by
        filter_upwards [Ioi_mem_nhds hu] with v hv
        exact ih hv
      rw [QrefAux_succ, QrefCombAux_succ]
      calc Lop (R - (k + 1)) (QrefAux k R) u
          = deriv (QrefAux k R) u / a (R - (k + 1)) u := rfl
        _ = deriv (evalComb (QrefCombAux k R)) u / a (R - (k + 1)) u := by
            rw [hev.deriv_eq]
        _ = Lop (R - (k + 1)) (evalComb (QrefCombAux k R)) u := rfl
        _ = evalComb (shiftComb (aVec (R - (k + 1)))
              (derivComb (QrefCombAux k R))) u := Lop_evalComb _ _ hu

/-- **Eval bridge for the reference functions.**  On positive phase,
`Q_s^{[R]}` is the evaluation of its formal Laurent representation
(eq. `finite-reference` read through eq. `laurent-derivative`). -/
theorem Qref_eq_evalComb {s R : ℕ} {u : ℝ} (hu : 0 < u) :
    Qref s R u = evalComb (QrefComb s R) u :=
  QrefAux_eq_evalComb (R - s) R hu

/-- Derivative bridge: `Q_s^{[R]}` has the derivative of its comb
representation (via `hasDerivAt_evalComb` and locality of the
derivative). -/
theorem hasDerivAt_Qref {s R : ℕ} {u : ℝ} (hu : 0 < u) :
    HasDerivAt (Qref s R) (evalComb (derivComb (QrefComb s R)) u) u := by
  refine (hasDerivAt_evalComb hu (QrefComb s R)).congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hu] with v hv
  exact Qref_eq_evalComb hv

/-- Iterated derivative bridge: `evalComb (derivComb^[m] P)` is, at each
positive phase, the derivative of `evalComb (derivComb^[m−1] P)` — so the
iterated formal derivative evaluates to the honest `m`-th derivative
(used for the `k = 0, 1, 2` cases of eq. `reference-increment`). -/
theorem hasDerivAt_evalComb_iterate {u : ℝ} (hu : 0 < u) (P : LaurentComb)
    (m : ℕ) :
    HasDerivAt (evalComb (derivComb^[m] P))
      (evalComb (derivComb^[m + 1] P) u) u := by
  rw [Function.iterate_succ_apply']
  exact hasDerivAt_evalComb hu _

/-! ## The increment combs (eq. `reference-defect`)

`Δ_{s,R} = Q_s^{[R+1]} − Q_s^{[R]} = 𝓛_s ⋯ 𝓛_{R−1} R_R`, split as
`Δ_{s,R} = U_{s,R} + V_{s,R}` with `U_{s,R} = 𝓛_s ⋯ 𝓛_{R−1} A_{R−2}` and
`V_{s,R} = 𝓛_s ⋯ 𝓛_{R−1} (A_{R−1}/E_{R−2})`. -/

/-- `DeltaCombAux k R`: `k` backward steps applied to the defect seed
`RdefectComb R` (eq. `reference-defect`). -/
noncomputable def DeltaCombAux : ℕ → ℕ → LaurentComb
  | 0, R => RdefectComb R
  | k + 1, R => shiftComb (aVec (R - (k + 1))) (derivComb (DeltaCombAux k R))

theorem DeltaCombAux_zero (R : ℕ) : DeltaCombAux 0 R = RdefectComb R := by
  rw [DeltaCombAux]

theorem DeltaCombAux_succ (k R : ℕ) :
    DeltaCombAux (k + 1) R
      = shiftComb (aVec (R - (k + 1))) (derivComb (DeltaCombAux k R)) := rfl

/-- `DeltaComb s R`: the increment `Δ_{s,R} = Q_s^{[R+1]} − Q_s^{[R]}`
(eq. `reference-defect`) as a formal Laurent combination. -/
noncomputable def DeltaComb (s R : ℕ) : LaurentComb := DeltaCombAux (R - s) R

theorem DeltaComb_self (R : ℕ) : DeltaComb R R = RdefectComb R := by
  unfold DeltaComb
  rw [Nat.sub_self, DeltaCombAux_zero]

theorem DeltaComb_of_lt {s R : ℕ} (h : s < R) :
    DeltaComb s R = shiftComb (aVec s) (derivComb (DeltaComb (s + 1) R)) := by
  unfold DeltaComb
  rw [show R - s = (R - (s + 1)) + 1 by omega, DeltaCombAux_succ,
    show R - (R - (s + 1) + 1) = s by omega]

/-- `UCombAux k R`: `k` backward steps applied to the first half `A_{R−2}`
of the defect `R_R` (the paper's `U_{s,R}` with `k = R − s`). -/
noncomputable def UCombAux : ℕ → ℕ → LaurentComb
  | 0, R => AComb (R - 2)
  | k + 1, R => shiftComb (aVec (R - (k + 1))) (derivComb (UCombAux k R))

theorem UCombAux_zero (R : ℕ) : UCombAux 0 R = AComb (R - 2) := rfl

theorem UCombAux_succ (k R : ℕ) :
    UCombAux (k + 1) R
      = shiftComb (aVec (R - (k + 1))) (derivComb (UCombAux k R)) := rfl

/-- `VCombAux k R`: `k` backward steps applied to the second half
`A_{R−1}/E_{R−2}` of the defect `R_R` (the paper's `V_{s,R}` with
`k = R − s`). -/
noncomputable def VCombAux : ℕ → ℕ → LaurentComb
  | 0, R => shiftComb (Finsupp.single (R - 2) 1) (AComb (R - 1))
  | k + 1, R => shiftComb (aVec (R - (k + 1))) (derivComb (VCombAux k R))

theorem VCombAux_zero (R : ℕ) :
    VCombAux 0 R = shiftComb (Finsupp.single (R - 2) 1) (AComb (R - 1)) := rfl

theorem VCombAux_succ (k R : ℕ) :
    VCombAux (k + 1) R
      = shiftComb (aVec (R - (k + 1))) (derivComb (VCombAux k R)) := rfl

/-- The increment comb splits into its `U`- and `V`-halves (the paper's
`Δ_{s,R} = U_{s,R} + V_{s,R}`). -/
theorem DeltaCombAux_eq_UCombAux_add_VCombAux (k R : ℕ) :
    DeltaCombAux k R = UCombAux k R + VCombAux k R := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [DeltaCombAux_succ, UCombAux_succ, VCombAux_succ, ih, derivComb_add,
        shiftComb_add]

/-! ## The exact increment identity (eq. `reference-defect`) -/

/-- Downward induction engine for eq. `reference-defect`, with the depth gap
`n = R − s` explicit so that both the depth and the phase can vary in the
induction. -/
theorem Qref_succ_sub_eval_aux (n : ℕ) :
    ∀ s : ℕ, 4 ≤ s → ∀ u : ℝ, 0 < u →
      Qref s (s + n + 1) u - Qref s (s + n) u
        = evalComb (DeltaComb s (s + n)) u := by
  induction n with
  | zero =>
      intro s hs u hu
      show Qref s (s + 1) u - Qref s s u = evalComb (DeltaComb s s) u
      rw [Qref_of_lt (by omega : s < s + 1), Qref_self, Qref_self,
        Lop_eq_of_hasDerivAt (hasDerivAt_J_succ hs u),
        mul_div_cancel_left₀ _ (a_pos s u).ne', DeltaComb_self,
        evalComb_RdefectComb hu]
      ring
  | succ n ih =>
      intro s hs u hu
      show Qref s (s + n + 1 + 1) u - Qref s (s + n + 1) u
        = evalComb (DeltaComb s (s + n + 1)) u
      have hd1 : HasDerivAt (Qref (s + 1) (s + n + 1 + 1))
          (evalComb (derivComb (QrefComb (s + 1) (s + n + 1 + 1))) u) u :=
        hasDerivAt_Qref hu
      have hd2 : HasDerivAt (Qref (s + 1) (s + n + 1))
          (evalComb (derivComb (QrefComb (s + 1) (s + n + 1))) u) u :=
        hasDerivAt_Qref hu
      have hev : evalComb (DeltaComb (s + 1) (s + n + 1)) =ᶠ[nhds u]
          fun v => Qref (s + 1) (s + n + 1 + 1) v
            - Qref (s + 1) (s + n + 1) v := by
        filter_upwards [Ioi_mem_nhds hu] with v hv
        have h := ih (s + 1) (by omega) v hv
        rw [show s + 1 + n = s + n + 1 by omega] at h
        exact h.symm
      have hΔ : HasDerivAt (evalComb (DeltaComb (s + 1) (s + n + 1)))
          (evalComb (derivComb (QrefComb (s + 1) (s + n + 1 + 1))) u
            - evalComb (derivComb (QrefComb (s + 1) (s + n + 1))) u) u :=
        (hd1.sub hd2).congr_of_eventuallyEq hev
      have huniq : evalComb (derivComb (DeltaComb (s + 1) (s + n + 1))) u
          = evalComb (derivComb (QrefComb (s + 1) (s + n + 1 + 1))) u
            - evalComb (derivComb (QrefComb (s + 1) (s + n + 1))) u :=
        (hasDerivAt_evalComb hu _).unique hΔ
      rw [Qref_of_lt (by omega : s < s + n + 1 + 1),
        Qref_of_lt (by omega : s < s + n + 1),
        Lop_eq_of_hasDerivAt hd1, Lop_eq_of_hasDerivAt hd2, div_sub_div_same,
        ← huniq, DeltaComb_of_lt (by omega : s < s + n + 1),
        evalComb_shiftComb hu, evalMon_aVec]

/-- **The exact increment identity** (eq. `reference-defect`): for
`4 ≤ s ≤ R` and positive phase,
`Q_s^{[R+1]} − Q_s^{[R]} = 𝓛_s ⋯ 𝓛_{R−1} R_R = evalComb (DeltaComb s R)`.
(The paper's side condition `4 ≤ R` follows from `4 ≤ s ≤ R`.) -/
theorem Qref_succ_sub_eval {s R : ℕ} (hs : 4 ≤ s) (hsR : s ≤ R) {u : ℝ}
    (hu : 0 < u) :
    Qref s (R + 1) u - Qref s R u = evalComb (DeltaComb s R) u := by
  obtain ⟨n, rfl⟩ : ∃ n, R = s + n := ⟨R - s, by omega⟩
  exact Qref_succ_sub_eval_aux n s hs u hu

/-! ## The size induction (inside the paper's proof of `lem:backward-reference-convergence`)

The bundled invariant: all variable indices at most `t`, all
positive-exponent indices strictly below `t`, exponent height at most `h`,
coefficient ℓ¹-norm at most `l`.  One backward step preserves the index
bounds, adds at most `2t + 1` to the height, and multiplies the norm by at
most the old height ("differentiation multiplies the coefficient ℓ¹-norm by
at most the old height, whereas the division shift leaves coefficients
unchanged"). -/

/-- Bundled size invariant of the paper's all-depth induction: for the
`U`-half `t = R − 3`, for the `V`-half `t = R − 2`. -/
structure CombSizeBound (t h l : ℕ) (P : LaurentComb) : Prop where
  /-- No variable of index above `t` occurs. -/
  maxIdx_le : maxIdx P ≤ t
  /-- Positive exponents occur only at indices `< t` (so evaluation is
  controlled by `x_{t−1}`). -/
  pos_index_le : ∀ ν ∈ P.support, ∀ j, 0 < ν j → j + 1 ≤ t
  /-- Exponent height bound. -/
  combHeight_le : combHeight P ≤ h
  /-- Coefficient ℓ¹-norm bound. -/
  l1Norm_le : l1Norm P ≤ l

theorem CombSizeBound.mono {t h l h' l' : ℕ} {P : LaurentComb}
    (hP : CombSizeBound t h l P) (hh : h ≤ h') (hl : l ≤ l') :
    CombSizeBound t h' l' P :=
  ⟨hP.maxIdx_le, hP.pos_index_le, le_trans hP.combHeight_le hh,
    le_trans hP.l1Norm_le hl⟩

/-- Formal differentiation step of the size induction: height grows by at
most `t + 1`, the norm multiplies by at most the old height, and the index
invariants persist (differentiating `x_j` adds only stair indices `< j ≤ t`). -/
theorem CombSizeBound.derivComb_step {t h l : ℕ} {P : LaurentComb}
    (hP : CombSizeBound t h l P) :
    CombSizeBound t (h + (t + 1)) (h * l) (derivComb P) := by
  refine ⟨le_trans (maxIdx_derivComb_le P) hP.maxIdx_le, ?_, ?_, ?_⟩
  · intro μ hμ j hj
    obtain ⟨ν, hν, i, hi, rfl⟩ := exists_of_mem_derivComb_support hμ
    rw [Finsupp.add_apply] at hj
    by_cases hνj : 0 < ν j
    · exact hP.pos_index_le ν hν j hνj
    · have hshift : 0 < derivShift i j := by omega
      have hji : j < i := derivShift_pos_index_lt hshift
      have hit : i ≤ t := le_trans (le_maxIdx hν hi) hP.maxIdx_le
      omega
  · refine le_trans (combHeight_derivComb_le P) ?_
    have h1 := hP.combHeight_le
    have h2 := hP.maxIdx_le
    omega
  · exact le_trans (l1Norm_derivComb_le P)
      (Nat.mul_le_mul hP.combHeight_le hP.l1Norm_le)

/-- Division-shift step of the size induction: the shift by `aVec r`
(`r ≤ t + 2`) preserves the norm and the index invariants and adds at most
`t` to the height. -/
theorem CombSizeBound.shiftComb_step {t h l r : ℕ} {P : LaurentComb}
    (hP : CombSizeBound t h l P) (hr : r ≤ t + 2) :
    CombSizeBound t (h + t) l (shiftComb (aVec r) P) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine le_trans (maxIdx_shiftComb_le _ _) (max_le hP.maxIdx_le ?_)
    exact le_trans (vecMaxIdx_aVec_le r) (by omega)
  · intro ν' hν' j hj
    obtain ⟨ν, hν, rfl⟩ := mem_shiftComb_support hν'
    rw [Finsupp.sub_apply] at hj
    have hnn := aVec_apply_nonneg r j
    exact hP.pos_index_le ν hν j (by omega)
  · refine le_trans (combHeight_shiftComb_le _ _) ?_
    exact Nat.add_le_add hP.combHeight_le
      (le_trans (height_aVec_le r) (by omega))
  · rw [l1Norm_shiftComb]
    exact hP.l1Norm_le

/-- One full backward step `P ↦ shiftComb (aVec r) (derivComb P)` of the
size induction: height grows by at most `2t + 1`, the norm multiplies by at
most the old height. -/
theorem CombSizeBound.backward_step {t h l r : ℕ} {P : LaurentComb}
    (hP : CombSizeBound t h l P) (hr : r ≤ t + 2) :
    CombSizeBound t (h + (2 * t + 1)) (h * l)
      (shiftComb (aVec r) (derivComb P)) :=
  (hP.derivComb_step.shiftComb_step hr).mono (Nat.le_of_eq (by ring)) le_rfl

/-- Norm-multiplication step shared by the four size-bound inductions
(`U`/`V` × base/derivative): under `X + 1 ≤ R` the old height `R + 2RX` is
`≤ 2R²`, so multiplying the norm `2R(2R²)^X` by it stays `≤ 2R(2R²)^{X+1}`. -/
private theorem norm_backward_step {R X : ℕ} (h : X + 1 ≤ R) :
    (R + 2 * R * X) * (2 * R * (2 * R ^ 2) ^ X)
      ≤ 2 * R * (2 * R ^ 2) ^ (X + 1) := by
  calc (R + 2 * R * X) * (2 * R * (2 * R ^ 2) ^ X)
      ≤ (2 * R ^ 2) * (2 * R * (2 * R ^ 2) ^ X) := by
        refine Nat.mul_le_mul ?_ le_rfl
        calc R + 2 * R * X = R * (2 * X + 1) := by ring
          _ ≤ R * (2 * R) := Nat.mul_le_mul_left R (by omega)
          _ = 2 * R ^ 2 := by ring
    _ = 2 * R * (2 * R ^ 2) ^ (X + 1) := by ring

/-- Height-addition step shared by the four size-bound inductions: any
increment `i ≤ 2R` added to `R + 2RX` stays within `R + 2R(X+1)`. -/
private theorem height_backward_step {R X i : ℕ} (h : i ≤ 2 * R) :
    R + 2 * R * X + i ≤ R + 2 * R * (X + 1) := by
  have he : R + 2 * R * (X + 1) = R + 2 * R * X + 2 * R := by ring
  omega

/-- Size invariants along the `U`-half backward iteration: height
`≤ R + 2Rk`, norm `≤ 2R(2R²)^k`, indices `≤ R − 3`, positive indices
`≤ R − 4` (the paper's size induction, `U`-half). -/
theorem UCombAux_sizeBound_base {R : ℕ} (hR : 8 ≤ R) :
    ∀ k, k + 1 ≤ R →
      CombSizeBound (R - 3) (R + 2 * R * k) (2 * R * (2 * R ^ 2) ^ k)
        (UCombAux k R) := by
  intro k
  induction k with
  | zero =>
      intro _
      have hbase : CombSizeBound (R - 3) R (2 * R) (UCombAux 0 R) := by
        rw [UCombAux_zero]
        refine ⟨le_trans (maxIdx_AComb_le (R - 2)) (by omega), ?_,
          le_trans (combHeight_AComb_le (R - 2)) (by omega),
          le_trans (l1Norm_AComb_le (by omega : 2 ≤ R - 2)) (by omega)⟩
        intro ν hν j hj
        have hjmem : j ∈ ν.support := Finsupp.mem_support_iff.mpr (by omega)
        have h := AComb_support_index_le hν j hjmem
        omega
      exact hbase.mono (Nat.le_of_eq (by ring)) (Nat.le_of_eq (by ring))
  | succ k ih =>
      intro hk1
      have h := (ih (by omega)).backward_step (r := R - (k + 1))
        (by omega : R - (k + 1) ≤ (R - 3) + 2)
      rw [← UCombAux_succ] at h
      refine h.mono ?_ ?_
      · exact height_backward_step (by omega)
      · exact norm_backward_step (by omega)

/-- Size invariants for the `U`-half after `k` backward steps and `m`
further formal derivatives (the paper's "`t` backward operators and then
`k` ordinary derivatives … `H_{t,k} < R + 2Rt + Rk < 2R²`, combined
coefficient norm `≤ 2R(2R²)^{t+k}`"). -/
theorem UCombAux_sizeBound {R : ℕ} (hR : 8 ≤ R) (k : ℕ) :
    ∀ m, k + m + 1 ≤ R →
      CombSizeBound (R - 3) (R + 2 * R * (k + m))
        (2 * R * (2 * R ^ 2) ^ (k + m)) (derivComb^[m] (UCombAux k R)) := by
  intro m
  induction m with
  | zero =>
      intro hkm
      exact UCombAux_sizeBound_base hR k (by omega)
  | succ m ih =>
      intro hkm
      rw [Function.iterate_succ_apply']
      have h := (ih (by omega)).derivComb_step
      refine h.mono ?_ ?_
      · exact height_backward_step (by omega)
      · exact norm_backward_step (by omega)

/-- Size invariants along the `V`-half backward iteration (`t = R − 2`;
the seed already carries the shift by `x_{R−2}`). -/
theorem VCombAux_sizeBound_base {R : ℕ} (hR : 8 ≤ R) :
    ∀ k, k + 1 ≤ R →
      CombSizeBound (R - 2) (R + 2 * R * k) (2 * R * (2 * R ^ 2) ^ k)
        (VCombAux k R) := by
  intro k
  induction k with
  | zero =>
      intro _
      have hbase : CombSizeBound (R - 2) R (2 * R) (VCombAux 0 R) := by
        rw [VCombAux_zero]
        refine ⟨?_, ?_, ?_, ?_⟩
        · refine le_trans (maxIdx_shiftComb_le _ _) (max_le ?_ ?_)
          · exact le_trans (maxIdx_AComb_le (R - 1)) (by omega)
          · exact le_trans (vecMaxIdx_single_le _ _) (by omega)
        · intro ν' hν' j hj
          obtain ⟨ν, hν, rfl⟩ := mem_shiftComb_support hν'
          rw [Finsupp.sub_apply] at hj
          have hsingle : (0 : ℤ) ≤ (Finsupp.single (R - 2) (1 : ℤ)) j := by
            rw [Finsupp.single_apply]
            split <;> omega
          have hjmem : j ∈ ν.support := Finsupp.mem_support_iff.mpr (by omega)
          have h := AComb_support_index_le hν j hjmem
          omega
        · refine le_trans (combHeight_shiftComb_le _ _) ?_
          have h1 := combHeight_AComb_le (R - 1)
          have h2 : height (Finsupp.single (R - 2) (1 : ℤ)) = 1 := by
            rw [height_single]
            rfl
          omega
        · rw [l1Norm_shiftComb]
          exact le_trans (l1Norm_AComb_le (by omega : 2 ≤ R - 1)) (by omega)
      exact hbase.mono (Nat.le_of_eq (by ring)) (Nat.le_of_eq (by ring))
  | succ k ih =>
      intro hk1
      have h := (ih (by omega)).backward_step (r := R - (k + 1))
        (by omega : R - (k + 1) ≤ (R - 2) + 2)
      rw [← VCombAux_succ] at h
      refine h.mono ?_ ?_
      · exact height_backward_step (by omega)
      · exact norm_backward_step (by omega)

/-- Size invariants for the `V`-half after `k` backward steps and `m`
further formal derivatives. -/
theorem VCombAux_sizeBound {R : ℕ} (hR : 8 ≤ R) (k : ℕ) :
    ∀ m, k + m + 1 ≤ R →
      CombSizeBound (R - 2) (R + 2 * R * (k + m))
        (2 * R * (2 * R ^ 2) ^ (k + m)) (derivComb^[m] (VCombAux k R)) := by
  intro m
  induction m with
  | zero =>
      intro hkm
      exact VCombAux_sizeBound_base hR k (by omega)
  | succ m ih =>
      intro hkm
      rw [Function.iterate_succ_apply']
      have h := (ih (by omega)).derivComb_step
      refine h.mono ?_ ?_
      · exact height_backward_step (by omega)
      · exact norm_backward_step (by omega)

/-- Persistence of the terminal inverse factor `x_{R−3}^{−1}` in the
`U`-half, valid **after the first backward step** (`k ≥ 1`): the seed
`A_{R−2}` has coordinate `0` at `R − 3`, and the first shift by
`aVec (R−1) = stairVec (R−3)` subtracts `1` there ("every monomial in the
first polynomial contains `x_{R−3}^{−1}` and no variable of higher
index"). -/
theorem UCombAux_apply_le_neg_one {R : ℕ} (hR : 8 ≤ R) :
    ∀ k, 1 ≤ k → k + 1 ≤ R →
      ∀ μ ∈ (UCombAux k R).support, μ (R - 3) ≤ -1 := by
  intro k
  induction k with
  | zero => exact fun h => absurd h (by omega)
  | succ k ih =>
      intro _ hk1
      rcases Nat.eq_zero_or_pos k with rfl | hkpos
      · intro μ hμ
        rw [UCombAux_succ, UCombAux_zero] at hμ
        obtain ⟨ν, hν, rfl⟩ := mem_shiftComb_support hμ
        have hν3 : ν (R - 3) ≤ 0 := by
          obtain ⟨ν₀, hν₀, j, hj, rfl⟩ := exists_of_mem_derivComb_support hν
          have h0 : ν₀ (R - 3) = 0 := AComb_apply_eq_zero hν₀ (by omega)
          have hj3 : j ≤ R - 3 := by
            have h := AComb_support_index_le hν₀ j hj
            omega
          have hds := derivShift_apply_nonpos hj3
          rw [Finsupp.add_apply]
          omega
        have haV : aVec (R - (0 + 1)) (R - 3) = 1 := by
          show stairVec (R - 1 - 2) (R - 3) = 1
          rw [show R - 1 - 2 = R - 3 by omega, stairVec_apply,
            if_pos (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)]
        rw [Finsupp.sub_apply, haV]
        omega
      · intro μ hμ
        rw [UCombAux_succ] at hμ
        have hmax : maxIdx (UCombAux k R) ≤ R - 3 :=
          (UCombAux_sizeBound_base hR k (by omega)).maxIdx_le
        exact shiftComb_apply_le_neg_one (aVec_apply_nonneg _ _)
          (derivComb_apply_le_neg_one hmax (ih hkpos (by omega))) μ hμ

/-- Persistence of the terminal inverse factor `x_{R−2}^{−1}` in the
`V`-half, valid from `k = 0` on (the seed is already shifted by
`x_{R−2}`). -/
theorem VCombAux_apply_le_neg_one {R : ℕ} (hR : 8 ≤ R) :
    ∀ k, k + 1 ≤ R → ∀ μ ∈ (VCombAux k R).support, μ (R - 2) ≤ -1 := by
  intro k
  induction k with
  | zero =>
      intro _ μ hμ
      rw [VCombAux_zero] at hμ
      obtain ⟨ν, hν, rfl⟩ := mem_shiftComb_support hμ
      have h0 : ν (R - 2) = 0 := AComb_apply_eq_zero hν (by omega)
      rw [Finsupp.sub_apply, h0, Finsupp.single_eq_same]
      omega
  | succ k ih =>
      intro hk1 μ hμ
      rw [VCombAux_succ] at hμ
      have hmax : maxIdx (VCombAux k R) ≤ R - 2 :=
        (VCombAux_sizeBound_base hR k (by omega)).maxIdx_le
      exact shiftComb_apply_le_neg_one (aVec_apply_nonneg _ _)
        (derivComb_apply_le_neg_one hmax (ih (by omega))) μ hμ

/-! ## Evaluation bounds for the two halves
(eqs. `late-U-bound`, `late-V-bound`) -/

/-- Shared engine behind `late-U-bound`/`late-V-bound`: for a comb `P` with
the `(k+m)`-size invariant at terminal inverse index `b` and top phase index
`a`, one has `|∂_u^m P| ≤ 2R(2R²)^{k+m} E_a^{2R²} / E_b`.  The `U`-half calls
it with `(a,b) = (R−4, R−3)`, the `V`-half with `(a,b) = (R−3, R−2)`. -/
private theorem abs_evalComb_derivIter_le_aux {R k m a b : ℕ} (hR : 8 ≤ R)
    (hkm : k + m + 1 ≤ R) {u : ℝ} (hu : 1 ≤ u) {P : LaurentComb}
    (hSB : CombSizeBound b (R + 2 * R * (k + m))
      (2 * R * (2 * R ^ 2) ^ (k + m)) P)
    (hbound : ∀ ν ∈ P.support, ∀ j ∈ ν.support, 0 < ν j → E j u ≤ E a u)
    (hneg : ∀ ν ∈ P.support, ν b ≤ -1) :
    |evalComb P u|
      ≤ 2 * (R : ℝ) * (2 * (R : ℝ) ^ 2) ^ (k + m)
          * E a u ^ (2 * R ^ 2) / E b u := by
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu
  have hxmax1 : (1 : ℝ) ≤ E a u := one_le_E_of_one_le hu _
  refine (abs_evalComb_le_div hu hxmax1 hbound hneg).trans ?_
  have hpd : combPosDeg P ≤ 2 * R ^ 2 := by
    refine le_trans (combPosDeg_le_combHeight _)
      (le_trans hSB.combHeight_le ?_)
    calc R + 2 * R * (k + m) = R * (2 * (k + m) + 1) := by ring
      _ ≤ R * (2 * R) := Nat.mul_le_mul_left R (by omega)
      _ = 2 * R ^ 2 := by ring
  have hl1 : (l1Norm P : ℝ)
      ≤ 2 * (R : ℝ) * (2 * (R : ℝ) ^ 2) ^ (k + m) := by
    calc (l1Norm P : ℝ)
        ≤ ((2 * R * (2 * R ^ 2) ^ (k + m) : ℕ) : ℝ) :=
          Nat.cast_le.mpr hSB.l1Norm_le
      _ = 2 * (R : ℝ) * (2 * (R : ℝ) ^ 2) ^ (k + m) := by push_cast; ring
  refine div_le_div_of_nonneg_right ?_ (E_pos_of_pos hu0 _).le
  exact mul_le_mul hl1 (pow_le_pow_right₀ hxmax1 hpd)
    (pow_nonneg (by linarith : (0 : ℝ) ≤ E a u) _) (by positivity)

/-- Eq. `late-U-bound` (in the sharper `k + m`-exponent form):
`|∂_u^m U| ≤ 2R (2R²)^{k+m} E_{R−4}^{2R²} / E_{R−3}` for `u ≥ 1`, after
`k ≥ 1` backward steps and `m` derivatives with `k + m + 1 ≤ R`. -/
theorem abs_evalComb_derivIter_UCombAux_le {R k m : ℕ} (hR : 8 ≤ R)
    (hk : 1 ≤ k) (hkm : k + m + 1 ≤ R) {u : ℝ} (hu : 1 ≤ u) :
    |evalComb (derivComb^[m] (UCombAux k R)) u|
      ≤ 2 * (R : ℝ) * (2 * (R : ℝ) ^ 2) ^ (k + m)
          * E (R - 4) u ^ (2 * R ^ 2) / E (R - 3) u := by
  have hSB := UCombAux_sizeBound hR k m hkm
  refine abs_evalComb_derivIter_le_aux hR hkm hu hSB ?_ ?_
  · intro ν hν j _ hj
    have h := hSB.pos_index_le ν hν j hj
    exact E_mono_depth hu (by omega : j ≤ R - 4)
  · have hmax0 : maxIdx (UCombAux k R) ≤ R - 3 :=
      (UCombAux_sizeBound_base hR k (by omega)).maxIdx_le
    exact derivComb_iterate_apply_le_neg_one hmax0
      (UCombAux_apply_le_neg_one hR k hk (by omega)) m

/-- Eq. `late-V-bound` (in the sharper `k + m`-exponent form):
`|∂_u^m V| ≤ 2R (2R²)^{k+m} E_{R−3}^{2R²} / E_{R−2}` for `u ≥ 1`, valid
from `k = 0` on with `k + m + 1 ≤ R`. -/
theorem abs_evalComb_derivIter_VCombAux_le {R k m : ℕ} (hR : 8 ≤ R)
    (hkm : k + m + 1 ≤ R) {u : ℝ} (hu : 1 ≤ u) :
    |evalComb (derivComb^[m] (VCombAux k R)) u|
      ≤ 2 * (R : ℝ) * (2 * (R : ℝ) ^ 2) ^ (k + m)
          * E (R - 3) u ^ (2 * R ^ 2) / E (R - 2) u := by
  have hSB := VCombAux_sizeBound hR k m hkm
  refine abs_evalComb_derivIter_le_aux hR hkm hu hSB ?_ ?_
  · intro ν hν j _ hj
    have h := hSB.pos_index_le ν hν j hj
    exact E_mono_depth hu (by omega : j ≤ R - 3)
  · have hmax0 : maxIdx (VCombAux k R) ≤ R - 2 :=
      (VCombAux_sizeBound_base hR k (by omega)).maxIdx_le
    exact derivComb_iterate_apply_le_neg_one hmax0
      (VCombAux_apply_le_neg_one hR k (by omega)) m

/-! ## The clean exponential form (eq. `reference-increment`) -/

/-- `R³ ≤ E_{R−5}(1)` for `R ≥ 8` (the paper's "one has `x ≥ R³` — start
with `E₃(1) > 8³` and exponentiate"). -/
theorem R_cubed_le_E_sub_five {R : ℕ} (hR : 8 ≤ R) :
    ((R : ℝ)) ^ 3 ≤ E (R - 5) 1 := by
  induction R, hR using Nat.le_induction with
  | base =>
      have h := E_three_one_gt
      show ((8 : ℕ) : ℝ) ^ 3 ≤ E 3 1
      norm_num
      linarith
  | succ R hR ih =>
      have hidx : R + 1 - 5 = (R - 5) + 1 := by omega
      rw [hidx, E_succ]
      have h8 : (8 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
      have hy512 : (512 : ℝ) ≤ E (R - 5) 1 := by
        have hc : (8 : ℝ) ^ 3 ≤ (R : ℝ) ^ 3 :=
          pow_le_pow_left₀ (by norm_num) h8 3
        have h83 : (8 : ℝ) ^ 3 = 512 := by norm_num
        linarith
      have hsq : E (R - 5) 1 ^ 2 / 2 ≤ Real.exp (E (R - 5) 1) := by
        have h := pow_div_factorial_le_exp
          (by linarith : (0 : ℝ) ≤ E (R - 5) 1) 2
        have hfac : ((Nat.factorial 2 : ℕ) : ℝ) = 2 := by norm_num
        rwa [hfac] at h
      have h2R : (R : ℝ) + 1 ≤ 2 * (R : ℝ) := by linarith
      have hcube : ((R : ℝ) + 1) ^ 3 ≤ (2 * (R : ℝ)) ^ 3 :=
        pow_le_pow_left₀ (by linarith) h2R 3
      have hcube' : (2 * (R : ℝ)) ^ 3 = 8 * (R : ℝ) ^ 3 := by ring
      have h8y : 8 * E (R - 5) 1 ≤ E (R - 5) 1 ^ 2 / 2 := by
        nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ E (R - 5) 1 - 16)
          (by linarith : (0 : ℝ) ≤ E (R - 5) 1)]
      have hcast : (((R : ℕ) + 1 : ℕ) : ℝ) = (R : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      linarith

/-- The paper's logarithmic estimate behind eq. `reference-increment`: for
`R ≥ 8` and `x ≥ R³`, `2R (2R²)^R (e^x)^{2R²} ≤ exp(e^x/2)`.  (Taking
logarithms: `log 2R + R log 2R² + 2R²x ≤ R + R² + 2R²x ≤ 4x² ≤ e^x/2`.) -/
theorem poly_factor_le_exp_half {R : ℕ} (hR : 8 ≤ R) {x : ℝ}
    (hx : ((R : ℝ)) ^ 3 ≤ x) :
    2 * (R : ℝ) * (2 * (R : ℝ) ^ 2) ^ R * Real.exp x ^ (2 * R ^ 2)
      ≤ Real.exp (Real.exp x / 2) := by
  have hR8 : (8 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  have hRpos : (0 : ℝ) < (R : ℝ) := by linarith
  have hx512 : (512 : ℝ) ≤ x := by
    have hc : (8 : ℝ) ^ 3 ≤ (R : ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) hR8 3
    have h83 : (8 : ℝ) ^ 3 = 512 := by norm_num
    linarith
  have hx0 : (0 : ℝ) ≤ x := by linarith
  -- `2R² ≤ exp R` (via the Taylor term `R⁴/24`)
  have hexpR : 2 * (R : ℝ) ^ 2 ≤ Real.exp (R : ℝ) := by
    have h := pow_div_factorial_le_exp hRpos.le 4
    have hfac : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num
    rw [hfac] at h
    have hRsq : (64 : ℝ) ≤ (R : ℝ) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hRsq (sq_nonneg (R : ℝ))]
  have h2R : 2 * (R : ℝ) ≤ Real.exp (R : ℝ) := by
    nlinarith [hexpR, mul_nonneg hRpos.le (by linarith : (0 : ℝ) ≤ (R : ℝ) - 1)]
  have hpowRR : (2 * (R : ℝ) ^ 2) ^ R ≤ Real.exp ((R : ℝ) ^ 2) := by
    calc (2 * (R : ℝ) ^ 2) ^ R ≤ Real.exp (R : ℝ) ^ R :=
          pow_le_pow_left₀ (by positivity) hexpR R
      _ = Real.exp ((R : ℕ) * (R : ℝ)) := (Real.exp_nat_mul _ R).symm
      _ = Real.exp ((R : ℝ) ^ 2) := by
          congr 1
          ring
  have hxpow : Real.exp x ^ (2 * R ^ 2)
      = Real.exp (2 * (R : ℝ) ^ 2 * x) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hLHS : 2 * (R : ℝ) * (2 * (R : ℝ) ^ 2) ^ R * Real.exp x ^ (2 * R ^ 2)
      ≤ Real.exp ((R : ℝ) + (R : ℝ) ^ 2 + 2 * (R : ℝ) ^ 2 * x) := by
    rw [hxpow, Real.exp_add, Real.exp_add]
    have h1 : 2 * (R : ℝ) * (2 * (R : ℝ) ^ 2) ^ R
        ≤ Real.exp (R : ℝ) * Real.exp ((R : ℝ) ^ 2) :=
      mul_le_mul h2R hpowRR (by positivity) (Real.exp_pos _).le
    exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
  -- `R ≤ x` and `R² ≤ x` from `R³ ≤ x`
  have hstep1 : 8 * (R : ℝ) ≤ (R : ℝ) ^ 2 := by
    nlinarith [mul_nonneg hRpos.le (by linarith : (0 : ℝ) ≤ (R : ℝ) - 8)]
  have hstep2 : 8 * (R : ℝ) ^ 2 ≤ (R : ℝ) ^ 3 := by
    nlinarith [mul_nonneg (sq_nonneg (R : ℝ))
      (by linarith : (0 : ℝ) ≤ (R : ℝ) - 8)]
  have hRx : (R : ℝ) ≤ x := by nlinarith
  have hR2x : (R : ℝ) ^ 2 ≤ x := by nlinarith
  -- `8x² ≤ exp x` (via the Taylor term `x⁴/24`)
  have hexpx : 8 * x ^ 2 ≤ Real.exp x := by
    have h := pow_div_factorial_le_exp hx0 4
    have hfac : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num
    rw [hfac] at h
    have hxsq : (192 : ℝ) ≤ x ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hxsq (sq_nonneg x)]
  have hsum : (R : ℝ) + (R : ℝ) ^ 2 + 2 * (R : ℝ) ^ 2 * x ≤ 4 * x ^ 2 := by
    have hprod : (R : ℝ) ^ 2 * x ≤ x ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_right hR2x hx0]
    nlinarith [hRx, hR2x, hx512, hprod]
  refine hLHS.trans (Real.exp_le_exp.mpr ?_)
  linarith

/-- **The increment bound** (eq. `reference-increment`): for `R ≥ 8`,
`4 ≤ s ≤ R − 1`, `m ≤ 2`, and `u ≥ 1`,
`|evalComb (derivComb^[m] (DeltaComb s R)) u| ≤ 2 exp(−E_{R−4}(u)/2)` —
i.e. `|∂_u^m (Q_s^{[R+1]} − Q_s^{[R]})| ≤ 2 exp(−E_{R−4}/2)` through the
bridges `Qref_succ_sub_eval` / `hasDerivAt_evalComb_iterate`. -/
theorem abs_evalComb_derivIter_DeltaComb_le {s R : ℕ} (hR : 8 ≤ R)
    (hs : 4 ≤ s) (hsR : s + 1 ≤ R) {m : ℕ} (hm : m ≤ 2) {u : ℝ}
    (hu : 1 ≤ u) :
    |evalComb (derivComb^[m] (DeltaComb s R)) u|
      ≤ 2 * Real.exp (-(E (R - 4) u) / 2) := by
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu
  have hk1 : 1 ≤ R - s := by omega
  have hkm : (R - s) + m + 1 ≤ R := by omega
  have hsplit : derivComb^[m] (DeltaComb s R)
      = derivComb^[m] (UCombAux (R - s) R)
        + derivComb^[m] (VCombAux (R - s) R) := by
    rw [show DeltaComb s R = DeltaCombAux (R - s) R from rfl,
      DeltaCombAux_eq_UCombAux_add_VCombAux, derivComb_iterate_add]
  have hRcube : ((R : ℝ)) ^ 3 ≤ E (R - 5) u :=
    le_trans (R_cubed_le_E_sub_five hR) (E_mono (R - 5) hu)
  have hE4 : E (R - 4) u = Real.exp (E (R - 5) u) := by
    rw [show R - 4 = (R - 5) + 1 by omega, E_succ]
  have hE3 : E (R - 3) u = Real.exp (E (R - 4) u) := by
    rw [show R - 3 = (R - 4) + 1 by omega, E_succ]
  have hE2 : E (R - 2) u = Real.exp (E (R - 3) u) := by
    rw [show R - 2 = (R - 3) + 1 by omega, E_succ]
  have hpowR : (2 * (R : ℝ) ^ 2) ^ ((R - s) + m) ≤ (2 * (R : ℝ) ^ 2) ^ R := by
    have hbase : (1 : ℝ) ≤ 2 * (R : ℝ) ^ 2 := by
      have h8 : (8 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
      nlinarith
    exact pow_le_pow_right₀ hbase (by omega)
  -- the U half: `≤ exp(−E_{R−4}/2)`
  have hUkey : 2 * (R : ℝ) * (2 * (R : ℝ) ^ 2) ^ R * E (R - 4) u ^ (2 * R ^ 2)
      ≤ Real.exp (E (R - 4) u / 2) := by
    rw [hE4]
    exact poly_factor_le_exp_half hR hRcube
  have hU : |evalComb (derivComb^[m] (UCombAux (R - s) R)) u|
      ≤ Real.exp (-(E (R - 4) u) / 2) := by
    refine (abs_evalComb_derivIter_UCombAux_le hR hk1 hkm hu).trans ?_
    rw [hE3, div_le_iff₀ (Real.exp_pos _)]
    calc 2 * (R : ℝ) * (2 * (R : ℝ) ^ 2) ^ ((R - s) + m)
          * E (R - 4) u ^ (2 * R ^ 2)
        ≤ 2 * (R : ℝ) * (2 * (R : ℝ) ^ 2) ^ R * E (R - 4) u ^ (2 * R ^ 2) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpowR (by positivity))
            (pow_nonneg (E_pos_of_pos hu0 _).le _)
      _ ≤ Real.exp (E (R - 4) u / 2) := hUkey
      _ = Real.exp (-(E (R - 4) u) / 2) * Real.exp (E (R - 4) u) := by
          rw [← Real.exp_add]
          congr 1
          ring
  -- the V half: `≤ exp(−E_{R−3}/2) ≤ exp(−E_{R−4}/2)`
  have hRcube' : ((R : ℝ)) ^ 3 ≤ E (R - 4) u := by
    refine le_trans hRcube ?_
    rw [hE4]
    linarith [Real.add_one_le_exp (E (R - 5) u)]
  have hVkey : 2 * (R : ℝ) * (2 * (R : ℝ) ^ 2) ^ R * E (R - 3) u ^ (2 * R ^ 2)
      ≤ Real.exp (E (R - 3) u / 2) := by
    rw [hE3]
    exact poly_factor_le_exp_half hR hRcube'
  have hV : |evalComb (derivComb^[m] (VCombAux (R - s) R)) u|
      ≤ Real.exp (-(E (R - 3) u) / 2) := by
    refine (abs_evalComb_derivIter_VCombAux_le hR hkm hu).trans ?_
    rw [hE2, div_le_iff₀ (Real.exp_pos _)]
    calc 2 * (R : ℝ) * (2 * (R : ℝ) ^ 2) ^ ((R - s) + m)
          * E (R - 3) u ^ (2 * R ^ 2)
        ≤ 2 * (R : ℝ) * (2 * (R : ℝ) ^ 2) ^ R * E (R - 3) u ^ (2 * R ^ 2) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpowR (by positivity))
            (pow_nonneg (E_pos_of_pos hu0 _).le _)
      _ ≤ Real.exp (E (R - 3) u / 2) := hVkey
      _ = Real.exp (-(E (R - 3) u) / 2) * Real.exp (E (R - 3) u) := by
          rw [← Real.exp_add]
          congr 1
          ring
  have hVle : Real.exp (-(E (R - 3) u) / 2) ≤ Real.exp (-(E (R - 4) u) / 2) := by
    refine Real.exp_le_exp.mpr ?_
    have h34 : E (R - 4) u ≤ E (R - 3) u := by
      rw [hE3]
      linarith [Real.add_one_le_exp (E (R - 4) u)]
    linarith
  rw [hsplit, evalComb_add]
  refine le_trans (abs_add_le _ _) ?_
  linarith

/-! ## Geometric decay of the increments, the limit `Q_s^*`, and the tail -/

/-- Doubling per depth: `2^i E_j(u) ≤ E_{j+i}(u)` for `u ≥ 1` (each
exponentiation at least doubles, `two_mul_le_exp`). -/
theorem two_pow_mul_E_le_E_add_index {u : ℝ} (hu : 1 ≤ u) (j i : ℕ) :
    (2 : ℝ) ^ i * E j u ≤ E (j + i) u := by
  induction i with
  | zero => simp
  | succ i ih =>
      have hu0 : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu
      have hE : (0 : ℝ) ≤ E (j + i) u := (E_pos_of_pos hu0 _).le
      have h2 : 2 * E (j + i) u ≤ E (j + i + 1) u := by
        rw [E_succ]
        exact two_mul_le_exp hE
      calc (2 : ℝ) ^ (i + 1) * E j u = 2 * ((2 : ℝ) ^ i * E j u) := by ring
        _ ≤ 2 * E (j + i) u := by linarith
        _ ≤ E (j + (i + 1)) u := h2

/-- Super-geometric decay of the exponential weights:
`exp(−E_{j+i}/2) ≤ exp(−E_j/2) · (1/2)^i` for `u ≥ 1`, `j ≥ 1`
(from `E_{j+i} ≥ 2^i E_j ≥ (i+1) E_j` and `exp(−E_j/2) ≤ 1/2`). -/
theorem exp_neg_E_add_le {u : ℝ} (hu : 1 ≤ u) {j : ℕ} (hj : 1 ≤ j) (i : ℕ) :
    Real.exp (-(E (j + i) u) / 2)
      ≤ Real.exp (-(E j u) / 2) * (1 / 2 : ℝ) ^ i := by
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu
  have hE0 : (0 : ℝ) < E j u := E_pos_of_pos hu0 j
  have h2i := two_pow_mul_E_le_E_add_index hu j i
  have hip : ((i : ℝ) + 1) ≤ (2 : ℝ) ^ i := by
    have h := Nat.lt_two_pow_self (n := i)
    exact_mod_cast Nat.succ_le_of_lt h
  have hii : ((i : ℝ) + 1) * E j u ≤ E (j + i) u :=
    le_trans (mul_le_mul_of_nonneg_right hip hE0.le) h2i
  have hexp : Real.exp (-(E (j + i) u) / 2)
      ≤ Real.exp (-(((i : ℝ) + 1) * E j u) / 2) := by
    refine Real.exp_le_exp.mpr ?_
    linarith
  refine le_trans hexp ?_
  have hpow : Real.exp (-(((i : ℝ) + 1) * E j u) / 2)
      = Real.exp (-(E j u) / 2) * Real.exp (-(E j u) / 2) ^ i := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  rw [hpow]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  refine pow_le_pow_left₀ (Real.exp_pos _).le ?_ i
  have hT2 : (2 : ℝ) ≤ E j u := two_le_E hj hu
  have h1 : Real.exp (-(E j u) / 2) ≤ Real.exp (-1 : ℝ) :=
    Real.exp_le_exp.mpr (by linarith)
  have h2e : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hinv : (1 : ℝ) / Real.exp 1 ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) h2e
  have hexpneg : Real.exp (-1 : ℝ) = 1 / Real.exp 1 := by
    rw [Real.exp_neg, inv_eq_one_div]
  linarith [h1, hexpneg ▸ h1]

/-- `Q_s^*` (the limit of `lem:backward-reference-convergence`), realized as
the first finite reference function plus the convergent series of increments
`Δ_{s,R} = Q_s^{[R+1]} − Q_s^{[R]}` (eq. `reference-defect`). -/
noncomputable def QrefLimit (s : ℕ) : ℝ → ℝ := fun u =>
  Qref s (s + 1) u + ∑' k : ℕ, evalComb (DeltaComb s (s + 1 + k)) u

/-- Telescoping the increments: `Q_s^{[s+1+n]}` equals `Q_s^{[s+1]}` plus
the first `n` increments. -/
theorem Qref_eq_add_sum_DeltaComb {s : ℕ} (hs : 4 ≤ s) (n : ℕ) {u : ℝ}
    (hu : 0 < u) :
    Qref s (s + 1 + n) u
      = Qref s (s + 1) u
        + ∑ k ∈ Finset.range n, evalComb (DeltaComb s (s + 1 + k)) u := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have h := Qref_succ_sub_eval hs (show s ≤ s + 1 + n by omega) hu
      show Qref s (s + 1 + n + 1) u = _
      linarith [ih, h]

/-- Summability of the increment series at every phase `u ≥ 1` (comparison
with a geometric series via eq. `reference-increment`; the finitely many
depths below `R = 8` are absorbed by an index shift). -/
theorem summable_evalComb_DeltaComb {s : ℕ} (hs : 4 ≤ s) {u : ℝ}
    (hu : 1 ≤ u) :
    Summable fun k : ℕ => evalComb (DeltaComb s (s + 1 + k)) u := by
  rw [← summable_nat_add_iff 7]
  refine Summable.of_abs ?_
  have hg : Summable fun k : ℕ =>
      2 * Real.exp (-(E (s + 4) u) / 2) * (1 / 2 : ℝ) ^ k :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  refine Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_) hg
  have hb := abs_evalComb_derivIter_DeltaComb_le (s := s)
    (R := s + 1 + (k + 7)) (m := 0) (by omega) hs (by omega) (by omega) hu
  simp only [Function.iterate_zero_apply] at hb
  have hidx : s + 1 + (k + 7) - 4 = (s + 4) + k := by omega
  rw [hidx] at hb
  refine hb.trans ?_
  have hdecay := exp_neg_E_add_le hu (j := s + 4) (by omega) k
  linarith

/-- **Convergence of the reference functions** (pointwise half of
`lem:backward-reference-convergence`): for fixed `s ≥ 4` and `u ≥ 1`,
`Q_s^{[R]}(u) → Q_s^*(u)` as the terminal depth `R → ∞`. -/
theorem Qref_tendsto_QrefLimit {s : ℕ} (hs : 4 ≤ s) {u : ℝ} (hu : 1 ≤ u) :
    Filter.Tendsto (fun R : ℕ => Qref s R u) Filter.atTop
      (nhds (QrefLimit s u)) := by
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu
  have hsum := summable_evalComb_DeltaComb hs hu
  have hcomp := hsum.hasSum.tendsto_sum_nat.comp
    (Filter.tendsto_sub_atTop_nat (s + 1))
  have hadd := hcomp.const_add (Qref s (s + 1) u)
  refine Filter.Tendsto.congr' ?_ hadd
  filter_upwards [Filter.eventually_ge_atTop (s + 1)] with R hR
  have h := Qref_eq_add_sum_DeltaComb hs (R - (s + 1)) hu0
  rw [show s + 1 + (R - (s + 1)) = R by omega] at h
  exact h.symm

/-- The tail of the increment series is dominated by twice its first term
(the paper's "the resulting series is dominated by twice its first term"),
stated over the depth gap `n = R − (s + 1)`. -/
theorem abs_tsum_DeltaComb_tail_le {s n : ℕ} (hs : 4 ≤ s)
    (hR : 8 ≤ s + 1 + n) {u : ℝ} (hu : 1 ≤ u) :
    |∑' k : ℕ, evalComb (DeltaComb s (s + 1 + (k + n))) u|
      ≤ 4 * Real.exp (-(E (s + 1 + n - 4) u) / 2) := by
  have hsum := summable_evalComb_DeltaComb hs hu
  have hshift : Summable fun k : ℕ =>
      evalComb (DeltaComb s (s + 1 + (k + n))) u :=
    (summable_nat_add_iff
      (f := fun k : ℕ => evalComb (DeltaComb s (s + 1 + k)) u) n).mpr hsum
  have habs : Summable fun k : ℕ =>
      |evalComb (DeltaComb s (s + 1 + (k + n))) u| := hshift.abs
  have hterm : ∀ k : ℕ, |evalComb (DeltaComb s (s + 1 + (k + n))) u|
      ≤ 2 * Real.exp (-(E (s + 1 + n - 4) u) / 2) * (1 / 2 : ℝ) ^ k := by
    intro k
    have hb := abs_evalComb_derivIter_DeltaComb_le (s := s)
      (R := s + 1 + (k + n)) (m := 0) (by omega) hs (by omega) (by omega) hu
    simp only [Function.iterate_zero_apply] at hb
    have hidx : s + 1 + (k + n) - 4 = (s + 1 + n - 4) + k := by omega
    rw [hidx] at hb
    have hdecay := exp_neg_E_add_le hu (j := s + 1 + n - 4) (by omega) k
    linarith [hb, hdecay]
  have hgsum : Summable fun k : ℕ =>
      2 * Real.exp (-(E (s + 1 + n - 4) u) / 2) * (1 / 2 : ℝ) ^ k :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hnorm : ‖∑' k : ℕ, evalComb (DeltaComb s (s + 1 + (k + n))) u‖
      ≤ ∑' k : ℕ, ‖evalComb (DeltaComb s (s + 1 + (k + n))) u‖ :=
    norm_tsum_le_tsum_norm (by simpa only [Real.norm_eq_abs] using habs)
  simp only [Real.norm_eq_abs] at hnorm
  calc |∑' k : ℕ, evalComb (DeltaComb s (s + 1 + (k + n))) u|
      ≤ ∑' k : ℕ, |evalComb (DeltaComb s (s + 1 + (k + n))) u| := hnorm
    _ ≤ ∑' k : ℕ, 2 * Real.exp (-(E (s + 1 + n - 4) u) / 2) * (1 / 2 : ℝ) ^ k :=
        habs.tsum_le_tsum hterm hgsum
    _ = 2 * Real.exp (-(E (s + 1 + n - 4) u) / 2) * ∑' k : ℕ, (1 / 2 : ℝ) ^ k :=
        tsum_mul_left
    _ = 4 * Real.exp (-(E (s + 1 + n - 4) u) / 2) := by
        rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
        norm_num
        ring

/-- **Quantitative tail** for the limit: for `s ≥ 4`, `R ≥ max 8 (s+1)`,
and `u ≥ 1`, `|Q_s^* − Q_s^{[R]}| ≤ 4 exp(−E_{R−4}(u)/2)` — the paper's
"the resulting series is dominated by twice its first term". -/
theorem abs_QrefLimit_sub_Qref {s R : ℕ} (hs : 4 ≤ s) (hR : 8 ≤ R)
    (hsR : s + 1 ≤ R) {u : ℝ} (hu : 1 ≤ u) :
    |QrefLimit s u - Qref s R u| ≤ 4 * Real.exp (-(E (R - 4) u) / 2) := by
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu
  obtain ⟨n, rfl⟩ : ∃ n, R = s + 1 + n := ⟨R - (s + 1), by omega⟩
  have hsum := summable_evalComb_DeltaComb hs hu
  have hQ := Qref_eq_add_sum_DeltaComb hs n hu0
  have hsplit : (∑ k ∈ Finset.range n, evalComb (DeltaComb s (s + 1 + k)) u)
      + ∑' k : ℕ, evalComb (DeltaComb s (s + 1 + (k + n))) u
      = ∑' k : ℕ, evalComb (DeltaComb s (s + 1 + k)) u :=
    Summable.sum_add_tsum_nat_add
      (f := fun k : ℕ => evalComb (DeltaComb s (s + 1 + k)) u) n hsum
  have hQL : QrefLimit s u
      = Qref s (s + 1) u
        + ∑' k : ℕ, evalComb (DeltaComb s (s + 1 + k)) u := rfl
  have hdiff : QrefLimit s u - Qref s (s + 1 + n) u
      = ∑' k : ℕ, evalComb (DeltaComb s (s + 1 + (k + n))) u := by
    rw [hQL, hQ]
    linarith [hsplit]
  rw [hdiff]
  exact abs_tsum_DeltaComb_tail_le hs (by omega) hu

end Erdos320
