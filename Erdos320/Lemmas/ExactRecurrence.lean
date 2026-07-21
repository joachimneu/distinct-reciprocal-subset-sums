import Erdos320.Lemmas.BSlopes
import Erdos320.Lemmas.IteratedExpBounds
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The exact differentiated recurrence for `H̄` (paper `lem:exact-recurrence`)

The manuscript's Lemma "Exact differentiated recurrence" (`lem:exact-recurrence`)
asserts, for every `r ≥ 3`, the identity (eq. `exact-recurrence`)
```
H̄_{r+1}'(u) = a_r(u) · (H̄_r(u) + ρ_r(u))     for a.e. u ∈ [1, e],
```
where `a_r = E_{r-2}'` and `ρ_r` is the recurrence error of eq. `a-rho`.  This
file formalizes the *identity* half of the lemma (the error bound
eq. `rho-small` is out of scope here; it is proved in `Threshold.lean`
(`rhoDepth_abs_le`) on top of the averaging relation
(`AveragingRelation.lean`)):

* `hasDerivAt_E_full` — the chain-rule factorization `E_r' = a_r · E_{r-1} · E_r`;
* `hasDerivAt_Hbar_succ` — the pointwise identity at every non-breakpoint
  phase (`𝓑` is differentiable there by `lem:B-slopes`);
* `E_breakpoint_phases_countable`, `badPhaseSet_countable` — the exceptional
  phase set is countable, so "almost every `u`" in the paper's statement is
  justified in the strong (countable-exception) sense;
* `hasDerivWithinAt_B_Ioi`, `hasDerivWithinAt_Hbar_succ_Ioi` — at *every*
  phase (breakpoints included) the identity holds for the right derivative,
  because `𝓑` is right-affine with slope `1/m_*` on `[X, g(m_*(X)))`;
* `Hbar_succ_sub_eq_integral` — the integral (fundamental-theorem) form of
  eq. `exact-recurrence`, the form consumed by the iteration lemma
  (`lem:iteration-endpoint-matching`) and the backward-stability argument;
* continuity/monotonicity/Lipschitz facts for `E`, `a`, `𝓑`, `H̄` used above
  and by the downstream consumers.

Note that the differentiated identity needs no
positivity or range restriction on `u` at all — for `r ≥ 3` every quantity
involved (`E_r(u)`, `E_{r-1}(u)`, `a_r(u)`) is automatically positive, so the
paper's restriction to `u ∈ [1, e]` matters only for the (out-of-scope) error
bound, not for eq. `exact-recurrence` itself.
-/

namespace Erdos320

open MeasureTheory

/-! ## Continuity, monotonicity, and Lipschitz bounds

Basic regularity of the ingredients of `lem:exact-recurrence`: the iterated
exponentials `E_j`, the chain-rule factor `a_r`, the concave average `𝓑`
(`1`-Lipschitz by `lem:B-slopes`), and the averaged function `H̄_r`. -/

/-- Each iterated exponential `E_j` is continuous (used for the
absolute-continuity statement implicit in `lem:exact-recurrence`). -/
theorem continuous_E (k : ℕ) : Continuous (E k) := by
  induction k with
  | zero => exact continuous_id
  | succ k ih => exact Real.continuous_exp.comp ih

/-- The chain-rule factor `a_r = ∏_{j=1}^{r-2} E_j` of eq. `a-rho` is
continuous. -/
theorem continuous_a (r : ℕ) : Continuous (a r) :=
  continuous_finsetProd _ fun j _ => continuous_E j

/-- `𝓑` is `1`-Lipschitz, in bundled form (`lem:B-slopes`, "locally absolutely
continuous"; repackaging `B_lipschitz`). -/
theorem lipschitzWith_B : LipschitzWith 1 B :=
  LipschitzWith.mk_one fun X Y => by
    rw [Real.dist_eq, Real.dist_eq]
    exact B_lipschitz Y X

/-- `𝓑` is continuous (from `1`-Lipschitz continuity, `lem:B-slopes`). -/
theorem continuous_B : Continuous B :=
  lipschitzWith_B.continuous

/-- `H̄_r = 𝓑 ∘ E_{r-1}` is continuous — the regularity half of "absolutely
continuous" needed to state `lem:exact-recurrence` in integral form. -/
theorem continuous_Hbar (r : ℕ) : Continuous (Hbar r) :=
  continuous_B.comp (continuous_E (r - 1))

/-- `H̄_r` is (globally) monotone: both `𝓑` (`lem:B-slopes`) and `E_{r-1}` are
monotone. -/
theorem Hbar_mono (r : ℕ) : Monotone (Hbar r) :=
  fun _ _ huv => B_mono (E_mono (r - 1) huv)

/-! ## The chain-rule factorization `E_r' = a_r · E_{r-1} · E_r`

The derivative computation opening the proof of `lem:exact-recurrence`:
`E_r'(u) = ∏_{j=1}^{r} E_j(u) = a_r(u) · E_{r-1}(u) · E_r(u)` (eq. `a-rho`). -/

/-- The chain-rule factorization of `lem:exact-recurrence`: for `r ≥ 2`,
`E_r'(u) = a_r(u) · E_{r-1}(u) · E_r(u)`, splitting off the top two factors
of the full product `∏_{j=1}^{r} E_j(u)`. -/
theorem hasDerivAt_E_full {r : ℕ} (hr : 2 ≤ r) (u : ℝ) :
    HasDerivAt (E r) (a r u * E (r - 1) u * E r u) u := by
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 2 := ⟨r - 2, by omega⟩
  have h := hasDerivAt_E (m + 2) u
  rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ m + 2),
    Finset.prod_Icc_succ_top (by omega : 1 ≤ m + 1)] at h
  exact h

/-! ## The pointwise exact recurrence (eq. `exact-recurrence`)

At every phase `u` where `E_r(u)` avoids the breakpoints `g(m)` of `𝓑`, the
paper's identity `H̄_{r+1}'(u) = a_r(u)(H̄_r(u) + ρ_r(u))` holds as a genuine
two-sided derivative; the excluded phase set is countable. -/

/-- Eq. `exact-recurrence` of `lem:exact-recurrence`, pointwise form: for
`r ≥ 3`, at every phase `u` with `E_r(u)` not a breakpoint of `g`,
`H̄_{r+1}'(u) = a_r(u) · (H̄_r(u) + ρ_r(u))`.  Chain rule from
`hasDerivAt_B` (`lem:B-slopes`, eq. `B-prime`) and `hasDerivAt_E_full`,
then the algebra of eq. `a-rho` (`rhoDepth_eq`).  No positivity or range
hypothesis on `u` is needed (see the module docstring). -/
theorem hasDerivAt_Hbar_succ {r : ℕ} (hr : 3 ≤ r) {u : ℝ}
    (hbp : ∀ m, g m ≠ E r u) :
    HasDerivAt (Hbar (r + 1)) (a r u * (Hbar r u + rhoDepth r u)) u := by
  have hEr : 0 < E r u := E_pos_of_one_le (by omega) u
  have hcomp := (hasDerivAt_B hEr hbp).comp u (hasDerivAt_E_full (by omega) u)
  have hfun : Hbar (r + 1) = B ∘ E r := by
    funext v
    simp only [Hbar, Function.comp_apply, Nat.add_sub_cancel]
  have hval : 1 / (mStar (E r u) : ℝ) * (a r u * E (r - 1) u * E r u)
      = a r u * (Hbar r u + rhoDepth r u) := by
    rw [rhoDepth_eq (by omega : 1 ≤ r), Hbar]
    ring
  rw [hfun, ← hval]
  exact hcomp

/-- The phases `u` at which `E_r(u)` hits a breakpoint of `g` form a countable
set: `E_r` is (strictly monotone, hence) injective, and the breakpoint set is
countable (`breakpoints_countable`, `lem:B-slopes`).  This justifies the
"for almost every `u`" of `lem:exact-recurrence`. -/
theorem E_breakpoint_phases_countable (r : ℕ) :
    Set.Countable {u : ℝ | ∃ m, g m = E r u} :=
  breakpoints_countable.preimage (E_strictMono r).injective

/-- Variant of `E_breakpoint_phases_countable` restricted to positive phases,
the exceptional set of the pointwise identity `hasDerivAt_Hbar_succ` on
`(0, ∞)` (`lem:exact-recurrence`, "for almost every `u ∈ [1, e]`"). -/
theorem badPhaseSet_countable (r : ℕ) :
    Set.Countable {u : ℝ | 0 < u ∧ ∃ m, g m = E r u} :=
  Set.Countable.mono (fun _ hu => hu.2) (E_breakpoint_phases_countable r)

/-! ## The right derivative at every phase, breakpoints included

`𝓑` is right-affine on `[X, g(m_*(X)))` with slope exactly `1/m_*(X)` — the
right-derivative form of eq. `B-prime` (as the paper states it:
`𝓑₊'(X) = 1/m_*(X)` at every `X ≥ 1`, breakpoints included).  Consequently the
recurrence identity holds for the *right* derivative of `H̄_{r+1}` at every
phase with no exceptional set, which is what the fundamental theorem of
calculus consumes. -/

/-- Right-affineness of `𝓑` (`lem:B-slopes`, right-derivative side): for
`0 ≤ X ≤ Y ≤ g(m_*(X))`, the increment is exactly `(Y − X)/m_*(X)` — every
term of paper index `< m_*(X)` is frozen and every later term moves in
full. -/
theorem B_right_affine {X Y : ℝ} (hX : 0 ≤ X) (hXY : X ≤ Y)
    (hY : Y ≤ g (mStar X)) :
    B Y - B X = (Y - X) / (mStar X : ℝ) := by
  have hk1 : 1 ≤ mStar X := mStar_pos hX
  rw [B_sub_eq_tsum]
  have hterm : ∀ m : ℕ,
      (min (g (m + 1)) Y - min (g (m + 1)) X) / ((m + 1 : ℝ) * (m + 2 : ℝ))
        = (Y - X) * weightTail (mStar X) m := by
    intro m
    rw [weightTail]
    split_ifs with h
    · have hg : g (mStar X) ≤ g (m + 1) := g_mono h
      rw [min_eq_right (hY.trans hg),
        min_eq_right ((lt_g_mStar X).le.trans hg), mul_one_div]
    · have hg : g (m + 1) ≤ X := g_le_of_lt_mStar (by omega)
      rw [min_eq_left (hg.trans hXY), min_eq_left hg, sub_self, zero_div,
        mul_zero]
  rw [tsum_congr hterm, tsum_mul_left, tsum_weightTail hk1, mul_one_div]

/-- At *every* `X ≥ 0` — breakpoints included — `𝓑` has right derivative
`1/m_*(X)` (`eq:B-prime`: `𝓑₊'(X) = 1/m_*(X)` for every `X ≥ 1`; at
`X = g(N)` this is `1/(N+1)`).  From the right-affineness `B_right_affine` on
`[X, g(m_*(X)))`. -/
theorem hasDerivWithinAt_B_Ioi {X : ℝ} (hX : 0 ≤ X) :
    HasDerivWithinAt B (1 / (mStar X : ℝ)) (Set.Ioi X) X := by
  have haffine : HasDerivAt (fun Y : ℝ => B X + (Y - X) / (mStar X : ℝ))
      (1 / (mStar X : ℝ)) X :=
    (((hasDerivAt_id X).sub_const X).div_const (mStar X : ℝ)).const_add (B X)
  refine haffine.hasDerivWithinAt.congr_of_eventuallyEq ?_ (by simp)
  filter_upwards [Ioo_mem_nhdsGT (lt_g_mStar X)] with Y hY
  have h := B_right_affine hX hY.1.le hY.2.le
  linarith

/-- Eq. `exact-recurrence` of `lem:exact-recurrence` in right-derivative form,
valid at **every** phase `u` (no breakpoint exclusion): for `r ≥ 3`,
`H̄_{r+1}` has right derivative `a_r(u) · (H̄_r(u) + ρ_r(u))` at `u`.  This is
the everywhere-valid strengthening feeding the fundamental theorem of
calculus in `Hbar_succ_sub_eq_integral`. -/
theorem hasDerivWithinAt_Hbar_succ_Ioi {r : ℕ} (hr : 3 ≤ r) (u : ℝ) :
    HasDerivWithinAt (Hbar (r + 1)) (a r u * (Hbar r u + rhoDepth r u))
      (Set.Ioi u) u := by
  have hEr : 0 < E r u := E_pos_of_one_le (by omega) u
  have hmaps : Set.MapsTo (E r) (Set.Ioi u) (Set.Ioi (E r u)) :=
    fun v hv => E_strictMono r hv
  have hcomp := (hasDerivWithinAt_B_Ioi hEr.le).comp u
    ((hasDerivAt_E_full (by omega : 2 ≤ r) u).hasDerivWithinAt) hmaps
  have hfun : Hbar (r + 1) = B ∘ E r := by
    funext v
    simp only [Hbar, Function.comp_apply, Nat.add_sub_cancel]
  have hval : 1 / (mStar (E r u) : ℝ) * (a r u * E (r - 1) u * E r u)
      = a r u * (Hbar r u + rhoDepth r u) := by
    rw [rhoDepth_eq (by omega : 1 ≤ r), Hbar]
    ring
  rw [hfun, ← hval]
  exact hcomp

/-! ## The integral form of the exact recurrence

The form of eq. `exact-recurrence` the iteration
(`lem:iteration-endpoint-matching`) and backward-stability arguments consume:
`H̄_{r+1}(y) − H̄_{r+1}(x) = ∫_x^y a_r(t)(H̄_r(t) + ρ_r(t)) dt`. -/

/-- The integrand of the exact recurrence, rewritten without `ρ_r`: by
eq. `a-rho` (`rhoDepth_eq`), `a_r(t)(H̄_r(t) + ρ_r(t)) =
a_r(t) E_r(t) E_{r-1}(t) / m_*(E_r(t))` — an identity valid at every `t`,
with no breakpoint or positivity condition (`lem:exact-recurrence`,
first display of the proof). -/
theorem recurrenceIntegrand_eq {r : ℕ} (hr : 1 ≤ r) (t : ℝ) :
    a r t * (Hbar r t + rhoDepth r t)
      = a r t * E r t * E (r - 1) t / (mStar (E r t) : ℝ) := by
  rw [rhoDepth_eq hr, Hbar]
  ring

/-- The recurrence integrand is interval integrable on every `[x, y]`
(`lem:exact-recurrence`, integrability of the right-hand side): in the
division form of `recurrenceIntegrand_eq` it is measurable — `m_* ∘ E_r` is a
monotone step function — and dominated by the continuous function
`a_r · E_r · E_{r-1}` since `m_*(E_r(t)) ≥ 1`. -/
theorem intervalIntegrable_recurrenceIntegrand {r : ℕ} (hr : 3 ≤ r)
    (x y : ℝ) :
    IntervalIntegrable (fun t => a r t * (Hbar r t + rhoDepth r t))
      volume x y := by
  have hfun : (fun t => a r t * (Hbar r t + rhoDepth r t))
      = fun t => a r t * E r t * E (r - 1) t / (mStar (E r t) : ℝ) :=
    funext fun t => recurrenceIntegrand_eq (by omega) t
  rw [hfun, intervalIntegrable_iff]
  have hG : Continuous fun t => a r t * E r t * E (r - 1) t :=
    ((continuous_a r).mul (continuous_E r)).mul (continuous_E (r - 1))
  have hGint : IntegrableOn (fun t => a r t * E r t * E (r - 1) t)
      (Set.uIoc x y) volume :=
    intervalIntegrable_iff.mp (hG.intervalIntegrable x y)
  have hmono : Monotone fun t => (mStar (E r t) : ℝ) := fun s t hst =>
    Nat.cast_le.mpr (mStar_mono (E_mono r hst))
  have hmeas : Measurable
      fun t => a r t * E r t * E (r - 1) t / (mStar (E r t) : ℝ) :=
    hG.measurable.div hmono.measurable
  refine Integrable.mono' hGint hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => ?_)
  have ha := a_pos r t
  have hEr : 0 < E r t := E_pos_of_one_le (by omega) t
  have hEr1 : 0 < E (r - 1) t := E_pos_of_one_le (by omega) t
  have hm : (1 : ℝ) ≤ (mStar (E r t) : ℝ) := by
    exact_mod_cast mStar_pos hEr.le
  have hnum : 0 ≤ a r t * E r t * E (r - 1) t :=
    mul_nonneg (mul_nonneg ha.le hEr.le) hEr1.le
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hnum (by linarith))]
  exact div_le_self hnum hm

/-- **Integral form of the exact differentiated recurrence**
(`lem:exact-recurrence`, eq. `exact-recurrence` integrated): for `r ≥ 3` and
`x ≤ y`,
`H̄_{r+1}(y) − H̄_{r+1}(x) = ∫_x^y a_r(t) (H̄_r(t) + ρ_r(t)) dt`.
Fundamental theorem of calculus for the continuous function `H̄_{r+1}` with
its everywhere-defined right derivative (`hasDerivWithinAt_Hbar_succ_Ioi`) —
no exceptional set is needed at all, sharpening the paper's "for almost every
`u`".  No positivity of `x` is needed either (see the module docstring). -/
theorem Hbar_succ_sub_eq_integral {r : ℕ} (hr : 3 ≤ r) {x y : ℝ}
    (hxy : x ≤ y) :
    Hbar (r + 1) y - Hbar (r + 1) x
      = ∫ t in x..y, a r t * (Hbar r t + rhoDepth r t) :=
  (intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hxy
    (continuous_Hbar (r + 1)).continuousOn
    (fun t _ => hasDerivWithinAt_Hbar_succ_Ioi hr t)
    (intervalIntegrable_recurrenceIntegrand hr x y)).symm

end Erdos320
