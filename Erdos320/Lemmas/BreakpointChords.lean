-- Import only the Mathlib modules actually used, not all of `Mathlib` (see
-- `Erdos320/Defs/Basic.lean` for the rationale).
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Quantitative chord bounds at a breakpoint (paper `lem:breakpoint-chords`)

This file formalizes the manuscript's Lemma "Quantitative chord bounds at a
breakpoint" (`lem:breakpoint-chords`, eqs. `chord-C-bounds` and `Apm`,
`sec:breakpoint-chords`): at a breakpoint `x = g(N)` of the concave count
function `𝓑`, the one-sided chord slopes of `𝓑` (pinned to `1/N` by
`lem:B-slopes` and to `1/(N+1)` by its `eq:B-prime` right-derivative identity
via `m_*(g(N)) = N+1`) squeeze any constant `C` for which
`‖𝓑 − C·q‖ ≤ ε` on the window `[x(1−t), x(1+t)]`, provided the reference
function `q` (the paper's `q_br`) is increasing with relative curvature
`−ξ q''(ξ)/q'(ξ)` bounded by `κ` on that window. The resulting two-sided bound is eq. `chord-C-bounds`:
```
(Ĉ − η)/A₋ ≤ C ≤ (Ĉ + η)/A₊,   Ĉ = x/(N σ₀),  η = 2ε/(t σ₀),  σ₀ = x q'(x),
```
with the chord factors `A₊`, `A₋` of eq. `Apm` (`chordAplus`, `chordAminus`
below).

## Design choices

* The lemma is stated **generically**: `Bf` plays `𝓑` and `qf` plays `q`, and
  the two concavity/slope facts about `𝓑` at the breakpoint —
  `𝓑(x(1+t)) − 𝓑(x) ≤ tx/N` and `tx/N ≤ 𝓑(x) − 𝓑(x(1−t))` — enter as
  *hypotheses* (`hchord_up`, `hchord_down`), to be discharged elsewhere from
  the paper's `lem:B-slopes`. This file therefore depends on no project
  infrastructure.
* The hypothesis set matches the paper's `lem:breakpoint-chords`
  hypothesis-for-hypothesis: real `κ ≠ 1` (`hκ1`; both finite applications
  use `κ = 1.061` and `κ = 1.021`), real `ε` (no sign condition; a
  nonnegativity is implied by `happrox` at any window point anyway),
  `q' > 0` and the *upper* curvature bound `−ξ q''(ξ)/q'(ξ) ≤ κ` only, and
  `q` merely twice differentiable (continuity of `q'` follows from `hq''`;
  continuity of `q''` is never used).  In particular no `0 ≤ κ`, no
  `ε ≥ 0`, no lower curvature bound `q'' ≤ 0`, and no twice-*continuous*
  differentiability are assumed — none is needed for this step.
-/

namespace Erdos320

/-- Paper eq. `Apm`: the upper chord factor
`A₊ = ((1+t)^{1-κ} − 1) / ((1−κ)·t)` (real exponentiation `Real.rpow`). -/
noncomputable def chordAplus (t κ : ℝ) : ℝ :=
  ((1 + t) ^ (1 - κ) - 1) / ((1 - κ) * t)

/-- Paper eq. `Apm`: the lower chord factor
`A₋ = (1 − (1−t)^{1-κ}) / ((1−κ)·t)` (real exponentiation `Real.rpow`). -/
noncomputable def chordAminus (t κ : ℝ) : ℝ :=
  (1 - (1 - t) ^ (1 - κ)) / ((1 - κ) * t)

/-- The upper chord factor `A₊` is positive for `0 < t` and `κ ≠ 1`
(numerator and denominator of eq. `Apm` change sign together at `κ = 1`). -/
theorem chordAplus_pos {t κ : ℝ} (ht0 : 0 < t) (hκ1 : κ ≠ 1) :
    0 < chordAplus t κ := by
  rcases lt_or_gt_of_ne hκ1 with hκ | hκ
  · have h1 : (1 : ℝ) < (1 + t) ^ (1 - κ) :=
      (Real.one_lt_rpow_iff_of_pos (by linarith)).mpr
        (Or.inl ⟨by linarith, by linarith⟩)
    exact div_pos (by linarith) (mul_pos (by linarith) ht0)
  · have h1 : (1 + t) ^ (1 - κ) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith)
    exact div_pos_iff.mpr
      (Or.inr ⟨by linarith, mul_neg_of_neg_of_pos (by linarith) ht0⟩)

/-- The lower chord factor `A₋` is positive for `0 < t < 1` and `κ ≠ 1`. -/
theorem chordAminus_pos {t κ : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hκ1 : κ ≠ 1) :
    0 < chordAminus t κ := by
  rcases lt_or_gt_of_ne hκ1 with hκ | hκ
  · have h1 : (1 - t) ^ (1 - κ) < 1 :=
      Real.rpow_lt_one (by linarith) (by linarith) (by linarith)
    exact div_pos (by linarith) (mul_pos (by linarith) ht0)
  · have h1 : (1 : ℝ) < (1 - t) ^ (1 - κ) :=
      (Real.one_lt_rpow_iff_of_pos (by linarith)).mpr
        (Or.inr ⟨by linarith, by linarith⟩)
    exact div_pos_iff.mpr
      (Or.inr ⟨by linarith, mul_neg_of_neg_of_pos (by linarith) ht0⟩)

/-- Key comparison behind `lem:breakpoint-chords`: on an interval
`[a, b] ⊂ (0, ∞)` where the relative curvature `−ξ q''(ξ)/q'(ξ)` is at most
`κ` (equivalently `−ξ q''(ξ) ≤ κ q'(ξ)`), the weighted slope
`ξ ↦ q'(ξ)·ξ^κ` is monotone nondecreasing. -/
theorem monotoneOn_deriv_mul_rpow_of_curvature_le {q' q'' : ℝ → ℝ} {a b κ : ℝ}
    (ha : 0 < a)
    (hq'' : ∀ ξ ∈ Set.Icc a b, HasDerivAt q' (q'' ξ) ξ)
    (hcurvκ : ∀ ξ ∈ Set.Icc a b, -(ξ * q'' ξ) ≤ κ * q' ξ) :
    MonotoneOn (fun ξ => q' ξ * ξ ^ κ) (Set.Icc a b) := by
  have hpos : ∀ ξ ∈ Set.Icc a b, 0 < ξ := fun ξ hξ => lt_of_lt_of_le ha hξ.1
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b)
    (f' := fun ξ => q'' ξ * ξ ^ κ + q' ξ * (κ * ξ ^ (κ - 1)))
  · -- continuity of the weighted slope on the interval
    intro ξ hξ
    exact ((hq'' ξ hξ).continuousAt.mul
      (Real.continuousAt_rpow_const ξ κ (Or.inl (hpos ξ hξ).ne'))).continuousWithinAt
  · -- differentiability on the interior, with the displayed derivative
    intro ξ hξ
    have hξm : ξ ∈ Set.Icc a b := interior_subset hξ
    exact ((hq'' ξ hξm).mul
      (Real.hasDerivAt_rpow_const (Or.inl (hpos ξ hξm).ne'))).hasDerivWithinAt
  · -- nonnegativity of that derivative, from the curvature bound
    intro ξ hξ
    have hξm : ξ ∈ Set.Icc a b := interior_subset hξ
    have hξ0 : 0 < ξ := hpos ξ hξm
    have hcur : 0 ≤ ξ * q'' ξ + κ * q' ξ := by
      have := hcurvκ ξ hξm; linarith
    have hsplit : ξ ^ κ = ξ ^ (κ - 1) * ξ := by
      have hexp : κ - 1 + 1 = κ := by ring
      rw [← hexp, Real.rpow_add_one hξ0.ne', hexp]
    calc (0 : ℝ) ≤ ξ ^ (κ - 1) * (ξ * q'' ξ + κ * q' ξ) :=
          mul_nonneg (Real.rpow_nonneg hξ0.le _) hcur
      _ = q'' ξ * ξ ^ κ + q' ξ * (κ * ξ ^ (κ - 1)) := by rw [hsplit]; ring

/-- Paper `lem:breakpoint-chords` ("Quantitative chord bounds at a
breakpoint"), eq. `chord-C-bounds`. `Bf` plays the concave count function `𝓑`,
`qf` plays the depth-4 reference function `q` of eq.
`q-breakpoint-coordinate`, `x = g(N)` is the breakpoint, and the hypotheses
`hchord_up`/`hchord_down` are the concavity + one-sided-slope facts
`𝓑(x(1+t)) − 𝓑(x) ≤ tx/(N+1) ≤ tx/N` and `tx/N ≤ 𝓑(x) − 𝓑(x(1−t))`, proved
elsewhere from the paper's `lem:B-slopes`. The conclusion is
`(Ĉ − η)/A₋ ≤ C ≤ (Ĉ + η)/A₊` with `Ĉ = x/(N·σ₀)`, `η = 2ε/(t·σ₀)`,
`σ₀ = x·q'(x)`, and the chord factors `A₊ = chordAplus t κ`,
`A₋ = chordAminus t κ` of eq. `Apm`.

Stated for real `κ ≠ 1` (the paper's two applications use `κ = 1.061` and
`κ = 1.021`), real `ε`, `q' > 0`, and the upper curvature bound only, with
`q` twice differentiable — exactly the hypothesis set of the paper's
`lem:breakpoint-chords` (see the module docstring). -/
theorem breakpoint_chord_bounds
    (Bf qf q' q'' : ℝ → ℝ) (x t C ε κ : ℝ) (N : ℕ)
    (hx : 0 < x) (ht0 : 0 < t) (ht1 : t < 1) (hN : 1 ≤ N)
    (hC : 0 ≤ C) (hκ1 : κ ≠ 1)
    -- `q` is twice differentiable with the stated derivative data on the window:
    (hq' : ∀ ξ ∈ Set.Icc (x * (1 - t)) (x * (1 + t)), HasDerivAt qf (q' ξ) ξ)
    (hq'' : ∀ ξ ∈ Set.Icc (x * (1 - t)) (x * (1 + t)), HasDerivAt q' (q'' ξ) ξ)
    (hq'pos : ∀ ξ ∈ Set.Icc (x * (1 - t)) (x * (1 + t)), 0 < q' ξ)
    -- curvature bound `−ξ q''(ξ)/q'(ξ) ≤ κ` on the window:
    (hcurvκ : ∀ ξ ∈ Set.Icc (x * (1 - t)) (x * (1 + t)), -(ξ * q'' ξ) ≤ κ * q' ξ)
    -- uniform approximation `‖𝓑 − C·q‖ ≤ ε` on the window:
    (happrox : ∀ ξ ∈ Set.Icc (x * (1 - t)) (x * (1 + t)), |Bf ξ - C * qf ξ| ≤ ε)
    -- concavity chord facts about `𝓑` at the breakpoint (from `lem:B-slopes`):
    (hchord_up : Bf (x * (1 + t)) - Bf x ≤ t * x / N)
    (hchord_down : t * x / N ≤ Bf x - Bf (x * (1 - t))) :
    (x / (N * (x * q' x)) - 2 * ε / (t * (x * q' x))) / chordAminus t κ ≤ C ∧
      C ≤ (x / (N * (x * q' x)) + 2 * ε / (t * (x * q' x))) / chordAplus t κ := by
  set lo := x * (1 - t) with hlo_def
  set hi := x * (1 + t) with hhi_def
  -- basic window geometry
  have hlo_pos : 0 < lo := mul_pos hx (by linarith)
  have hlo_le_x : lo ≤ x := by nlinarith [mul_pos hx ht0]
  have hx_le_hi : x ≤ hi := by nlinarith [mul_pos hx ht0]
  have hx_mem : x ∈ Set.Icc lo hi := ⟨hlo_le_x, hx_le_hi⟩
  have hq'x : 0 < q' x := hq'pos x hx_mem
  have hσ0 : 0 < x * q' x := mul_pos hx hq'x
  have htσ0 : 0 < t * (x * q' x) := mul_pos ht0 hσ0
  have hNpos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
  have h1κ : (1 : ℝ) - κ ≠ 0 := sub_ne_zero.mpr (Ne.symm hκ1)
  -- `q'` is continuous on the window (it is differentiable there)
  have hq'cont : ContinuousOn q' (Set.Icc lo hi) := fun ξ hξ =>
    ((hq'' ξ hξ).continuousAt).continuousWithinAt
  -- the weighted slope `ξ ↦ q'(ξ)·ξ^κ` is monotone on the window
  have hg_mono : MonotoneOn (fun ξ => q' ξ * ξ ^ κ) (Set.Icc lo hi) :=
    monotoneOn_deriv_mul_rpow_of_curvature_le hlo_pos hq'' hcurvκ
  -- `x^κ · x^(1−κ) = x`
  have hxpow : x ^ κ * x ^ (1 - κ) = x := by
    have hexp : κ + (1 - κ) = 1 := by ring
    rw [← Real.rpow_add hx, hexp, Real.rpow_one]
  -- the model integral `∫ ξ^(−κ)` over positive subintervals
  have hrpow_int : ∀ c d : ℝ, 0 < c → c ≤ d →
      (∫ ξ in c..d, ξ ^ (-κ)) = (d ^ (1 - κ) - c ^ (1 - κ)) / (1 - κ) := by
    intro c d hc hcd
    have hmem : (0 : ℝ) ∉ Set.uIcc c d := by
      rw [Set.uIcc_of_le hcd]
      exact fun h0 => absurd h0.1 (not_le.mpr hc)
    rw [integral_rpow (Or.inr ⟨fun hcontra => hκ1 (neg_inj.mp hcontra), hmem⟩)]
    have hexp : -κ + 1 = 1 - κ := by ring
    rw [hexp]
  -- STEP `A₊`: the reference increment `q(x(1+t)) − q(x)` is at least `σ₀·t·A₊`
  have hup : x * q' x * (t * chordAplus t κ) ≤ qf hi - qf x := by
    have hsub : Set.uIcc x hi ⊆ Set.Icc lo hi := by
      rw [Set.uIcc_of_le hx_le_hi]
      exact Set.Icc_subset_Icc hlo_le_x le_rfl
    have hq'int : IntervalIntegrable q' MeasureTheory.volume x hi :=
      (hq'cont.mono hsub).intervalIntegrable
    have hftc : (∫ ξ in x..hi, q' ξ) = qf hi - qf x :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun ξ hξ => hq' ξ (hsub hξ)) hq'int
    have hcmp_int :
        IntervalIntegrable (fun ξ => q' x * x ^ κ * ξ ^ (-κ))
          MeasureTheory.volume x hi := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hx_le_hi]
      exact continuousOn_const.mul fun ξ hξ =>
        (Real.continuousAt_rpow_const ξ (-κ)
          (Or.inl (lt_of_lt_of_le hx hξ.1).ne')).continuousWithinAt
    have hptwise : ∀ ξ ∈ Set.Icc x hi, q' x * x ^ κ * ξ ^ (-κ) ≤ q' ξ := by
      intro ξ hξ
      have hξ0 : 0 < ξ := lt_of_lt_of_le hx hξ.1
      have hξw : ξ ∈ Set.Icc lo hi := ⟨hlo_le_x.trans hξ.1, hξ.2⟩
      have hg : q' x * x ^ κ ≤ q' ξ * ξ ^ κ := hg_mono hx_mem hξw hξ.1
      calc q' x * x ^ κ * ξ ^ (-κ) ≤ q' ξ * ξ ^ κ * ξ ^ (-κ) :=
            mul_le_mul_of_nonneg_right hg (Real.rpow_nonneg hξ0.le _)
        _ = q' ξ := by
            rw [mul_assoc, ← Real.rpow_add hξ0, add_neg_cancel, Real.rpow_zero,
              mul_one]
    -- the chord-factor identity `σ₀·t·A₊ = q'(x)·x^κ·(hi^(1−κ) − x^(1−κ))/(1−κ)`
    have hhi_rpow : hi ^ (1 - κ) = x ^ (1 - κ) * (1 + t) ^ (1 - κ) := by
      rw [hhi_def]
      exact Real.mul_rpow hx.le (by linarith)
    have hAeq : q' x * x ^ κ * ((hi ^ (1 - κ) - x ^ (1 - κ)) / (1 - κ))
        = x * q' x * (t * chordAplus t κ) := by
      have lhs_eq : q' x * x ^ κ *
            ((x ^ (1 - κ) * (1 + t) ^ (1 - κ) - x ^ (1 - κ)) / (1 - κ))
          = q' x * (x ^ κ * x ^ (1 - κ)) *
            (((1 + t) ^ (1 - κ) - 1) / (1 - κ)) := by ring
      have rhs_eq : x * q' x * (t * chordAplus t κ)
          = q' x * x * (((1 + t) ^ (1 - κ) - 1) / (1 - κ)) := by
        rw [chordAplus]
        field_simp
      rw [hhi_rpow, lhs_eq, hxpow, rhs_eq]
    calc x * q' x * (t * chordAplus t κ)
        = q' x * x ^ κ * ((hi ^ (1 - κ) - x ^ (1 - κ)) / (1 - κ)) := hAeq.symm
      _ = ∫ ξ in x..hi, q' x * x ^ κ * ξ ^ (-κ) := by
          rw [intervalIntegral.integral_const_mul, hrpow_int x hi hx hx_le_hi]
      _ ≤ ∫ ξ in x..hi, q' ξ :=
          intervalIntegral.integral_mono_on hx_le_hi hcmp_int hq'int hptwise
      _ = qf hi - qf x := hftc
  -- STEP `A₋`: the reference increment `q(x) − q(x(1−t))` is at most `σ₀·t·A₋`
  have hdown : qf x - qf lo ≤ x * q' x * (t * chordAminus t κ) := by
    have hsub : Set.uIcc lo x ⊆ Set.Icc lo hi := by
      rw [Set.uIcc_of_le hlo_le_x]
      exact Set.Icc_subset_Icc le_rfl hx_le_hi
    have hq'int : IntervalIntegrable q' MeasureTheory.volume lo x :=
      (hq'cont.mono hsub).intervalIntegrable
    have hftc : (∫ ξ in lo..x, q' ξ) = qf x - qf lo :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun ξ hξ => hq' ξ (hsub hξ)) hq'int
    have hcmp_int :
        IntervalIntegrable (fun ξ => q' x * x ^ κ * ξ ^ (-κ))
          MeasureTheory.volume lo x := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hlo_le_x]
      exact continuousOn_const.mul fun ξ hξ =>
        (Real.continuousAt_rpow_const ξ (-κ)
          (Or.inl (lt_of_lt_of_le hlo_pos hξ.1).ne')).continuousWithinAt
    have hptwise : ∀ ξ ∈ Set.Icc lo x, q' ξ ≤ q' x * x ^ κ * ξ ^ (-κ) := by
      intro ξ hξ
      have hξ0 : 0 < ξ := lt_of_lt_of_le hlo_pos hξ.1
      have hξw : ξ ∈ Set.Icc lo hi := ⟨hξ.1, hξ.2.trans hx_le_hi⟩
      have hg : q' ξ * ξ ^ κ ≤ q' x * x ^ κ := hg_mono hξw hx_mem hξ.2
      calc q' ξ = q' ξ * ξ ^ κ * ξ ^ (-κ) := by
            rw [mul_assoc, ← Real.rpow_add hξ0, add_neg_cancel, Real.rpow_zero,
              mul_one]
        _ ≤ q' x * x ^ κ * ξ ^ (-κ) :=
            mul_le_mul_of_nonneg_right hg (Real.rpow_nonneg hξ0.le _)
    -- the chord-factor identity `σ₀·t·A₋ = q'(x)·x^κ·(x^(1−κ) − lo^(1−κ))/(1−κ)`
    have hlo_rpow : lo ^ (1 - κ) = x ^ (1 - κ) * (1 - t) ^ (1 - κ) := by
      rw [hlo_def]
      exact Real.mul_rpow hx.le (by linarith)
    have hAeq : q' x * x ^ κ * ((x ^ (1 - κ) - lo ^ (1 - κ)) / (1 - κ))
        = x * q' x * (t * chordAminus t κ) := by
      have lhs_eq : q' x * x ^ κ *
            ((x ^ (1 - κ) - x ^ (1 - κ) * (1 - t) ^ (1 - κ)) / (1 - κ))
          = q' x * (x ^ κ * x ^ (1 - κ)) *
            ((1 - (1 - t) ^ (1 - κ)) / (1 - κ)) := by ring
      have rhs_eq : x * q' x * (t * chordAminus t κ)
          = q' x * x * ((1 - (1 - t) ^ (1 - κ)) / (1 - κ)) := by
        rw [chordAminus]
        field_simp
      rw [hlo_rpow, lhs_eq, hxpow, rhs_eq]
    calc qf x - qf lo = ∫ ξ in lo..x, q' ξ := hftc.symm
      _ ≤ ∫ ξ in lo..x, q' x * x ^ κ * ξ ^ (-κ) :=
          intervalIntegral.integral_mono_on hlo_le_x hq'int hcmp_int hptwise
      _ = q' x * x ^ κ * ((x ^ (1 - κ) - lo ^ (1 - κ)) / (1 - κ)) := by
          rw [intervalIntegral.integral_const_mul,
            hrpow_int lo x hlo_pos hlo_le_x]
      _ = x * q' x * (t * chordAminus t κ) := hAeq
  -- insert the two uniform errors of size `ε` and the chord facts about `𝓑`
  have happ_hi := abs_le.mp (happrox hi ⟨hlo_le_x.trans hx_le_hi, le_rfl⟩)
  have happ_lo := abs_le.mp (happrox lo ⟨le_rfl, hlo_le_x.trans hx_le_hi⟩)
  have happ_x := abs_le.mp (happrox x hx_mem)
  have hkey_up : C * (x * q' x * (t * chordAplus t κ)) ≤ t * x / N + 2 * ε := by
    have h1 : C * qf hi - C * qf x ≤ Bf hi - Bf x + 2 * ε := by
      linarith [happ_hi.1, happ_x.2]
    have h2 : C * (x * q' x * (t * chordAplus t κ)) ≤ C * (qf hi - qf x) :=
      mul_le_mul_of_nonneg_left hup hC
    have h3 : C * (qf hi - qf x) = C * qf hi - C * qf x := by ring
    linarith [hchord_up]
  have hkey_down : t * x / N - 2 * ε
      ≤ C * (x * q' x * (t * chordAminus t κ)) := by
    have h1 : Bf x - Bf lo - 2 * ε ≤ C * qf x - C * qf lo := by
      linarith [happ_x.1, happ_lo.2]
    have h2 : C * (qf x - qf lo) ≤ C * (x * q' x * (t * chordAminus t κ)) :=
      mul_le_mul_of_nonneg_left hdown hC
    have h3 : C * (qf x - qf lo) = C * qf x - C * qf lo := by ring
    linarith [hchord_down]
  -- rearrange into eq. `chord-C-bounds`
  constructor
  · rw [div_le_iff₀ (chordAminus_pos ht0 ht1 hκ1)]
    have hexpand : x / (N * (x * q' x)) - 2 * ε / (t * (x * q' x))
        = (t * x / N - 2 * ε) / (t * (x * q' x)) := by
      field_simp
    rw [hexpand, div_le_iff₀ htσ0]
    calc t * x / N - 2 * ε ≤ C * (x * q' x * (t * chordAminus t κ)) := hkey_down
      _ = C * chordAminus t κ * (t * (x * q' x)) := by ring
  · rw [le_div_iff₀ (chordAplus_pos ht0 hκ1)]
    have hexpand : x / (N * (x * q' x)) + 2 * ε / (t * (x * q' x))
        = (t * x / N + 2 * ε) / (t * (x * q' x)) := by
      field_simp
    rw [hexpand, le_div_iff₀ htσ0]
    calc C * chordAplus t κ * (t * (x * q' x))
        = C * (x * q' x * (t * chordAplus t κ)) := by ring
      _ ≤ t * x / N + 2 * ε := hkey_up

end Erdos320
