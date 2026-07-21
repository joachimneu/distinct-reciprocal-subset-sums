import Erdos320.Lemmas.CertificateTransfer
import Erdos320.Lemmas.CertLowQ4Positive
import Erdos320.Lemmas.CertLowSlopeMargin
import Erdos320.Lemmas.CertLowCurvature
import Erdos320.Lemmas.CertLowSlopeMatch
import Erdos320.Lemmas.CertHighSlopeMatched
import Erdos320.Lemmas.CertHighData

/-!
# Certificate consumers: core→limit transfer on the low/high windows

These lemmas transfer the six proved directed-interval certificate theorems —
`lowQ4PositiveCert`, `lowSlopeMarginCert`, `lowCurvatureCert`,
`lowSlopeMatchCert` in `CertLowQ4Positive`/`CertLowSlopeMargin`/
`CertLowCurvature`/`CertLowSlopeMatch`, and `highSlopeMatchedCert`,
`highDataCert` in `CertHighSlopeMatched`/`CertHighData` (the slope-matched
certs via a monotonicity-of-the-slope-matched-candidate argument that
collapses the wide a-priori range to one endpoint) — from the core reference
functions to the limit reference functions consumed downstream
(`sec:certificates`).  They live in this separate file, rather than in
`CertificateTransfer.lean` itself, because the certificate proofs sit
downstream of the `CertificateTransfer` toolkit, so any lemma applying them
must sit downstream of the proofs (avoiding an import cycle).
-/

namespace Erdos320

/-! ## Core→limit transfer: the low certificate window -/

/-- **`eq:low-slope-match` transferred to the limit** (constant slackened
`1.1163 → 1.11635`): for `f ∈ [2.787, 2.792]`,
`f·y(f) < 1.11635·(log N₀·Q₃*(u(f)))`. -/
theorem cert_low_slope_match_limit {f : ℝ} (h1 : (2.787 : ℝ) ≤ f)
    (h2 : f ≤ 2.792) :
    f * Real.log (lowBreakpointX f)
      < 1.11635 * (Real.log 65659969
          * QrefLimit3 (iteratedLog 3 (lowBreakpointX f))) := by
  obtain ⟨hL1, hL2⟩ := cert_log_N0_bounds
  obtain ⟨hw1, hw2⟩ := cert_low_window_inner h1 h2
  have hx0 : (0 : ℝ) ≤ lowBreakpointX f := by nlinarith
  have hx97 : (9.7e6 : ℝ) ≤ lowBreakpointX f := by nlinarith
  have hx39 : (3.9e6 : ℝ) < lowBreakpointX f := by linarith
  have hy16 := cert_log_ge_sixteen hx97
  have hu1 : 1 < iteratedLog 3 (lowBreakpointX f) :=
    cert_one_lt_iteratedLog_three hx39
  have hcert := lowSlopeMatchCert f (by linarith) (by linarith)
  have hmargin := lowSlopeMarginCert f (by linarith) (by linarith)
  have hQc : (2.222 : ℝ) ≤ QrefCore3 (iteratedLog 3 (lowBreakpointX f)) := by
    nlinarith
  have htail := abs_QrefLimit3_sub_QrefCore3_le hu1.le
  have htiny : Real.exp (-(3.7e6 : ℝ)) ≤ 1e-40 :=
    cert_exp_neg_le_tiny (by norm_num)
  have hQl : QrefCore3 (iteratedLog 3 (lowBreakpointX f)) - 1e-40
      ≤ QrefLimit3 (iteratedLog 3 (lowBreakpointX f)) := by
    have := abs_le.mp htail
    linarith
  have hLpos : (0 : ℝ) ≤ Real.log 65659969 := by linarith
  have hprod : Real.log 65659969
        * (QrefCore3 (iteratedLog 3 (lowBreakpointX f)) - 1e-40)
      ≤ Real.log 65659969
        * QrefLimit3 (iteratedLog 3 (lowBreakpointX f)) :=
    mul_le_mul_of_nonneg_left hQl hLpos
  have hA : (17.9999 : ℝ) * 2.222
      ≤ Real.log 65659969 * QrefCore3 (iteratedLog 3 (lowBreakpointX f)) := by
    nlinarith
  nlinarith

/-- **`eq:low-slope-margin` transferred to the limit** (constant slackened
`0.1389 → 0.13889`): `0.13889·y(f) < Q₃*(u(f))` for `f ∈ [2.787, 2.792]`. -/
theorem cert_low_slope_margin_limit {f : ℝ} (h1 : (2.787 : ℝ) ≤ f)
    (h2 : f ≤ 2.792) :
    0.13889 * Real.log (lowBreakpointX f)
      < QrefLimit3 (iteratedLog 3 (lowBreakpointX f)) := by
  obtain ⟨hw1, hw2⟩ := cert_low_window_inner h1 h2
  have hx0 : (0 : ℝ) ≤ lowBreakpointX f := by nlinarith
  have hx97 : (9.7e6 : ℝ) ≤ lowBreakpointX f := by nlinarith
  have hx39 : (3.9e6 : ℝ) < lowBreakpointX f := by linarith
  have hy16 := cert_log_ge_sixteen hx97
  have hu1 : 1 < iteratedLog 3 (lowBreakpointX f) :=
    cert_one_lt_iteratedLog_three hx39
  have hmargin := lowSlopeMarginCert f (by linarith) (by linarith)
  have htail := abs_QrefLimit3_sub_QrefCore3_le hu1.le
  have htiny : Real.exp (-(3.7e6 : ℝ)) ≤ 1e-40 :=
    cert_exp_neg_le_tiny (by norm_num)
  have := abs_le.mp htail
  nlinarith

/-- **`eq:low-Q4-positive` transferred to the limit** (constant slackened
`4.79 → 4.789`): `Q₄*(log₃ w) > 4.789` on `[9 725 449, 10 632 947]`. -/
theorem cert_low_Q4_positive_limit {w : ℝ} (h1 : (9725449 : ℝ) ≤ w)
    (h2 : w ≤ 10632947) :
    (4.789 : ℝ) < QrefLimit 4 (iteratedLog 3 w) := by
  have hw39 : (3.9e6 : ℝ) < w := by linarith
  have hu1 : 1 < iteratedLog 3 w := cert_one_lt_iteratedLog_three hw39
  have hcert := lowQ4PositiveCert w h1 h2
  have htail := abs_QrefLimit_four_sub_QrefCore4_le hu1.le
  have htiny : Real.exp (-(3.7e6 : ℝ)) ≤ 1e-40 :=
    cert_exp_neg_le_tiny (by norm_num)
  have := abs_le.mp htail
  linarith

/-- **Quantitative window-wide slope lower bound for the core**: on every
low chord window, `q̃'(ξ) > 1.2·10⁻⁸`.  Left of the breakpoint this is
`q̃'' ≤ 0` (antitone slope); right of it, `−ξq̃''/q̃' < 1.0601 < 2` makes
`ξ ↦ q̃'(ξ)·ξ²` nondecreasing, costing a factor `(1.04)⁻² > 0.92` against
the breakpoint value `q̃'(x) > 0.1389/x` from `eq:low-slope-margin` +
`eq:q-slope`. -/
theorem cert_low_qCore_deriv_window_lb {f : ℝ} (h1 : (2.787 : ℝ) ≤ f)
    (h2 : f ≤ 2.792) {ξ : ℝ} (hξ1 : 0.96 * lowBreakpointX f ≤ ξ)
    (hξ2 : ξ ≤ 1.04 * lowBreakpointX f) :
    (1.2e-8 : ℝ) < deriv qCore ξ := by
  obtain ⟨hw1, hw2⟩ := cert_low_window_inner h1 h2
  have hx0 : (0 : ℝ) < lowBreakpointX f := by nlinarith
  have hx_lb : (9725449 : ℝ) ≤ lowBreakpointX f := by nlinarith
  have hx_ub : lowBreakpointX f ≤ 10224038 := by nlinarith
  have hx39 : (3.9e6 : ℝ) < lowBreakpointX f := by linarith
  have hξ_lb : (9333333 : ℝ) ≤ ξ := by nlinarith
  have hξ39 : (3.9e6 : ℝ) < ξ := by linarith
  have hξ0 : (0 : ℝ) < ξ := by linarith
  -- the breakpoint slope: `q̃'(x) > 0.1389/x`
  have hy16 := cert_log_ge_sixteen (show (9.7e6 : ℝ) ≤ lowBreakpointX f by
    linarith)
  have hy0 : (0 : ℝ) < Real.log (lowBreakpointX f) := by linarith
  have hmargin := lowSlopeMarginCert f (by linarith) (by linarith)
  have hslope := cert_qCore_slope hx39
  have hqx : 0.1389 / lowBreakpointX f < deriv qCore (lowBreakpointX f) := by
    have hgt : (0.1389 : ℝ) < lowBreakpointX f * deriv qCore (lowBreakpointX f) := by
      rw [hslope, lt_div_iff₀ hy0]
      linarith
    rw [div_lt_iff₀ hx0]
    linarith [mul_comm (lowBreakpointX f) (deriv qCore (lowBreakpointX f))]
  have hqx_num : (1.35e-8 : ℝ) < deriv qCore (lowBreakpointX f) := by
    have : (1.35e-8 : ℝ) ≤ 0.1389 / lowBreakpointX f := by
      rw [le_div_iff₀ hx0]
      nlinarith
    linarith
  rcases le_or_gt ξ (lowBreakpointX f) with hle | hlt
  · -- left of the breakpoint: `q̃'` is antitone there (`q̃'' ≤ 0`)
    rcases eq_or_lt_of_le hle with heq | hlt'
    · rw [heq]; linarith
    · have hcont : ContinuousOn (deriv qCore)
          (Set.Icc ξ (lowBreakpointX f)) := fun v hv =>
        ((cert_hasDerivAt_deriv_qCore_self
          (show (3.9e6 : ℝ) < v by linarith [hv.1])).continuousAt).continuousWithinAt
      obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope (deriv qCore)
        (fun v => deriv (deriv qCore) v) hlt' hcont
        (fun v hv => cert_hasDerivAt_deriv_qCore_self
          (show (3.9e6 : ℝ) < v by linarith [hv.1]))
      have hcw := lowCurvatureCert f (by linarith) (by linarith) c
        (by linarith [hc.1]) (by nlinarith [hc.2])
      have hslope_nonpos : (deriv qCore (lowBreakpointX f) - deriv qCore ξ)
          / (lowBreakpointX f - ξ) ≤ 0 := hceq ▸ hcw.2.1
      have hd : (0 : ℝ) < lowBreakpointX f - ξ := by linarith
      have hnum : deriv qCore (lowBreakpointX f) - deriv qCore ξ ≤ 0 := by
        have h := mul_le_mul_of_nonneg_right hslope_nonpos hd.le
        rw [div_mul_cancel₀ _ hd.ne'] at h
        linarith
      linarith
  · -- right of the breakpoint: `v ↦ q̃'(v)·v²` is nondecreasing
    have hHd : ∀ v, (3.9e6 : ℝ) < v →
        HasDerivAt (fun t => deriv qCore t * t ^ 2)
          (deriv (deriv qCore) v * v ^ 2 + deriv qCore v * (2 * v)) v := by
      intro v hv
      refine ((cert_hasDerivAt_deriv_qCore_self hv).mul
        (hasDerivAt_pow 2 v)).congr_deriv ?_
      push_cast
      ring
    have hcont : ContinuousOn (fun t => deriv qCore t * t ^ 2)
        (Set.Icc (lowBreakpointX f) ξ) := fun v hv =>
      ((hHd v (by linarith [hv.1])).continuousAt).continuousWithinAt
    obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope
      (fun t => deriv qCore t * t ^ 2)
      (fun v => deriv (deriv qCore) v * v ^ 2 + deriv qCore v * (2 * v))
      hlt hcont
      (fun v hv => hHd v (by linarith [hv.1]))
    have hc0 : (0 : ℝ) < c := by nlinarith [hc.1]
    have hcw := lowCurvatureCert f (by linarith) (by linarith) c
      (by nlinarith [hc.1]) (by linarith [hc.2])
    have hderiv_nonneg : 0 ≤ deriv (deriv qCore) c * c ^ 2
        + deriv qCore c * (2 * c) := by
      have hcurv := hcw.2.2
      have hq'c := hcw.1
      nlinarith
    have hd : (0 : ℝ) < ξ - lowBreakpointX f := by linarith
    have hmono : deriv qCore (lowBreakpointX f) * lowBreakpointX f ^ 2
        ≤ deriv qCore ξ * ξ ^ 2 := by
      have h := hceq ▸ hderiv_nonneg
      have h2 := mul_le_mul_of_nonneg_right h hd.le
      rw [zero_mul, div_mul_cancel₀ _ hd.ne'] at h2
      linarith
    -- `q̃'(ξ) ≥ q̃'(x)·x²/ξ² > 1.35·10⁻⁸/1.0816 > 1.2·10⁻⁸`
    have hξsq : ξ ^ 2 ≤ 1.0816 * lowBreakpointX f ^ 2 := by nlinarith
    by_contra hcon
    rw [not_lt] at hcon
    have hsq0 : (0 : ℝ) < ξ ^ 2 := by positivity
    nlinarith [sq_nonneg (lowBreakpointX f)]

/-- Window-wide slope lower bound for the *limit*: `q'(ξ) > 1.1·10⁻⁸` on
every low chord window. -/
theorem cert_low_qLimit_deriv_window_lb {f : ℝ} (h1 : (2.787 : ℝ) ≤ f)
    (h2 : f ≤ 2.792) {ξ : ℝ} (hξ1 : 0.96 * lowBreakpointX f ≤ ξ)
    (hξ2 : ξ ≤ 1.04 * lowBreakpointX f) :
    (1.1e-8 : ℝ) < deriv qLimit ξ := by
  obtain ⟨hw1, hw2⟩ := cert_low_window_inner h1 h2
  have hx0 : (0 : ℝ) < lowBreakpointX f := by nlinarith
  have hξ39 : (3.9e6 : ℝ) < ξ := by nlinarith
  have hcore := cert_low_qCore_deriv_window_lb h1 h2 hξ1 hξ2
  have htail := cert_abs_deriv_qLimit_sub_qCore_le hξ39
  have htiny : Real.exp (-(3.7e6 : ℝ)) ≤ 1e-40 :=
    cert_exp_neg_le_tiny (by norm_num)
  have := abs_le.mp htail
  linarith

/-- **`eq:low-curvature` transferred to the limit** (curvature constant
slackened `1.0601 → 1.061`; the exact `q̃'' ≤ 0` becomes
`q'' ≤ exp(−3.6·10⁶)`): on every low chord window,
`0 < q'`, `q'' ≤ exp(−3.6·10⁶)`, and `−ξ·q''(ξ) < 1.061·q'(ξ)`.

The chord computation at `κ = 1.061` matches `prop:nonconstant`'s
low-breakpoint computation: `A₊(0.04, 1.061) > 0.97934` and
`(1.1163 + η)/0.97934 < 1.16` gives the margin of `prop:nonconstant`. -/
theorem cert_low_curvature_limit {f : ℝ} (h1 : (2.787 : ℝ) ≤ f)
    (h2 : f ≤ 2.792) {ξ : ℝ} (hξ1 : 0.96 * lowBreakpointX f ≤ ξ)
    (hξ2 : ξ ≤ 1.04 * lowBreakpointX f) :
    0 < deriv qLimit ξ ∧
      deriv (deriv qLimit) ξ ≤ Real.exp (-(3.6e6 : ℝ)) ∧
      -(ξ * deriv (deriv qLimit) ξ) < 1.061 * deriv qLimit ξ := by
  obtain ⟨hw1, hw2⟩ := cert_low_window_inner h1 h2
  have hx0 : (0 : ℝ) < lowBreakpointX f := by nlinarith
  have hξ_lb : (9333333 : ℝ) ≤ ξ := by nlinarith
  have hξ_ub : ξ ≤ 10632947 := by nlinarith
  have hξ39 : (3.9e6 : ℝ) < ξ := by linarith
  have hξ0 : (0 : ℝ) < ξ := by linarith
  have hlim_lb := cert_low_qLimit_deriv_window_lb h1 h2 hξ1 hξ2
  have hcurv := lowCurvatureCert f (by linarith) (by linarith) ξ hξ1 hξ2
  have ht1 := abs_le.mp (cert_abs_deriv_qLimit_sub_qCore_le hξ39)
  have ht2 := abs_le.mp (cert_abs_deriv2_qLimit_sub_qCore_le hξ39)
  have htiny1 : Real.exp (-(3.7e6 : ℝ)) ≤ 1e-40 :=
    cert_exp_neg_le_tiny (by norm_num)
  have hxe : ξ * Real.exp (-(3.6e6 : ℝ)) ≤ 1e-40 :=
    cert_mul_exp_le_tiny (by linarith)
  refine ⟨by linarith, by linarith [hcurv.2.1], ?_⟩
  -- transfer of the curvature bound
  have hPQ : ξ * deriv (deriv qCore) ξ - ξ * deriv (deriv qLimit) ξ
      ≤ 1e-40 := by
    have h := mul_le_mul_of_nonneg_left
      (show deriv (deriv qCore) ξ - deriv (deriv qLimit) ξ
          ≤ Real.exp (-(3.6e6 : ℝ)) by linarith [ht2.1]) hξ0.le
    calc ξ * deriv (deriv qCore) ξ - ξ * deriv (deriv qLimit) ξ
        = ξ * (deriv (deriv qCore) ξ - deriv (deriv qLimit) ξ) := by ring
      _ ≤ ξ * Real.exp (-(3.6e6 : ℝ)) := h
      _ ≤ 1e-40 := hxe
  have hcore_curv := hcurv.2.2
  linarith [ht1.1]

/-! ## Core→limit transfer: the high certificate window -/

/-- **High slope-matched candidate transferred to the limit** (constant
slackened `1.1794 → 1.1793`): for `f ∈ [3.2411, 46]`,
`1.1793·(log N₁·Q₃*(u(f))) < f·y(f)`, i.e. `Ĉ > 1.1793` for the limit. -/
theorem cert_high_slope_matched_limit {f : ℝ} (h1 : (3.2411 : ℝ) ≤ f)
    (h2 : f ≤ 46) :
    1.1793 * (Real.log 16948892444103337141417836114
        * QrefLimit3 (iteratedLog 3 (highBreakpointX f)))
      < f * Real.log (highBreakpointX f) := by
  obtain ⟨hL1, hL2⟩ := cert_log_N1_bounds
  obtain ⟨hw1, hw2⟩ := cert_high_window_inner h1 h2
  have hx0 : (0 : ℝ) ≤ highBreakpointX f := by nlinarith
  have hx8 : (8e26 : ℝ) ≤ highBreakpointX f := by nlinarith
  have hx39 : (3.9e6 : ℝ) < highBreakpointX f := by linarith
  have hu1 : 1 < iteratedLog 3 (highBreakpointX f) :=
    cert_one_lt_iteratedLog_three hx39
  have hy619 : (61.9 : ℝ) ≤ Real.log (highBreakpointX f) := high_logX_lb hx8
  have hy0 : (0 : ℝ) < Real.log (highBreakpointX f) := by linarith
  have hcert := highSlopeMatchedCert f (by linarith) h2
  -- `Q̃₃ > 0.0399·y ≥ 2.469` from `eq:high-data` at the breakpoint itself
  have hdata := (highDataCert f (by linarith) h2 (highBreakpointX f)
    (by nlinarith) (by nlinarith)).1
  have hslope := cert_qCore_slope hx39
  have hQc : (2.4 : ℝ) ≤ QrefCore3 (iteratedLog 3 (highBreakpointX f)) := by
    rw [hslope, lt_div_iff₀ hy0] at hdata
    nlinarith
  have htail := abs_QrefLimit3_sub_QrefCore3_le hu1.le
  have htiny : Real.exp (-(3.7e6 : ℝ)) ≤ 1e-40 :=
    cert_exp_neg_le_tiny (by norm_num)
  have hQle : QrefLimit3 (iteratedLog 3 (highBreakpointX f))
      ≤ QrefCore3 (iteratedLog 3 (highBreakpointX f)) + 1e-40 := by
    have := abs_le.mp htail
    linarith
  have hL0 : (0 : ℝ) ≤ Real.log 16948892444103337141417836114 := by linarith
  have hprod : Real.log 16948892444103337141417836114
        * QrefLimit3 (iteratedLog 3 (highBreakpointX f))
      ≤ Real.log 16948892444103337141417836114
        * (QrefCore3 (iteratedLog 3 (highBreakpointX f)) + 1e-40) :=
    mul_le_mul_of_nonneg_left hQle hL0
  have hAlb : (155 : ℝ) ≤ Real.log 16948892444103337141417836114
      * QrefCore3 (iteratedLog 3 (highBreakpointX f)) := by
    nlinarith
  nlinarith

/-- **`eq:high-data` transferred to the limit** (slope constant slackened
`0.0399 → 0.0398`, curvature `1.0201 → 1.021`, exact `q̃'' ≤ 0` becomes
`q'' ≤ exp(−3.6·10⁶)`): on every high chord window,
`ξ·q'(ξ) > 0.0398`, `q'' ≤ exp(−3.6·10⁶)`, `−ξ·q''(ξ) < 1.021·q'(ξ)`.

The chord computation at `κ = 1.021` matches `prop:nonconstant`'s
high-breakpoint computation (`A₋ < 1.00052`, preserving the `C > 1.17`
conclusion). -/
theorem cert_high_data_limit {f : ℝ} (h1 : (3.2411 : ℝ) ≤ f) (h2 : f ≤ 46)
    {ξ : ℝ} (hξ1 : 0.999 * highBreakpointX f ≤ ξ)
    (hξ2 : ξ ≤ 1.001 * highBreakpointX f) :
    (0.0398 : ℝ) < ξ * deriv qLimit ξ ∧
      deriv (deriv qLimit) ξ ≤ Real.exp (-(3.6e6 : ℝ)) ∧
      -(ξ * deriv (deriv qLimit) ξ) < 1.021 * deriv qLimit ξ := by
  obtain ⟨hw1, hw2⟩ := cert_high_window h1 h2
  have hx0 : (0 : ℝ) ≤ highBreakpointX f := by nlinarith
  have hξ_lb : (8e26 : ℝ) ≤ ξ := by nlinarith
  have hξ_ub : ξ ≤ 1.3e28 := by nlinarith
  have hξ39 : (3.9e6 : ℝ) < ξ := by linarith
  have hξ0 : (0 : ℝ) < ξ := by linarith
  have hdata := highDataCert f (by linarith) h2 ξ hξ1 hξ2
  have ht1 := abs_le.mp (cert_abs_deriv_qLimit_sub_qCore_le hξ39)
  have ht2 := abs_le.mp (cert_abs_deriv2_qLimit_sub_qCore_le hξ39)
  have htiny1 : Real.exp (-(3.7e6 : ℝ)) ≤ 1e-40 :=
    cert_exp_neg_le_tiny (by norm_num)
  have hxe : ξ * Real.exp (-(3.6e6 : ℝ)) ≤ 1e-40 :=
    cert_mul_exp_le_tiny hξ_ub
  -- transfer of the slope bound
  have hslope : (0.0398 : ℝ) < ξ * deriv qLimit ξ := by
    have hdiff : ξ * deriv qCore ξ - ξ * deriv qLimit ξ ≤ 1e-40 := by
      have h := mul_le_mul_of_nonneg_left
        (show deriv qCore ξ - deriv qLimit ξ ≤ Real.exp (-(3.7e6 : ℝ)) by
          linarith [ht1.1]) hξ0.le
      have hxe7 : ξ * Real.exp (-(3.7e6 : ℝ)) ≤ 1e-40 := by
        have hmono : Real.exp (-(3.7e6 : ℝ)) ≤ Real.exp (-(3.6e6 : ℝ)) :=
          Real.exp_le_exp.mpr (by norm_num)
        have := mul_le_mul_of_nonneg_left hmono hξ0.le
        linarith
      calc ξ * deriv qCore ξ - ξ * deriv qLimit ξ
          = ξ * (deriv qCore ξ - deriv qLimit ξ) := by ring
        _ ≤ ξ * Real.exp (-(3.7e6 : ℝ)) := h
        _ ≤ 1e-40 := hxe7
    linarith [hdata.1]
  refine ⟨hslope, by linarith [hdata.2.1, ht2.1], ?_⟩
  -- window-wide positive slope for the limit, quantitatively
  have hq'pos : (0 : ℝ) < deriv qLimit ξ := by nlinarith
  have hq'lb : (3e-30 : ℝ) < deriv qLimit ξ := by nlinarith
  -- transfer of the curvature bound
  have hPQ : ξ * deriv (deriv qCore) ξ - ξ * deriv (deriv qLimit) ξ
      ≤ 1e-40 := by
    have h := mul_le_mul_of_nonneg_left
      (show deriv (deriv qCore) ξ - deriv (deriv qLimit) ξ
          ≤ Real.exp (-(3.6e6 : ℝ)) by linarith [ht2.1]) hξ0.le
    calc ξ * deriv (deriv qCore) ξ - ξ * deriv (deriv qLimit) ξ
        = ξ * (deriv (deriv qCore) ξ - deriv (deriv qLimit) ξ) := by ring
      _ ≤ ξ * Real.exp (-(3.6e6 : ℝ)) := h
      _ ≤ 1e-40 := hxe
  linarith [hdata.2.2, ht1.1]

end Erdos320
