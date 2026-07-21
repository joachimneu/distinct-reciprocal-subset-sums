import Erdos320.Lemmas.ConstantPhaseBackward
import Erdos320.Lemmas.CertificateConsumers
import Erdos320.Lemmas.BreakpointChords
import Erdos320.Lemmas.BSlopes
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Nonconstancy of the phase `Φ` (paper `prop:nonconstant`)

This file assembles the manuscript's Proposition "Nonconstancy": the phase
function `Φ` of `prop:phase` is **not** constant on `[1, e]`.  Following the
paper's proof, we suppose `Φ ≡ C` and apply the chord lemma
(`breakpoint_chord_bounds`, paper `lem:breakpoint-chords`) at the two
certified breakpoints:

* **Low input** `N₀ = 65 659 969 = ⌊e¹⁸⌋` (`comp:low`): with `t = 0.04`,
  `ε = 4.1·10⁻⁵`, `κ = 1.061`, the certified data `Ĉ < 1.11635`,
  `σ₀ > 0.13889`, `A₊ > 0.977` give `C < 1.16` (paper eq. `low-eps` and the
  first display of the `prop:nonconstant` proof).
* **High input** `N₁ = ⌊e⁶⁵⌋` (`comp:high`): with `t = 10⁻³`, `ε = 10⁻¹²`,
  `κ = 1.021`, the certified data `Ĉ > 1.1793`, `σ₁ > 0.0398`, `A₋ < 1.005`
  give `C > 1.17`.

The two bounds are incompatible, so no constant `C` exists.

The uniform `ε`-approximations `‖𝓑 − C·q‖ < ε` on the two chord windows come
from backward propagation under the constant-phase hypothesis
(`constant_phase_backward`, paper `prop:constant-phase-backward`), fed by

* the low `ρ₄` ledger `|ρ₄| < 3.6·10⁻⁵` (`cert_low_rhoDepth_ledger`, the
  paper's four-term budget for eq. `threshold-displacement`), together with
  the **preliminary bound** `C < 3` of eq. `preliminary-C-bound` (obtained
  from `𝓑 ≤ 12.3` and `Q₄* > 4.789` at the low breakpoint), and
* the depth-free high bound `|ρ₄| < 10·E₂²/E₃ < 5.3·10⁻²³`
  (`rhoDepth_lt_of_big`, paper `cor:explicit-high-rho`), so that
  `ε = 10⁻¹²` holds with astronomic slack (paper eq. `high-eps`).

Realized numeric chain (each verified below by exact rational arithmetic):
low side `C ≤ (Ĉ + η)/A₊ < (1.11635 + 0.0148)/0.977 < 1.16`; high side
`C ≥ (Ĉ − η)/A₋ > (1.1793 − 5.1·10⁻⁸)/1.005 > 1.17`.  Relative to the paper's
displayed constants (`A₊ > 0.97934`, `η < 0.01476`, `A₋ < 1.00052`) the
formalized bounds are slightly weaker but still clear the same `1.16`/`1.17`
targets with margin.
-/

namespace Erdos320

/-! ## Elementary exponential estimates -/

/-- The backward-propagation tail is negligible on both certificate windows:
`exp(−w/110) ≤ 10⁻⁴⁰` already for `w ≥ 9.7·10⁶` (via
`exp(−135) = exp(−5)²⁷ ≤ 32⁻²⁷`). -/
theorem nc_exp_tail_le {w : ℝ} (hw : (9.7e6 : ℝ) ≤ w) :
    Real.exp (-w / 110) ≤ 1e-40 := by
  have h1 : Real.exp (-w / 110) ≤ Real.exp (-(135 : ℝ)) :=
    Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.exp (-(135 : ℝ)) = Real.exp (-5 : ℝ) ^ (27 : ℕ) := by
    rw [← Real.exp_nat_mul]; norm_num
  have h3 : Real.exp (-5 : ℝ) ^ (27 : ℕ) ≤ ((1 : ℝ) / 32) ^ (27 : ℕ) :=
    pow_le_pow_left₀ (Real.exp_pos _).le exp_neg_five_le 27
  have h4 : ((1 : ℝ) / 32) ^ (27 : ℕ) ≤ 1e-40 := by norm_num
  rw [h2] at h1
  linarith

/-- Sharp exponential upper bound from the quadratic Taylor minorant:
`exp(−c) ≤ D` whenever `(1 + c + c²/2)·D ≥ 1` (used for the chord factor
`A₊` at the low breakpoint). -/
theorem nc_exp_neg_le_of_quad {c D : ℝ} (hc : 0 ≤ c)
    (hD : 1 ≤ (1 + c + c ^ 2 / 2) * D) : Real.exp (-c) ≤ D := by
  have hq := Real.quadratic_le_exp_of_nonneg hc
  have hqpos : (0 : ℝ) < 1 + c + c ^ 2 / 2 := by positivity
  have hD0 : (0 : ℝ) < D := by nlinarith
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos c) hD0]
  have h2 : D⁻¹ ≤ 1 + c + c ^ 2 / 2 := by
    rw [inv_eq_one_div, div_le_iff₀ hD0]
    linarith
  linarith

/-- Elementary exponential upper bound `exp c ≤ D` for `c < 1` whenever
`(1 − c)·D ≥ 1` (from `1 − c ≤ exp(−c)`; used for the chord factor `A₋` at
the high breakpoint). -/
theorem nc_exp_le_of_lt_one {c D : ℝ} (hc1 : c < 1)
    (hD : 1 ≤ (1 - c) * D) : Real.exp c ≤ D := by
  have h1 : 1 - c ≤ Real.exp (-c) := Real.one_sub_le_exp_neg c
  have h1c : (0 : ℝ) < 1 - c := by linarith
  have hD0 : (0 : ℝ) < D := by nlinarith
  have heq : Real.exp c = (Real.exp (-c))⁻¹ := by rw [← Real.exp_neg, neg_neg]
  rw [heq, inv_le_comm₀ (Real.exp_pos (-c)) hD0]
  have h2 : D⁻¹ ≤ 1 - c := by
    rw [inv_eq_one_div, div_le_iff₀ hD0]
    linarith
  linarith

/-- Taylor lower bound `log 1.04 ≥ 0.0391333` (two-term alternating series
`log(1+t) ≥ t − t²/2 − t³/(1−t)` via `Real.abs_log_sub_add_sum_range_le`). -/
theorem nc_log_104_lb : (0.0391333 : ℝ) ≤ Real.log 1.04 := by
  have habs : |(-0.04 : ℝ)| = 0.04 := by
    rw [abs_of_nonpos (by norm_num : (-0.04 : ℝ) ≤ 0)]; norm_num
  have h := Real.abs_log_sub_add_sum_range_le (x := (-0.04 : ℝ))
    (by rw [habs]; norm_num) 2
  rw [habs] at h
  have hsum : (∑ i ∈ Finset.range 2, (-0.04 : ℝ) ^ (i + 1) / (i + 1))
      = -0.0392 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
  have harg : (1 : ℝ) - -0.04 = 1.04 := by norm_num
  rw [hsum, harg] at h
  have hbound : (0.04 : ℝ) ^ (2 + 1) / (1 - 0.04) ≤ 0.0000667 := by norm_num
  have h1 := (abs_le.mp h).1
  linarith

/-! ## The two chord factors, numerically -/

/-- **Lower bound for the upper chord factor at the low breakpoint**:
`A₊ = chordAplus 0.04 1.061 ≥ 0.977` (paper: `A₊ > 0.97934`; the weaker
`0.977` suffices for the final `C < 1.16` with margin, see
`nc_low_endgame`).  Numerically `(1.04)^(−0.061) = exp(−0.061·log 1.04)
≤ exp(−0.0023871) ≤ 0.9976158`, so `A₊ ≥ 0.0023842/0.00244 > 0.977`. -/
theorem nc_chordAplus_lb : (0.977 : ℝ) ≤ chordAplus 0.04 1.061 := by
  have hL' : (0.0391333 : ℝ) ≤ Real.log (1 + 0.04) := by
    rw [show ((1 : ℝ) + 0.04) = 1.04 by norm_num]
    exact nc_log_104_lb
  have hp : ((1 : ℝ) + 0.04) ^ ((1 : ℝ) - 1.061) ≤ 0.9976158 := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 1 + 0.04)]
    have harg : Real.log (1 + 0.04) * ((1 : ℝ) - 1.061) ≤ -0.0023871 := by
      linarith
    calc Real.exp (Real.log (1 + 0.04) * (1 - 1.061))
        ≤ Real.exp (-0.0023871) := Real.exp_le_exp.mpr harg
      _ ≤ 0.9976158 := nc_exp_neg_le_of_quad (by norm_num) (by norm_num)
  have hden : ((1 : ℝ) - 1.061) * 0.04 = -0.00244 := by norm_num
  rw [chordAplus, hden, div_neg, ← neg_div, neg_sub,
    le_div_iff₀ (by norm_num : (0 : ℝ) < 0.00244)]
  linarith

/-- **Upper bound for the lower chord factor at the high breakpoint**:
`A₋ = chordAminus 0.001 1.021 ≤ 1.005` (paper: `A₋ < 1.00052`; the weaker
`1.005` suffices for the final `C > 1.17` with margin, see
`nc_high_endgame`).  Numerically `(0.999)^(−0.021) = exp(0.021·(−log 0.999))
≤ exp(0.0000210211) ≤ 1.0000211`, so `A₋ ≤ 0.0000211/0.000021 ≤ 1.005`. -/
theorem nc_chordAminus_ub : chordAminus 0.001 1.021 ≤ 1.005 := by
  have hq : ((1 : ℝ) - 0.001) ^ ((1 : ℝ) - 1.021) ≤ 1.0000211 := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 1 - 0.001)]
    have hlog : Real.log (1 - 0.001) * ((1 : ℝ) - 1.021) ≤ 0.0000210211 := by
      have hinv := Real.log_le_sub_one_of_pos
        (show (0 : ℝ) < ((1 : ℝ) - 0.001)⁻¹ by norm_num)
      rw [Real.log_inv] at hinv
      have hnum : ((1 : ℝ) - 0.001)⁻¹ - 1 ≤ 0.001001002 := by norm_num
      linarith
    calc Real.exp (Real.log (1 - 0.001) * (1 - 1.021))
        ≤ Real.exp 0.0000210211 := Real.exp_le_exp.mpr hlog
      _ ≤ 1.0000211 := nc_exp_le_of_lt_one (by norm_num) (by norm_num)
  have hden : ((1 : ℝ) - 1.021) * 0.001 = -0.000021 := by norm_num
  rw [chordAminus, hden, div_neg, ← neg_div, neg_sub,
    div_le_iff₀ (by norm_num : (0 : ℝ) < 0.000021)]
  linarith

/-! ## Backward propagation in the breakpoint coordinate

`constant_phase_backward` bounds `|H̄₄ − C·Q₄*|` on phase intervals; via the
cancellation `E₃ ∘ log₃ = id` on the certificate windows this is exactly
`|𝓑 − C·qLimit|` in the breakpoint coordinate `ξ`. -/

/-- **Backward propagation, `ξ`-coordinate form**: under the constant-phase
hypothesis, for any window `[w₋, w₊]` with `0.999·w₋ ≥ 9.7·10⁶` and
`1.001·w₊ ≤ 1.3·10²⁸`, and any bound `ρ4bound` for `|ρ₄|` on the buffered
phase window, `|𝓑(ξ) − C·q(ξ)| ≤ ρ4bound + (1 + C)·exp(−0.999·w₋/110)` for
every `ξ ∈ [w₋, w₊]` (paper eq. `H4-Q4` composed with
eq. `q-breakpoint-coordinate`; `constant_phase_backward` gives the paper's
tighter tail `exp(−w₋/110)`, relaxed here to `exp(−0.999·w₋/110)` for the
downstream tail-absorption lemmas). -/
theorem nc_B_sub_C_qLimit_le {C : ℝ} (hC : 0 ≤ C)
    (hconst : ∀ u ∈ Set.Icc (1 : ℝ) (Real.exp 1), phasePhi u = C)
    {wlo whi : ℝ} (hlo : (9.7e6 : ℝ) ≤ 0.999 * wlo)
    (hhi : 1.001 * whi ≤ 1.3e28) (hwin : wlo ≤ whi)
    {ρ4bound : ℝ}
    (hρ4 : ∀ v, iteratedLog 3 (0.999 * wlo) ≤ v →
      v ≤ iteratedLog 3 (1.001 * whi) → |rhoDepth 4 v| ≤ ρ4bound)
    {ξ : ℝ} (h1 : wlo ≤ ξ) (h2 : ξ ≤ whi) :
    |B ξ - C * qLimit ξ|
      ≤ ρ4bound + (1 + C) * Real.exp (-(0.999 * wlo) / 110) := by
  have hwlo97 : (9.7e6 : ℝ) ≤ wlo := by linarith
  have hξ97 : (9.7e6 : ℝ) ≤ ξ := le_trans hwlo97 h1
  have hu1 : iteratedLog 3 wlo ≤ iteratedLog 3 ξ :=
    cpb_iteratedLog3_mono hwlo97 h1
  have hu2 : iteratedLog 3 ξ ≤ iteratedLog 3 whi :=
    cpb_iteratedLog3_mono hξ97 h2
  have h := constant_phase_backward hC hconst hlo hhi hwin hρ4
    (iteratedLog 3 ξ) hu1 hu2
  have hH : Hbar 4 (iteratedLog 3 ξ) = B ξ := by
    rw [Hbar, show (4 : ℕ) - 1 = 3 from rfl, cpb_E3_iteratedLog3 hξ97]
  rw [hH] at h
  have h' : |B ξ - C * qLimit ξ|
      ≤ ρ4bound + (1 + C) * Real.exp (-(wlo) / 110) := h
  have htail : Real.exp (-(wlo) / 110) ≤ Real.exp (-(0.999 * wlo) / 110) :=
    Real.exp_le_exp.mpr (by linarith)
  have hCtail := mul_le_mul_of_nonneg_left htail
    (show (0 : ℝ) ≤ 1 + C by linarith)
  linarith only [h', hCtail]

/-! ## The `ρ₄` bounds on the two enlarged windows -/

/-- The low `ρ₄` input for backward propagation: `|ρ₄| ≤ 3.6·10⁻⁵` on the
buffered phase window of the low chord window `[0.96·x(f), 1.04·x(f)]`
(paper `comp:low`, the four-term budget of eq. `threshold-displacement`,
via `cert_low_rhoDepth_ledger` and the window containment
`cert_low_window`). -/
theorem nc_low_rho4 {f : ℝ} (h1 : (2.787 : ℝ) ≤ f) (h2 : f ≤ 2.792) :
    ∀ v, iteratedLog 3 (0.999 * (0.96 * lowBreakpointX f)) ≤ v →
      v ≤ iteratedLog 3 (1.001 * (1.04 * lowBreakpointX f)) →
      |rhoDepth 4 v| ≤ 3.6e-5 := by
  obtain ⟨hw1, hw2⟩ := cert_low_window h1 h2
  intro v hv1 hv2
  have hxpos : (0 : ℝ) < lowBreakpointX f := by nlinarith
  have hlo97 : (9.7e6 : ℝ) ≤ 0.999 * (0.96 * lowBreakpointX f) := by linarith
  have hhi97 : (9.7e6 : ℝ) ≤ 1.001 * (1.04 * lowBreakpointX f) := by
    nlinarith
  have hE1 := E_mono 3 hv1
  rw [cpb_E3_iteratedLog3 hlo97] at hE1
  have hE2 := E_mono 3 hv2
  rw [cpb_E3_iteratedLog3 hhi97] at hE2
  exact (cert_low_rhoDepth_ledger (by linarith) (by linarith)).le

/-- The high `ρ₄` input for backward propagation: `|ρ₄| ≤ 5.3·10⁻²³` on the
buffered phase window of the high chord window `[0.999·x(f), 1.001·x(f)]` —
the paper's `comp:high` bound `‖ρ₄‖_{U⁺} ≤ 5.3·10⁻²³` digit-for-digit, from
the depth-free bound `|ρ₄| < 10·E₂²/E₃` of `cor:explicit-high-rho` with
`E₂ ≤ 65` and `E₃ ≥ 8·10²⁶`. -/
theorem nc_high_rho4 {f : ℝ} (h1 : (3.2411 : ℝ) ≤ f) (h2 : f ≤ 46) :
    ∀ v, iteratedLog 3 (0.999 * (0.999 * highBreakpointX f)) ≤ v →
      v ≤ iteratedLog 3 (1.001 * (1.001 * highBreakpointX f)) →
      |rhoDepth 4 v| ≤ 5.3e-23 := by
  obtain ⟨hw1, hw2⟩ := cert_high_window h1 h2
  intro v hv1 hv2
  have hxpos : (0 : ℝ) < highBreakpointX f := by nlinarith
  have hlo97 : (9.7e6 : ℝ) ≤ 0.999 * (0.999 * highBreakpointX f) := by
    linarith
  have hhi97 : (9.7e6 : ℝ) ≤ 1.001 * (1.001 * highBreakpointX f) := by
    nlinarith
  have hE1 := E_mono 3 hv1
  rw [cpb_E3_iteratedLog3 hlo97] at hE1
  have hE2 := E_mono 3 hv2
  rw [cpb_E3_iteratedLog3 hhi97] at hE2
  have hbig : (8e26 : ℝ) ≤ E 3 v := by linarith
  have hub : E 3 v ≤ 1.3e28 := by linarith
  have hE3exp : E 3 v = Real.exp (E 2 v) := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, E_succ]
  have hE2eq : E 2 v = Real.log (E 3 v) := by rw [hE3exp, Real.log_exp]
  have hE2ub : E 2 v ≤ 65 := by
    rw [hE2eq]
    exact cpb_log_le_sixtyfive (by linarith) hub
  have hE2lb : (61.9 : ℝ) ≤ E 2 v := by
    rw [hE2eq]
    exact high_logX_lb hbig
  have hbig' : (8e26 : ℝ) ≤ E (4 - 1) v := hbig
  have hrho : |rhoDepth 4 v| < 10 * (E 2 v ^ 2 / E 3 v) :=
    rhoDepth_lt_of_big (by norm_num) hbig'
  have hfinal : 10 * (E 2 v ^ 2 / E 3 v) ≤ 5.3e-23 := by
    rw [← mul_div_assoc, div_le_iff₀ (by linarith : (0 : ℝ) < E 3 v)]
    nlinarith [sq_nonneg (65 - E 2 v)]
  linarith

/-! ## The preliminary bound `C < 3` (paper eq. `preliminary-C-bound`) -/

/-- **Preliminary bound** (paper eq. `preliminary-C-bound`, which displays
`C < 2.63 < 3`; here only the consumed `C < 3` is stated): under the
constant-phase hypothesis, `C < 3`.  From backward propagation at the low
breakpoint itself, via a sharper `𝓑`-bound than the paper's route:
`4.789·C < C·Q₄*(u₀) ≤ 𝓑(x₀) + ε ≤ 12.3 + 3.6·10⁻⁵ + (1 + C)·10⁻⁴⁰`. -/
theorem nc_prelim_C_lt_three {C : ℝ} (hC : 0 ≤ C)
    (hconst : ∀ u ∈ Set.Icc (1 : ℝ) (Real.exp 1), phasePhi u = C) :
    C < 3 := by
  obtain ⟨hf1, hf2⟩ := cert_F_N0_bounds
  obtain ⟨hw1, hw2⟩ := cert_low_window hf1 hf2
  have hxpos : (0 : ℝ) < lowBreakpointX (F 65659969) := by nlinarith
  have happ := nc_B_sub_C_qLimit_le hC hconst
    (wlo := 0.96 * lowBreakpointX (F 65659969))
    (whi := 1.04 * lowBreakpointX (F 65659969))
    (by linarith) (by linarith) (by linarith) (nc_low_rho4 hf1 hf2)
    (ξ := lowBreakpointX (F 65659969)) (by linarith) (by linarith)
  have htiny := nc_exp_tail_le
    (w := 0.999 * (0.96 * lowBreakpointX (F 65659969))) (by linarith)
  have h1C : (1 + C)
      * Real.exp (-(0.999 * (0.96 * lowBreakpointX (F 65659969))) / 110)
      ≤ (1 + C) * 1e-40 :=
    mul_le_mul_of_nonneg_left htiny (by linarith)
  have hx0lb : (9725449 : ℝ) ≤ lowBreakpointX (F 65659969) := by linarith
  have hx0ub : lowBreakpointX (F 65659969) ≤ 10632947 := by linarith
  have hB := cert_B_low_le hx0lb hx0ub
  have hQ4 : (4.789 : ℝ) < qLimit (lowBreakpointX (F 65659969)) :=
    cert_low_Q4_positive_limit hx0lb hx0ub
  have habs := (abs_le.mp happ).1
  have hlow : C * 4.789 ≤ C * qLimit (lowBreakpointX (F 65659969)) :=
    mul_le_mul_of_nonneg_left hQ4.le hC
  linarith

/-! ## The endgame arithmetic of the two chord applications -/

/-- **Low-side endgame** (first display of the `prop:nonconstant` proof):
from `σ₀ > 0.13889`, `A₊ ≥ 0.977`, and the slope-matched bound
`x₀ < 1.11635·N₀·σ₀`, the chord upper bound
`C ≤ (Ĉ + η)/A₊` forces `C < 1.16`
(realized: `Ĉ < 1.11635`, `η < 0.0148`, `(1.11635 + 0.0148)/0.977 < 1.16`). -/
theorem nc_low_endgame {C x σ A : ℝ} (hσ : (0.13889 : ℝ) < σ)
    (hA : (0.977 : ℝ) ≤ A)
    (hx : x < 1.11635 * (65659969 * σ))
    (hC : C ≤ (x / (((65659969 : ℕ) : ℝ) * σ) + 2 * 4.1e-5 / (0.04 * σ)) / A) :
    C < 1.16 := by
  have hσ0 : (0 : ℝ) < σ := by linarith
  have hA0 : (0 : ℝ) < A := by linarith
  have hden : (0 : ℝ) < ((65659969 : ℕ) : ℝ) * σ :=
    mul_pos (by norm_num) hσ0
  have h1 : x / (((65659969 : ℕ) : ℝ) * σ) < 1.11635 := by
    rw [div_lt_iff₀ hden, show (((65659969 : ℕ) : ℝ)) = 65659969 by norm_num]
    linarith
  have h2 : 2 * (4.1e-5 : ℝ) / (0.04 * σ) < 0.0148 := by
    rw [div_lt_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 0.04) hσ0)]
    linarith
  have h3 : (x / (((65659969 : ℕ) : ℝ) * σ) + 2 * 4.1e-5 / (0.04 * σ)) / A
      < 1.16 := by
    rw [div_lt_iff₀ hA0]
    linarith
  linarith

/-- **High-side endgame** (second display of the `prop:nonconstant` proof):
from `σ₁ > 0.0398`, `A₋ ≤ 1.005`, and the slope-matched bound
`x₁ > 1.1793·N₁·σ₁`, the chord lower bound `(Ĉ − η)/A₋ ≤ C` forces
`C > 1.17` (realized: `Ĉ > 1.1793`, `η < 5.1·10⁻⁸`,
`(1.1793 − 5.1·10⁻⁸)/1.005 > 1.17`). -/
theorem nc_high_endgame {C x σ A : ℝ} (hσ : (0.0398 : ℝ) < σ)
    (hA0 : 0 < A) (hA : A ≤ 1.005)
    (hx : 1.1793 * (16948892444103337141417836114 * σ) < x)
    (hC : (x / (((16948892444103337141417836114 : ℕ) : ℝ) * σ)
        - 2 * 1e-12 / (0.001 * σ)) / A ≤ C) :
    1.17 < C := by
  have hσ0 : (0 : ℝ) < σ := by linarith
  have hden : (0 : ℝ) < ((16948892444103337141417836114 : ℕ) : ℝ) * σ :=
    mul_pos (by norm_num) hσ0
  have h1 : (1.1793 : ℝ)
      < x / (((16948892444103337141417836114 : ℕ) : ℝ) * σ) := by
    rw [lt_div_iff₀ hden, show (((16948892444103337141417836114 : ℕ) : ℝ))
      = 16948892444103337141417836114 by norm_num]
    linarith
  have h2 : 2 * (1e-12 : ℝ) / (0.001 * σ) < 5.1e-8 := by
    rw [div_lt_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 0.001) hσ0)]
    linarith
  have h3 : (1.17 : ℝ)
      < (x / (((16948892444103337141417836114 : ℕ) : ℝ) * σ)
          - 2 * 1e-12 / (0.001 * σ)) / A := by
    rw [lt_div_iff₀ hA0]
    linarith
  linarith

/-! ## The two chord applications -/

set_option maxHeartbeats 800000 in
/-- **Low breakpoint chord bound** (paper `prop:nonconstant`, first half,
eq. `low-eps`): under the constant-phase hypothesis, `C < 1.16`.  Chord
lemma at `x₀ = g(N₀)` with `t = 0.04`, `ε = 4.1·10⁻⁵`, `κ = 1.061`. -/
theorem nc_low_C_lt {C : ℝ} (hC : 0 ≤ C)
    (hconst : ∀ u ∈ Set.Icc (1 : ℝ) (Real.exp 1), phasePhi u = C) :
    C < 1.16 := by
  obtain ⟨hf1, hf2⟩ := cert_F_N0_bounds
  obtain ⟨hw1, hw2⟩ := cert_low_window hf1 hf2
  have hxpos : (0 : ℝ) < lowBreakpointX (F 65659969) := by nlinarith
  have hC3 : C < 3 := nc_prelim_C_lt_three hC hconst
  -- window membership: chord-window points sit in the certificate window
  have hwmem : ∀ ξ ∈ Set.Icc (lowBreakpointX (F 65659969) * (1 - 0.04))
      (lowBreakpointX (F 65659969) * (1 + 0.04)),
      0.96 * lowBreakpointX (F 65659969) ≤ ξ ∧
        ξ ≤ 1.04 * lowBreakpointX (F 65659969) ∧ (3.9e6 : ℝ) < ξ := by
    intro ξ hξ
    obtain ⟨ha, hb⟩ := hξ
    exact ⟨by linarith, by linarith, by linarith⟩
  -- `ε = 4.1·10⁻⁵` uniform approximation on the chord window (eq. `low-eps`)
  have happrox : ∀ ξ ∈ Set.Icc (lowBreakpointX (F 65659969) * (1 - 0.04))
      (lowBreakpointX (F 65659969) * (1 + 0.04)),
      |B ξ - C * qLimit ξ| ≤ 4.1e-5 := by
    intro ξ hξ
    obtain ⟨hm1, hm2, -⟩ := hwmem ξ hξ
    have h := nc_B_sub_C_qLimit_le hC hconst
      (wlo := 0.96 * lowBreakpointX (F 65659969))
      (whi := 1.04 * lowBreakpointX (F 65659969))
      (by linarith) (by linarith) (by linarith) (nc_low_rho4 hf1 hf2) hm1 hm2
    have htiny := nc_exp_tail_le
      (w := 0.999 * (0.96 * lowBreakpointX (F 65659969))) (by linarith)
    have h1C : (1 + C)
        * Real.exp (-(0.999 * (0.96 * lowBreakpointX (F 65659969))) / 110)
        ≤ (1 + C) * 1e-40 :=
      mul_le_mul_of_nonneg_left htiny (by linarith)
    linarith
  -- the concavity chord facts at the breakpoint `x₀ = g(N₀)` (lem:B-slopes)
  have hgN : g 65659969 = lowBreakpointX (F 65659969) := cert_gN0_eq
  have hδ0 : (0 : ℝ) ≤ 0.04 * lowBreakpointX (F 65659969) :=
    mul_nonneg (by norm_num) hxpos.le
  have hchord_up : B (lowBreakpointX (F 65659969) * (1 + 0.04))
      - B (lowBreakpointX (F 65659969))
      ≤ 0.04 * lowBreakpointX (F 65659969) / ((65659969 : ℕ) : ℝ) := by
    have h := B_chord_up 65659969 hδ0
    rw [hgN] at h
    rw [show lowBreakpointX (F 65659969) * (1 + 0.04)
        = lowBreakpointX (F 65659969) + 0.04 * lowBreakpointX (F 65659969)
      by ring]
    calc B (lowBreakpointX (F 65659969)
            + 0.04 * lowBreakpointX (F 65659969))
          - B (lowBreakpointX (F 65659969))
        ≤ 0.04 * lowBreakpointX (F 65659969)
            / (((65659969 : ℕ) : ℝ) + 1) := h
      _ ≤ 0.04 * lowBreakpointX (F 65659969) / ((65659969 : ℕ) : ℝ) :=
          div_le_div_of_nonneg_left hδ0 (by norm_num) (by linarith)
  have hchord_down : 0.04 * lowBreakpointX (F 65659969) / ((65659969 : ℕ) : ℝ)
      ≤ B (lowBreakpointX (F 65659969))
        - B (lowBreakpointX (F 65659969) * (1 - 0.04)) := by
    have h := B_chord_down 65659969 (by norm_num) hδ0
    rw [hgN] at h
    rw [show lowBreakpointX (F 65659969) * (1 - 0.04)
        = lowBreakpointX (F 65659969) - 0.04 * lowBreakpointX (F 65659969)
      by ring]
    exact h
  -- the chord lemma (paper lem:breakpoint-chords)
  have hbounds := breakpoint_chord_bounds B qLimit (deriv qLimit)
    (deriv (deriv qLimit)) (lowBreakpointX (F 65659969)) 0.04 C (4.1e-5)
    1.061 65659969 hxpos (by norm_num) (by norm_num) (by norm_num) hC
    (by norm_num)
    (fun ξ hξ => cert_hasDerivAt_qLimit_self (hwmem ξ hξ).2.2)
    (fun ξ hξ => cert_hasDerivAt_deriv_qLimit_self (hwmem ξ hξ).2.2)
    (fun ξ hξ =>
      (cert_low_curvature_limit hf1 hf2 (hwmem ξ hξ).1 (hwmem ξ hξ).2.1).1)
    (fun ξ hξ =>
      ((cert_low_curvature_limit hf1 hf2 (hwmem ξ hξ).1
        (hwmem ξ hξ).2.1).2.2).le)
    happrox hchord_up hchord_down
  -- the certified slope data at the breakpoint (comp:low)
  have hx0lb : (9725449 : ℝ) ≤ lowBreakpointX (F 65659969) := by linarith
  have hx39 : (3.9e6 : ℝ) < lowBreakpointX (F 65659969) := by linarith
  have hy16 : (16 : ℝ) ≤ Real.log (lowBreakpointX (F 65659969)) :=
    cert_log_ge_sixteen (by linarith)
  have hy0 : (0 : ℝ) < Real.log (lowBreakpointX (F 65659969)) := by linarith
  have hslope := cert_qLimit_slope hx39
  have hσlb : (0.13889 : ℝ) < lowBreakpointX (F 65659969)
      * deriv qLimit (lowBreakpointX (F 65659969)) := by
    rw [hslope, lt_div_iff₀ hy0]
    exact cert_low_slope_margin_limit hf1 hf2
  have hQeq : QrefLimit3 (iteratedLog 3 (lowBreakpointX (F 65659969)))
      = lowBreakpointX (F 65659969)
          * deriv qLimit (lowBreakpointX (F 65659969))
        * Real.log (lowBreakpointX (F 65659969)) := by
    rw [hslope, div_mul_cancel₀ _ hy0.ne']
  have hmatch := cert_low_slope_match_limit hf1 hf2
  rw [hQeq] at hmatch
  obtain ⟨hX1, -⟩ := cert_log_N0_bounds
  have hf₀lt : F 65659969 < 1.11635 * (Real.log 65659969
      * (lowBreakpointX (F 65659969)
        * deriv qLimit (lowBreakpointX (F 65659969)))) := by
    nlinarith [hy0, hmatch]
  have hX0 : (0 : ℝ) < Real.log 65659969 := by linarith
  have hxid : lowBreakpointX (F 65659969) * Real.log 65659969
      = 65659969 * F 65659969 := by
    rw [lowBreakpointX, div_mul_cancel₀ _ hX0.ne']
  have hChat : lowBreakpointX (F 65659969)
      < 1.11635 * (65659969 * (lowBreakpointX (F 65659969)
          * deriv qLimit (lowBreakpointX (F 65659969)))) := by
    nlinarith [hf₀lt, hX1, hxid]
  exact nc_low_endgame hσlb nc_chordAplus_lb hChat hbounds.2

set_option maxHeartbeats 800000 in
/-- **High breakpoint chord bound** (paper `prop:nonconstant`, second half,
eq. `high-eps`): under the constant-phase hypothesis, `C > 1.17`.  Chord
lemma at `x₁ = g(N₁)` with `t = 10⁻³`, `ε = 10⁻¹²`, `κ = 1.021`. -/
theorem nc_high_C_gt {C : ℝ} (hC : 0 ≤ C)
    (hconst : ∀ u ∈ Set.Icc (1 : ℝ) (Real.exp 1), phasePhi u = C) :
    1.17 < C := by
  have hf1 : (3.2411 : ℝ) ≤ F 16948892444103337141417836114 :=
    cert_F_N1_bounds.1.le
  have hf2 : F 16948892444103337141417836114 ≤ 46 := cert_F_N1_bounds.2.le
  obtain ⟨hw1, hw2⟩ := cert_high_window hf1 hf2
  have hxpos : (0 : ℝ)
      < highBreakpointX (F 16948892444103337141417836114) := by nlinarith
  have hC3 : C < 3 := nc_prelim_C_lt_three hC hconst
  -- window membership: chord-window points sit in the certificate window
  have hwmem : ∀ ξ ∈ Set.Icc
      (highBreakpointX (F 16948892444103337141417836114) * (1 - 0.001))
      (highBreakpointX (F 16948892444103337141417836114) * (1 + 0.001)),
      0.999 * highBreakpointX (F 16948892444103337141417836114) ≤ ξ ∧
        ξ ≤ 1.001 * highBreakpointX (F 16948892444103337141417836114) ∧
        (3.9e6 : ℝ) < ξ := by
    intro ξ hξ
    obtain ⟨ha, hb⟩ := hξ
    exact ⟨by linarith, by linarith, by linarith⟩
  -- `ε = 10⁻¹²` uniform approximation on the chord window (eq. `high-eps`)
  have happrox : ∀ ξ ∈ Set.Icc
      (highBreakpointX (F 16948892444103337141417836114) * (1 - 0.001))
      (highBreakpointX (F 16948892444103337141417836114) * (1 + 0.001)),
      |B ξ - C * qLimit ξ| ≤ 1e-12 := by
    intro ξ hξ
    obtain ⟨hm1, hm2, -⟩ := hwmem ξ hξ
    have h := nc_B_sub_C_qLimit_le hC hconst
      (wlo := 0.999 * highBreakpointX (F 16948892444103337141417836114))
      (whi := 1.001 * highBreakpointX (F 16948892444103337141417836114))
      (by linarith) (by linarith) (by linarith) (nc_high_rho4 hf1 hf2) hm1 hm2
    have htiny := nc_exp_tail_le
      (w := 0.999 * (0.999
        * highBreakpointX (F 16948892444103337141417836114))) (by linarith)
    have h1C : (1 + C) * Real.exp (-(0.999 * (0.999
        * highBreakpointX (F 16948892444103337141417836114))) / 110)
        ≤ (1 + C) * 1e-40 :=
      mul_le_mul_of_nonneg_left htiny (by linarith)
    linarith
  -- window-wide slope positivity (from `ξ·q'(ξ) > 0.0398` with `ξ > 0`)
  have hq'pos : ∀ ξ ∈ Set.Icc
      (highBreakpointX (F 16948892444103337141417836114) * (1 - 0.001))
      (highBreakpointX (F 16948892444103337141417836114) * (1 + 0.001)),
      0 < deriv qLimit ξ := by
    intro ξ hξ
    obtain ⟨hm1, hm2, hm3⟩ := hwmem ξ hξ
    have hd := (cert_high_data_limit hf1 hf2 hm1 hm2).1
    nlinarith
  -- the concavity chord facts at the breakpoint `x₁ = g(N₁)` (lem:B-slopes)
  have hgN : g 16948892444103337141417836114
      = highBreakpointX (F 16948892444103337141417836114) := cert_gN1_eq
  have hδ0 : (0 : ℝ)
      ≤ 0.001 * highBreakpointX (F 16948892444103337141417836114) :=
    mul_nonneg (by norm_num) hxpos.le
  have hchord_up :
      B (highBreakpointX (F 16948892444103337141417836114) * (1 + 0.001))
        - B (highBreakpointX (F 16948892444103337141417836114))
      ≤ 0.001 * highBreakpointX (F 16948892444103337141417836114)
          / ((16948892444103337141417836114 : ℕ) : ℝ) := by
    have h := B_chord_up 16948892444103337141417836114 hδ0
    rw [hgN] at h
    rw [show highBreakpointX (F 16948892444103337141417836114) * (1 + 0.001)
        = highBreakpointX (F 16948892444103337141417836114)
          + 0.001 * highBreakpointX (F 16948892444103337141417836114)
      by ring]
    calc B (highBreakpointX (F 16948892444103337141417836114)
            + 0.001 * highBreakpointX (F 16948892444103337141417836114))
          - B (highBreakpointX (F 16948892444103337141417836114))
        ≤ 0.001 * highBreakpointX (F 16948892444103337141417836114)
            / (((16948892444103337141417836114 : ℕ) : ℝ) + 1) := h
      _ ≤ 0.001 * highBreakpointX (F 16948892444103337141417836114)
            / ((16948892444103337141417836114 : ℕ) : ℝ) :=
          div_le_div_of_nonneg_left hδ0 (by norm_num) (by linarith)
  have hchord_down :
      0.001 * highBreakpointX (F 16948892444103337141417836114)
          / ((16948892444103337141417836114 : ℕ) : ℝ)
      ≤ B (highBreakpointX (F 16948892444103337141417836114))
        - B (highBreakpointX (F 16948892444103337141417836114)
            * (1 - 0.001)) := by
    have h := B_chord_down 16948892444103337141417836114 (by norm_num) hδ0
    rw [hgN] at h
    rw [show highBreakpointX (F 16948892444103337141417836114) * (1 - 0.001)
        = highBreakpointX (F 16948892444103337141417836114)
          - 0.001 * highBreakpointX (F 16948892444103337141417836114)
      by ring]
    exact h
  -- the chord lemma (paper lem:breakpoint-chords)
  have hbounds := breakpoint_chord_bounds B qLimit (deriv qLimit)
    (deriv (deriv qLimit))
    (highBreakpointX (F 16948892444103337141417836114)) 0.001 C (1e-12)
    1.021 16948892444103337141417836114 hxpos (by norm_num) (by norm_num)
    (by norm_num) hC (by norm_num)
    (fun ξ hξ => cert_hasDerivAt_qLimit_self (hwmem ξ hξ).2.2)
    (fun ξ hξ => cert_hasDerivAt_deriv_qLimit_self (hwmem ξ hξ).2.2)
    hq'pos
    (fun ξ hξ =>
      ((cert_high_data_limit hf1 hf2 (hwmem ξ hξ).1 (hwmem ξ hξ).2.1).2.2).le)
    happrox hchord_up hchord_down
  -- the certified slope data at the breakpoint (comp:high)
  have hx8 : (8e26 : ℝ)
      ≤ highBreakpointX (F 16948892444103337141417836114) := by linarith
  have hx39 : (3.9e6 : ℝ)
      < highBreakpointX (F 16948892444103337141417836114) := by linarith
  have hσlb : (0.0398 : ℝ)
      < highBreakpointX (F 16948892444103337141417836114)
        * deriv qLimit (highBreakpointX (F 16948892444103337141417836114)) :=
    (cert_high_data_limit hf1 hf2 (by linarith) (by linarith)).1
  have hy619 : (61.9 : ℝ)
      ≤ Real.log (highBreakpointX (F 16948892444103337141417836114)) :=
    high_logX_lb hx8
  have hy0 : (0 : ℝ)
      < Real.log (highBreakpointX (F 16948892444103337141417836114)) := by
    linarith
  have hslope := cert_qLimit_slope hx39
  have hQeq : QrefLimit3
      (iteratedLog 3 (highBreakpointX (F 16948892444103337141417836114)))
      = highBreakpointX (F 16948892444103337141417836114)
          * deriv qLimit (highBreakpointX (F 16948892444103337141417836114))
        * Real.log (highBreakpointX (F 16948892444103337141417836114)) := by
    rw [hslope, div_mul_cancel₀ _ hy0.ne']
  have hmatch := cert_high_slope_matched_limit hf1 hf2
  rw [hQeq] at hmatch
  obtain ⟨hY1, -⟩ := cert_log_N1_bounds
  have hf₁lt : 1.1793 * (Real.log 16948892444103337141417836114
      * (highBreakpointX (F 16948892444103337141417836114)
        * deriv qLimit (highBreakpointX (F 16948892444103337141417836114))))
      < F 16948892444103337141417836114 := by
    nlinarith [hy0, hmatch]
  have hY0 : (0 : ℝ) < Real.log 16948892444103337141417836114 := by linarith
  have hxid : highBreakpointX (F 16948892444103337141417836114)
      * Real.log 16948892444103337141417836114
      = 16948892444103337141417836114
        * F 16948892444103337141417836114 := by
    rw [highBreakpointX, div_mul_cancel₀ _ hY0.ne']
  have hChat : 1.1793 * (16948892444103337141417836114
      * (highBreakpointX (F 16948892444103337141417836114)
        * deriv qLimit (highBreakpointX (F 16948892444103337141417836114))))
      < highBreakpointX (F 16948892444103337141417836114) := by
    nlinarith [hf₁lt, hY1, hxid]
  exact nc_high_endgame hσlb
    (chordAminus_pos (by norm_num) (by norm_num) (by norm_num))
    nc_chordAminus_ub hChat hbounds.1

/-! ## The nonconstancy proposition -/

/-- **Paper `prop:nonconstant` ("Nonconstancy")**: the phase `Φ` of
`prop:phase` is **not** constant on `[1, e]`.  Any constant value `C` would
have to be nonnegative (`Φ > 0`), below `1.16` by the low finite input, and
above `1.17` by the high finite input — a contradiction. -/
theorem phasePhi_nonconstant :
    ¬ ∃ C : ℝ, ∀ u ∈ Set.Icc (1 : ℝ) (Real.exp 1), phasePhi u = C := by
  rintro ⟨C, hconst⟩
  have h1mem : (1 : ℝ) ∈ Set.Icc (1 : ℝ) (Real.exp 1) :=
    ⟨le_rfl, by linarith [Real.exp_one_gt_d9]⟩
  have hC : 0 ≤ C := by
    have hpos := phasePhi_pos 1 h1mem
    have heq := hconst 1 h1mem
    linarith [heq ▸ hpos]
  linarith [nc_low_C_lt hC hconst, nc_high_C_gt hC hconst]

/-- Two-point form of `prop:nonconstant`: the phase `Φ` takes at least two
distinct values on `[1, e]`. -/
theorem phasePhi_exists_ne :
    ∃ u ∈ Set.Icc (1 : ℝ) (Real.exp 1), ∃ v ∈ Set.Icc (1 : ℝ) (Real.exp 1),
      phasePhi u ≠ phasePhi v := by
  by_contra h
  push Not at h
  exact phasePhi_nonconstant ⟨phasePhi 1, fun u hu =>
    h u hu 1 ⟨le_rfl, by linarith [Real.exp_one_gt_d9]⟩⟩

end Erdos320
