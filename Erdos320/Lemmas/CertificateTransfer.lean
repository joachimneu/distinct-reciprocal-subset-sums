import Erdos320.Assumptions
import Erdos320.Lemmas.BackwardReferenceLimit
import Erdos320.Lemmas.ExplicitHighAveraging
import Erdos320.Lemmas.IteratedExpBounds
import Erdos320.Lemmas.HighFiniteAssembly
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Certificate transfer: from the reference core to the limit, plus window
# numerics and the low `ρ₄` ledger

The directed-interval certificate lemmas (proved in `CertLow*.lean` /
`CertHigh*.lean`) quantify over the Lean-defined reference *core*
`Q̃₄ = QrefCore4`, `Q̃₃ = QrefCore3` and the core breakpoint profile
`q̃ = qCore`.  The chord-lemma applications (`lem:breakpoint-chords`,
`prop:nonconstant`) need the corresponding facts for the *limits*
`Q₄* = QrefLimit 4`, `Q₃* = QrefLimit3` and the limit profile
`q_br = qLimit` (paper `eq:q-breakpoint-coordinate`) below.  This file is the plumbing between the two, together with
the elementary numerics of the paper's certificate sections:

* **Numeric anchors** — two-sided bounds on `log N₀`, `log N₁`
  (`cert_log_N0_bounds`, `cert_log_N1_bounds`), the widened `F`-enclosures
  (`cert_F_N0_bounds`, `cert_F_N1_bounds`, using `F(N₁) ≤ log N₁ · log 2 < 46`
  from `S ≤ 2^N`), the breakpoint identities `g(Nᵢ) = x(F(Nᵢ))`
  (`cert_gN0_eq`, `cert_gN1_eq`), and the window containments
  `eq:low-breakpoint-window` / the high `8·10²⁶ < w < 1.3·10²⁸`
  (`cert_low_window`, `cert_high_window`).
* **The breakpoint-coordinate calculus** (`eq:q-breakpoint-coordinate`,
  `eq:q-slope`) — `qLimit ξ = Q₄*(log₃ ξ)`, its first two derivatives by the
  chain rule through `iteratedLog 3` (`cert_hasDerivAt_qLimit`,
  `cert_hasDerivAt_deriv_qLimit`, and the `qCore` analogues), and the exact
  slope identity `ξ·q_br'(ξ) = Q₃*(log₃ ξ)/log ξ` (`cert_qLimit_slope`,
  `cert_qCore_slope`).
* **Core→limit transfer on the certificate windows** — using the proved
  `R7-tail` bounds (`≤ exp(−3.7·10⁶)`, `BackwardReferenceLimit.lean`), each
  core certificate constant is carried to the limit objects with an explicit
  slackening (documented at each lemma; the curvature constants move
  `1.0601 → 1.061` and `1.0201 → 1.021`, the slope-match `1.1163 → 1.11635`,
  the high slope-match `1.1794 → 1.1793`, the margin `0.1389 → 0.13889`,
  `4.79 → 4.789`, `0.0399 → 0.0398`).  Since the limit second derivative
  cannot be certified `≤ 0` exactly, the transferred form is
  `≤ exp(−3.6·10⁶)`, together with a *quantitative* window-wide slope lower
  bound (`cert_low_qCore_deriv_window_lb`, `cert_low_qLimit_deriv_window_lb`)
  obtained from `eq:low-slope-margin` at the breakpoint plus the certified
  curvature (monotonicity of `ξ ↦ q̃'(ξ)·ξ²` on the window).
* **The low `ρ₄` ledger** (`comp:low`, proof around
  `eq:threshold-displacement`) — `|ρ(w)| < 3.6·10⁻⁵` on the enlarged low
  window `[9 725 449, 10 632 947]` (`cert_low_rho_ledger`,
  `cert_low_rhoDepth_ledger`), mirroring `high_rho_abs_lt` with the realized
  four-term budget `1.2·10⁻⁵ + 1.26·10⁻⁶ + 2.23·10⁻⁵ + 1.1·10⁻⁷` (the
  paper's corresponding `eq:threshold-displacement` ledger runs
  `1.2000·10⁻⁵, 1.2540·10⁻⁶, 2.2710·10⁻⁵, 10⁻¹⁰⁰⁰` — third term tighter,
  fourth coarser here; both totals clear the same `3.6·10⁻⁵`), via the
  elementary count-function bound `𝓑(w) ≤ 12.3` (`cert_B_low_le`).

Everything here is independent of the constant-phase hypothesis.
-/

namespace Erdos320

/-! ## Tiny-exponential absorption helpers

All transfer margins are at least `≈ 10⁻¹²`, while every tail is at most
`exp(−3.5·10⁶)`; the lemmas below crush the tails to `10⁻⁴⁰` once and for
all so the transfers are plain `linarith` steps. -/

/-- `exp(−c) ≤ 10⁻⁴⁰` for `c ≥ 3.5·10⁶` (via `exp(−135) ≤ 2⁻¹³⁵`). -/
theorem cert_exp_neg_le_tiny {c : ℝ} (hc : (3.5e6 : ℝ) ≤ c) :
    Real.exp (-c) ≤ 1e-40 := by
  have h1 : Real.exp (-c) ≤ Real.exp (-(135 : ℝ)) :=
    Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.exp (-(135 : ℝ)) = Real.exp (-5 : ℝ) ^ (27 : ℕ) := by
    rw [← Real.exp_nat_mul]; norm_num
  have h3 : Real.exp (-5 : ℝ) ^ (27 : ℕ) ≤ ((1 : ℝ) / 32) ^ (27 : ℕ) :=
    pow_le_pow_left₀ (Real.exp_pos _).le exp_neg_five_le 27
  have h4 : ((1 : ℝ) / 32) ^ (27 : ℕ) ≤ 1e-40 := by norm_num
  rw [h2] at h1
  linarith

/-- Any factor up to `1.3·10²⁸` is absorbed by one `exp(10⁵)` of tail slack:
`ξ·exp(−3.6·10⁶) ≤ 10⁻⁴⁰` for `ξ ≤ 1.3·10²⁸`. -/
theorem cert_mul_exp_le_tiny {ξ : ℝ} (h1 : ξ ≤ 1.3e28) :
    ξ * Real.exp (-(3.6e6 : ℝ)) ≤ 1e-40 := by
  have hbig : (1.3e28 : ℝ) ≤ Real.exp (1e5 : ℝ) := by
    have h := pow_div_factorial_le_exp (show (0 : ℝ) ≤ 1e5 by norm_num) 7
    have hfac : ((Nat.factorial 7 : ℕ) : ℝ) = 5040 := by norm_num
    rw [hfac] at h
    nlinarith [h]
  have hmul : ξ * Real.exp (-(3.6e6 : ℝ))
      ≤ Real.exp (1e5 : ℝ) * Real.exp (-(3.6e6 : ℝ)) :=
    mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
  have hadd : Real.exp (1e5 : ℝ) * Real.exp (-(3.6e6 : ℝ))
      = Real.exp (-(3.5e6 : ℝ)) := by
    rw [← Real.exp_add]; norm_num
  have := cert_exp_neg_le_tiny (le_refl (3.5e6 : ℝ))
  linarith [hadd ▸ hmul]

/-- Two `exp(−3.7·10⁶)` tails fit inside one `exp(−3.6·10⁶)`. -/
theorem cert_two_exp_le :
    2 * Real.exp (-(3.7e6 : ℝ)) ≤ Real.exp (-(3.6e6 : ℝ)) := by
  have hadd : Real.exp (1e5 : ℝ) * Real.exp (-(3.7e6 : ℝ))
      = Real.exp (-(3.6e6 : ℝ)) := by
    rw [← Real.exp_add]; norm_num
  have h2 : (2 : ℝ) ≤ Real.exp (1e5 : ℝ) := by
    have := Real.add_one_le_exp (1e5 : ℝ); linarith
  nlinarith [Real.exp_pos (-(3.7e6 : ℝ))]

/-! ## Elementary exponential anchors

Digit bounds on `e` (`Real.exp_one_gt_d9` / `Real.exp_one_lt_d9`) power all
the explicit `exp`/`log` evaluations of the certificate sections. -/

/-- `exp 15 < 3.3·10⁶` (so `log ξ ≥ 15` on every window). -/
theorem cert_exp_fifteen_lt : Real.exp (15 : ℝ) < 3.3e6 := by
  have heq : Real.exp (15 : ℝ) = Real.exp 1 ^ 15 := by
    rw [← Real.exp_nat_mul]; norm_num
  have h1 : Real.exp 1 ^ 15 ≤ (2.7182818286 : ℝ) ^ 15 :=
    pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 15
  have h2 : (2.7182818286 : ℝ) ^ 15 < 3.3e6 := by norm_num
  rw [heq]; linarith

/-- `exp 16 < 8 886 111` (so `log x ≥ 16` for `x ≥ 9.7·10⁶`). -/
theorem cert_exp_sixteen_lt : Real.exp (16 : ℝ) < 8886111 := by
  have heq : Real.exp (16 : ℝ) = Real.exp 1 ^ 16 := by
    rw [← Real.exp_nat_mul]; norm_num
  have h1 : Real.exp 1 ^ 16 ≤ (2.7182818286 : ℝ) ^ 16 :=
    pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 16
  have h2 : (2.7182818286 : ℝ) ^ 16 < 8886111 := by norm_num
  rw [heq]; linarith

/-- `exp 16.18 > 10 632 948`: the sharp threshold-displacement anchor
(`log(log 2 + w) ≤ 16.18` on the low window). -/
theorem cert_exp_16_18_gt : (10632948 : ℝ) ≤ Real.exp (16.18 : ℝ) := by
  have hsplit : Real.exp (16 : ℝ) * Real.exp (0.18 : ℝ)
      = Real.exp (16.18 : ℝ) := by
    rw [← Real.exp_add]; norm_num
  have h16 : (8886110.5 : ℝ) ≤ Real.exp (16 : ℝ) := by
    have heq : Real.exp (16 : ℝ) = Real.exp 1 ^ 16 := by
      rw [← Real.exp_nat_mul]; norm_num
    have h1 : (2.7182818283 : ℝ) ^ 16 ≤ Real.exp 1 ^ 16 :=
      pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 16
    have h2 : (8886110.5 : ℝ) ≤ (2.7182818283 : ℝ) ^ 16 := by norm_num
    rw [heq]; linarith
  have h018 : (1.197172 : ℝ) ≤ Real.exp (0.18 : ℝ) := by
    have hb : ∑ i ∈ Finset.range 4, (0.18 : ℝ) ^ i / (i.factorial : ℝ)
        ≤ Real.exp 0.18 := Real.sum_le_exp_of_nonneg (by norm_num) 4
    have hnum : (1.197172 : ℝ)
        ≤ ∑ i ∈ Finset.range 4, (0.18 : ℝ) ^ i / (i.factorial : ℝ) := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero]
      norm_num
    linarith
  nlinarith [Real.exp_pos (16 : ℝ), Real.exp_pos (0.18 : ℝ)]

/-- `exp 16.6 > 15 417 774`: the harmonic-sum anchor of `cert_B_low_le`
(`log(K+1) ≤ 16.6` for `K = ⌊w/log 2⌋` on the low window). -/
theorem cert_exp_16_6_gt : (15417774 : ℝ) ≤ Real.exp (16.6 : ℝ) := by
  have hsplit : Real.exp (16 : ℝ) * Real.exp (0.6 : ℝ)
      = Real.exp (16.6 : ℝ) := by
    rw [← Real.exp_add]; norm_num
  have h16 : (8886110.5 : ℝ) ≤ Real.exp (16 : ℝ) := by
    have heq : Real.exp (16 : ℝ) = Real.exp 1 ^ 16 := by
      rw [← Real.exp_nat_mul]; norm_num
    have h1 : (2.7182818283 : ℝ) ^ 16 ≤ Real.exp 1 ^ 16 :=
      pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 16
    have h2 : (8886110.5 : ℝ) ≤ (2.7182818283 : ℝ) ^ 16 := by norm_num
    rw [heq]; linarith
  have h06 : (1.78 : ℝ) ≤ Real.exp (0.6 : ℝ) := by
    have := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 0.6 by norm_num)
    nlinarith
  nlinarith [Real.exp_pos (16 : ℝ), Real.exp_pos (0.6 : ℝ)]

/-- `log ξ ≥ 15` for `ξ ≥ 3.9·10⁶`. -/
theorem cert_log_ge_fifteen {ξ : ℝ} (hξ : (3.9e6 : ℝ) ≤ ξ) :
    (15 : ℝ) ≤ Real.log ξ := by
  have hξ0 : (0 : ℝ) < ξ := by linarith
  rw [Real.le_log_iff_exp_le hξ0]
  linarith [cert_exp_fifteen_lt]

/-- `log x ≥ 16` for `x ≥ 9.7·10⁶` (both breakpoint windows qualify). -/
theorem cert_log_ge_sixteen {x : ℝ} (hx : (9.7e6 : ℝ) ≤ x) :
    (16 : ℝ) ≤ Real.log x := by
  have hx0 : (0 : ℝ) < x := by linarith
  rw [Real.le_log_iff_exp_le hx0]
  linarith [cert_exp_sixteen_lt]

/-! ## The two input scales: `log N₀`, `log N₁`, `F`-enclosures, breakpoints -/

/-- **`log N₀ ∈ [17.9999, 18.0001]`** for `N₀ = 65 659 969 = ⌊e¹⁸⌋`
(the true value is `18 − 2.09·10⁻⁹`). -/
theorem cert_log_N0_bounds :
    (17.9999 : ℝ) ≤ Real.log 65659969 ∧ Real.log 65659969 ≤ 18.0001 := by
  have hpos : (0 : ℝ) < 65659969 := by norm_num
  have heq : Real.exp (18 : ℝ) = Real.exp 1 ^ 18 := by
    rw [← Real.exp_nat_mul]; norm_num
  have hlb : (65659969 : ℝ) ≤ Real.exp (18 : ℝ) := by
    have h1 : (2.7182818283 : ℝ) ^ 18 ≤ Real.exp 1 ^ 18 :=
      pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 18
    have h2 : (65659969 : ℝ) ≤ (2.7182818283 : ℝ) ^ 18 := by norm_num
    rw [heq]; linarith
  have hub : Real.exp (18 : ℝ) ≤ 65659970 := by
    have h1 : Real.exp 1 ^ 18 ≤ (2.7182818286 : ℝ) ^ 18 :=
      pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 18
    have h2 : (2.7182818286 : ℝ) ^ 18 ≤ 65659970 := by norm_num
    rw [heq]; linarith
  constructor
  · rw [Real.le_log_iff_exp_le hpos]
    have hsplit : Real.exp (17.9999 : ℝ) * Real.exp (0.0001 : ℝ)
        = Real.exp (18 : ℝ) := by
      rw [← Real.exp_add]; norm_num
    have h1 : (1.0001 : ℝ) ≤ Real.exp (0.0001 : ℝ) := by
      have := Real.add_one_le_exp (0.0001 : ℝ); linarith
    have h2 : Real.exp (17.9999 : ℝ) * 1.0001
        ≤ Real.exp (17.9999 : ℝ) * Real.exp (0.0001 : ℝ) :=
      mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    linarith [hsplit ▸ h2]
  · rw [Real.log_le_iff_le_exp hpos]
    have hsplit : Real.exp (18 : ℝ) * Real.exp (0.0001 : ℝ)
        = Real.exp (18.0001 : ℝ) := by
      rw [← Real.exp_add]; norm_num
    have h1 : (1 : ℝ) ≤ Real.exp (0.0001 : ℝ) := by
      have := Real.add_one_le_exp (0.0001 : ℝ); linarith
    nlinarith [Real.exp_pos (18 : ℝ)]

/-- **`log N₁ ∈ [64.99, 65.01]`** for
`N₁ = 16 948 892 444 103 337 141 417 836 114 = ⌊e⁶⁵⌋`. -/
theorem cert_log_N1_bounds :
    (64.99 : ℝ) ≤ Real.log 16948892444103337141417836114 ∧
      Real.log 16948892444103337141417836114 ≤ 65.01 := by
  have hpos : (0 : ℝ) < 16948892444103337141417836114 := by norm_num
  have heq : Real.exp (65 : ℝ) = Real.exp 1 ^ 65 := by
    rw [← Real.exp_nat_mul]; norm_num
  have hlb : (1.6948e28 : ℝ) ≤ Real.exp (65 : ℝ) := by
    have h1 : (2.7182818283 : ℝ) ^ 65 ≤ Real.exp 1 ^ 65 :=
      pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 65
    have h2 : (1.6948e28 : ℝ) ≤ (2.7182818283 : ℝ) ^ 65 := by norm_num
    rw [heq]; linarith
  have hub : Real.exp (65 : ℝ) ≤ 1.695e28 := by
    have h1 : Real.exp 1 ^ 65 ≤ (2.7182818286 : ℝ) ^ 65 :=
      pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 65
    have h2 : (2.7182818286 : ℝ) ^ 65 ≤ 1.695e28 := by norm_num
    rw [heq]; linarith
  have h001 : (1.01 : ℝ) ≤ Real.exp (0.01 : ℝ) := by
    have := Real.add_one_le_exp (0.01 : ℝ); linarith
  constructor
  · rw [Real.le_log_iff_exp_le hpos]
    have hsplit : Real.exp (64.99 : ℝ) * Real.exp (0.01 : ℝ)
        = Real.exp (65 : ℝ) := by
      rw [← Real.exp_add]; norm_num
    have h2 : Real.exp (64.99 : ℝ) * 1.01
        ≤ Real.exp (64.99 : ℝ) * Real.exp (0.01 : ℝ) :=
      mul_le_mul_of_nonneg_left h001 (Real.exp_pos _).le
    linarith [hsplit ▸ h2]
  · rw [Real.log_le_iff_le_exp hpos]
    have hsplit : Real.exp (65 : ℝ) * Real.exp (0.01 : ℝ)
        = Real.exp (65.01 : ℝ) := by
      rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos (65 : ℝ)]

/-- The widened low `F`-enclosure `2.787 ≤ F(N₀) ≤ 2.792` consumed by the
window lemmas (weakening of the certified `eq:low-F`). -/
theorem cert_F_N0_bounds :
    (2.787 : ℝ) ≤ F 65659969 ∧ F 65659969 ≤ 2.792 :=
  ⟨by linarith [lowFiniteInput.1], by linarith [lowFiniteInput.2]⟩

set_option maxHeartbeats 400000 in
/-- The a-priori high `F`-enclosure `3.2411 < F(N₁) < 46` (paper:
`F(N₁) ≤ (log N₁)·log 2 < 65·log 2 < 46`, from `S(N) ≤ 2^N`). -/
theorem cert_F_N1_bounds :
    (3.2411 : ℝ) < F 16948892444103337141417836114 ∧
      F 16948892444103337141417836114 < 46 := by
  refine ⟨highFiniteInput, ?_⟩
  set N : ℕ := 16948892444103337141417836114 with hNdef
  have hNcast : ((N : ℕ) : ℝ) = (16948892444103337141417836114 : ℝ) := by
    rw [hNdef]; norm_num
  have hN0 : (0 : ℝ) < ((N : ℕ) : ℝ) := by rw [hNcast]; norm_num
  have hlogN_ub : Real.log ((N : ℕ) : ℝ) ≤ 65.01 := by
    rw [hNcast]; exact cert_log_N1_bounds.2
  have hlogN_lb : (0 : ℝ) ≤ Real.log ((N : ℕ) : ℝ) := by
    rw [hNcast]; linarith [cert_log_N1_bounds.1]
  have hS_pos : (0 : ℝ) < ((S N : ℕ) : ℝ) := by exact_mod_cast S_pos N
  have hS_ub : ((S N : ℕ) : ℝ) ≤ (2 : ℝ) ^ (N : ℕ) := by
    exact_mod_cast S_le_two_pow N
  have hlogS : Real.log ((S N : ℕ) : ℝ) ≤ ((N : ℕ) : ℝ) * Real.log 2 := by
    calc Real.log ((S N : ℕ) : ℝ) ≤ Real.log ((2 : ℝ) ^ (N : ℕ)) :=
          Real.log_le_log hS_pos hS_ub
      _ = ((N : ℕ) : ℝ) * Real.log 2 := by rw [Real.log_pow]
  have hstep : F N ≤ Real.log ((N : ℕ) : ℝ) * Real.log 2 := by
    rw [F]
    have h1 : Real.log ((N : ℕ) : ℝ) / ((N : ℕ) : ℝ) * Real.log ((S N : ℕ) : ℝ)
        ≤ Real.log ((N : ℕ) : ℝ) / ((N : ℕ) : ℝ)
          * (((N : ℕ) : ℝ) * Real.log 2) :=
      mul_le_mul_of_nonneg_left hlogS (div_nonneg hlogN_lb hN0.le)
    have h2 : Real.log ((N : ℕ) : ℝ) / ((N : ℕ) : ℝ)
          * (((N : ℕ) : ℝ) * Real.log 2)
        = Real.log ((N : ℕ) : ℝ) * Real.log 2 := by
      field_simp
    linarith [h2 ▸ h1]
  have hmul : Real.log ((N : ℕ) : ℝ) * Real.log 2 ≤ 65.01 * Real.log 2 :=
    mul_le_mul_of_nonneg_right hlogN_ub low_log2_pos.le
  have hfin : (65.01 : ℝ) * Real.log 2 < 46 := by
    nlinarith [Real.log_two_lt_d9]
  exact hstep.trans_lt (hmul.trans_lt hfin)

/-- **Breakpoint identity at the low input**: `g(N₀) = x(F(N₀))`
(paper: "at the actual value `f = F(N)` we have `x(f) = g(N)`"). -/
theorem cert_gN0_eq : g 65659969 = lowBreakpointX (F 65659969) := by
  have hcast : ((65659969 : ℕ) : ℝ) = (65659969 : ℝ) := by norm_num
  have hL0 : Real.log (65659969 : ℝ) ≠ 0 := by
    have := cert_log_N0_bounds.1; linarith
  have hN : (65659969 : ℝ) ≠ 0 := by norm_num
  rw [lowBreakpointX, F, g, hcast]
  rw [show (65659969 : ℝ)
        * (Real.log 65659969 / 65659969 * Real.log ((S 65659969 : ℕ) : ℝ))
        / Real.log 65659969
      = Real.log 65659969 / 65659969 * 65659969
        * Real.log ((S 65659969 : ℕ) : ℝ) / Real.log 65659969 from by ring,
    div_mul_cancel₀ _ hN, mul_comm (Real.log (65659969 : ℝ)),
    mul_div_assoc, div_self hL0, mul_one]

/-- **Breakpoint identity at the high input**: `g(N₁) = x(F(N₁))`. -/
theorem cert_gN1_eq :
    g 16948892444103337141417836114
      = highBreakpointX (F 16948892444103337141417836114) := by
  have hcast : ((16948892444103337141417836114 : ℕ) : ℝ)
      = (16948892444103337141417836114 : ℝ) := by norm_num
  have hL0 : Real.log (16948892444103337141417836114 : ℝ) ≠ 0 := by
    have := cert_log_N1_bounds.1; linarith
  have hN : (16948892444103337141417836114 : ℝ) ≠ 0 := by norm_num
  rw [highBreakpointX, F, g, hcast]
  rw [show (16948892444103337141417836114 : ℝ)
        * (Real.log 16948892444103337141417836114
            / 16948892444103337141417836114
          * Real.log ((S 16948892444103337141417836114 : ℕ) : ℝ))
        / Real.log 16948892444103337141417836114
      = Real.log 16948892444103337141417836114
          / 16948892444103337141417836114 * 16948892444103337141417836114
        * Real.log ((S 16948892444103337141417836114 : ℕ) : ℝ)
        / Real.log 16948892444103337141417836114 from by ring,
    div_mul_cancel₀ _ hN,
    mul_comm (Real.log (16948892444103337141417836114 : ℝ)),
    mul_div_assoc, div_self hL0, mul_one]

/-! ## Window containments (`eq:low-breakpoint-window`, high `x`-enclosure) -/

/-- **Low window containment** (`eq:low-breakpoint-window`, including the
`0.1%` backward-propagation enlargement): for every `f ∈ [2.787, 2.792]` the
enlarged chord window `[0.999·0.96·x(f), 1.001·1.04·x(f)]` lies inside the
certified interval `[9 725 449, 10 632 947]`. -/
theorem cert_low_window {f : ℝ} (h1 : (2.787 : ℝ) ≤ f) (h2 : f ≤ 2.792) :
    (9725449 : ℝ) ≤ 0.999 * (0.96 * lowBreakpointX f) ∧
      1.001 * (1.04 * lowBreakpointX f) ≤ 10632947 := by
  obtain ⟨hL1, hL2⟩ := cert_log_N0_bounds
  have hL0 : (0 : ℝ) < Real.log 65659969 := by linarith
  constructor
  · have hid : 0.999 * (0.96 * lowBreakpointX f)
        = 0.999 * (0.96 * (65659969 * f)) / Real.log 65659969 := by
      rw [lowBreakpointX]; ring
    rw [hid, le_div_iff₀ hL0]
    nlinarith
  · have hid : 1.001 * (1.04 * lowBreakpointX f)
        = 1.001 * (1.04 * (65659969 * f)) / Real.log 65659969 := by
      rw [lowBreakpointX]; ring
    rw [hid, div_le_iff₀ hL0]
    nlinarith

/-- Inner (unenlarged) form of `cert_low_window`. -/
theorem cert_low_window_inner {f : ℝ} (h1 : (2.787 : ℝ) ≤ f)
    (h2 : f ≤ 2.792) :
    (9725449 : ℝ) ≤ 0.96 * lowBreakpointX f ∧
      1.04 * lowBreakpointX f ≤ 10632947 := by
  obtain ⟨hlo, hhi⟩ := cert_low_window h1 h2
  have hx0 : 0 ≤ lowBreakpointX f := by nlinarith
  exact ⟨by nlinarith, by nlinarith⟩

/-- **High window containment**: for every `f ∈ [3.2411, 46]` the enlarged
chord window `[0.999²·x(f), 1.001²·x(f)]` lies inside `[8·10²⁶, 1.3·10²⁸]`. -/
theorem cert_high_window {f : ℝ} (h1 : (3.2411 : ℝ) ≤ f) (h2 : f ≤ 46) :
    (8e26 : ℝ) ≤ 0.999 * (0.999 * highBreakpointX f) ∧
      1.001 * (1.001 * highBreakpointX f) ≤ 1.3e28 := by
  obtain ⟨hL1, hL2⟩ := cert_log_N1_bounds
  have hL0 : (0 : ℝ) < Real.log 16948892444103337141417836114 := by linarith
  constructor
  · have hid : 0.999 * (0.999 * highBreakpointX f)
        = 0.999 * (0.999 * (16948892444103337141417836114 * f))
          / Real.log 16948892444103337141417836114 := by
      rw [highBreakpointX]; ring
    rw [hid, le_div_iff₀ hL0]
    nlinarith
  · have hid : 1.001 * (1.001 * highBreakpointX f)
        = 1.001 * (1.001 * (16948892444103337141417836114 * f))
          / Real.log 16948892444103337141417836114 := by
      rw [highBreakpointX]; ring
    rw [hid, div_le_iff₀ hL0]
    nlinarith

/-- Inner (unenlarged) form of `cert_high_window`. -/
theorem cert_high_window_inner {f : ℝ} (h1 : (3.2411 : ℝ) ≤ f)
    (h2 : f ≤ 46) :
    (8e26 : ℝ) ≤ 0.999 * highBreakpointX f ∧
      1.001 * highBreakpointX f ≤ 1.3e28 := by
  obtain ⟨hlo, hhi⟩ := cert_high_window h1 h2
  have hx0 : 0 ≤ highBreakpointX f := by nlinarith
  exact ⟨by nlinarith, by nlinarith⟩

/-! ## The breakpoint-coordinate calculus (`eq:q-breakpoint-coordinate`)

`iteratedLog 3` unfolds to `log ∘ log ∘ log`; on `ξ > 3.9·10⁶ > E₃(1)` the
whole chain is positive with phase `u = log₃ ξ > 1`, so both the core
`qCore = Q̃₄ ∘ log₃` and the limit `qLimit = Q₄* ∘ log₃` are twice
differentiable by the chain rule. -/

/-- `log₃ = log ∘ log ∘ log` (unconditionally, with Mathlib's junk values). -/
theorem cert_iteratedLog_three_eq (x : ℝ) :
    iteratedLog 3 x = Real.log (Real.log (Real.log x)) := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, iteratedLog_succ,
    show (2 : ℕ) = 1 + 1 from rfl, iteratedLog_succ,
    show (1 : ℕ) = 0 + 1 from rfl, iteratedLog_succ, iteratedLog_zero]

/-- `E 3 = exp ∘ exp ∘ exp` (unconditionally). -/
theorem cert_E_three_eq (v : ℝ) :
    E 3 v = Real.exp (Real.exp (Real.exp v)) := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, E_succ,
    show (2 : ℕ) = 1 + 1 from rfl, E_succ,
    show (1 : ℕ) = 0 + 1 from rfl, E_succ, E_zero]

/-- On `ξ ≥ 15 > e^e`'s base, `E₃` inverts `log₃` from the left. -/
theorem cert_E_three_iteratedLog {ξ : ℝ} (hξ : (15 : ℝ) ≤ ξ) :
    E 3 (iteratedLog 3 ξ) = ξ := by
  have hξ0 : (0 : ℝ) < ξ := by linarith
  have hy1 : (1 : ℝ) < Real.log ξ := by
    have he : Real.exp 1 < ξ := by
      have := Real.exp_one_lt_d9; linarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ < Real.log ξ := Real.log_lt_log (Real.exp_pos 1) he
  have hy0 : (0 : ℝ) < Real.log ξ := by linarith
  have hz0 : (0 : ℝ) < Real.log (Real.log ξ) := Real.log_pos hy1
  rw [cert_iteratedLog_three_eq, cert_E_three_eq, Real.exp_log hz0,
    Real.exp_log hy0, Real.exp_log hξ0]

/-- Phase positivity: `log₃ ξ > 1` for `ξ > 3.9·10⁶ > E₃(1)`. -/
theorem cert_one_lt_iteratedLog_three {ξ : ℝ} (hξ : (3.9e6 : ℝ) < ξ) :
    1 < iteratedLog 3 ξ := by
  have hE := cert_E_three_iteratedLog (by linarith : (15 : ℝ) ≤ ξ)
  by_contra h
  rw [not_lt] at h
  have hmono := E_mono 3 h
  rw [hE] at hmono
  linarith [E_three_one_lt]

/-- Positivity package on the working range: `log ξ ≥ 15` and
`log₂ ξ ≥ 1` for `ξ > 3.9·10⁶`. -/
theorem cert_logs_pos {ξ : ℝ} (hξ : (3.9e6 : ℝ) < ξ) :
    (15 : ℝ) ≤ Real.log ξ ∧ (1 : ℝ) ≤ Real.log (Real.log ξ) := by
  have hy := cert_log_ge_fifteen hξ.le
  refine ⟨hy, ?_⟩
  have hy0 : (0 : ℝ) < Real.log ξ := by linarith
  rw [Real.le_log_iff_exp_le hy0]
  have := Real.exp_one_lt_d9
  linarith

/-- The chain-rule derivative of `log₃`: `1/(ξ·log ξ·log₂ ξ)`. -/
noncomputable def cert_iteratedLogThreeDeriv (ξ : ℝ) : ℝ :=
  (ξ * Real.log ξ * Real.log (Real.log ξ))⁻¹

/-- The chain-rule second derivative of `log₃`:
`−(log ξ·log₂ ξ + log₂ ξ + 1)/(ξ·log ξ·log₂ ξ)²`. -/
noncomputable def cert_iteratedLogThreeDeriv2 (ξ : ℝ) : ℝ :=
  -((Real.log ξ * Real.log (Real.log ξ) + Real.log (Real.log ξ) + 1)
    / (ξ * Real.log ξ * Real.log (Real.log ξ)) ^ 2)

/-- On the working range, `15 ≤ log ξ·log₂ ξ` and
`1 ≤ ξ·log ξ·log₂ ξ` (denominator control for the chain rule). -/
theorem cert_logProduct_ge_one {ξ : ℝ} (hξ : (3.9e6 : ℝ) < ξ) :
    (15 : ℝ) ≤ Real.log ξ * Real.log (Real.log ξ) ∧
      (1 : ℝ) ≤ ξ * Real.log ξ * Real.log (Real.log ξ) := by
  obtain ⟨hy, hz⟩ := cert_logs_pos hξ
  have hyz : (15 : ℝ) ≤ Real.log ξ * Real.log (Real.log ξ) := by nlinarith
  refine ⟨hyz, ?_⟩
  nlinarith

/-- On the working range, `0 < (log₃)'(ξ) ≤ 1`. -/
theorem cert_iteratedLogThreeDeriv_bounds {ξ : ℝ} (hξ : (3.9e6 : ℝ) < ξ) :
    0 < cert_iteratedLogThreeDeriv ξ ∧ cert_iteratedLogThreeDeriv ξ ≤ 1 := by
  have hP := (cert_logProduct_ge_one hξ).2
  constructor
  · rw [cert_iteratedLogThreeDeriv]
    exact inv_pos.mpr (by linarith)
  · rw [cert_iteratedLogThreeDeriv]
    rw [inv_le_one_iff₀]
    right; linarith

/-- On the working range, `|(log₃)''(ξ)| ≤ 1`. -/
theorem cert_abs_iteratedLogThreeDeriv2_le_one {ξ : ℝ}
    (hξ : (3.9e6 : ℝ) < ξ) : |cert_iteratedLogThreeDeriv2 ξ| ≤ 1 := by
  obtain ⟨hy, hz⟩ := cert_logs_pos hξ
  obtain ⟨hyz, hP1⟩ := cert_logProduct_ge_one hξ
  have hnum : (0 : ℝ) ≤ Real.log ξ * Real.log (Real.log ξ)
      + Real.log (Real.log ξ) + 1 := by nlinarith
  have hnum3 : Real.log ξ * Real.log (Real.log ξ) + Real.log (Real.log ξ) + 1
      ≤ 3 * (Real.log ξ * Real.log (Real.log ξ)) := by nlinarith
  have h3P : 3 * (Real.log ξ * Real.log (Real.log ξ))
      ≤ ξ * Real.log ξ * Real.log (Real.log ξ) := by nlinarith
  have hPsq : ξ * Real.log ξ * Real.log (Real.log ξ)
      ≤ (ξ * Real.log ξ * Real.log (Real.log ξ)) ^ 2 := by nlinarith
  have hden : (0 : ℝ) < (ξ * Real.log ξ * Real.log (Real.log ξ)) ^ 2 := by
    nlinarith
  rw [cert_iteratedLogThreeDeriv2, abs_neg, abs_div, abs_of_nonneg hnum,
    abs_of_pos hden, div_le_one hden]
  linarith

/-- Chain-rule data for the inner map: `log₃` is differentiable on the
working range with derivative `cert_iteratedLogThreeDeriv`. -/
theorem cert_hasDerivAt_iteratedLog_three {ξ : ℝ} (hξ : (3.9e6 : ℝ) < ξ) :
    HasDerivAt (iteratedLog 3) (cert_iteratedLogThreeDeriv ξ) ξ := by
  obtain ⟨hy, hz⟩ := cert_logs_pos hξ
  have hξ0 : (0 : ℝ) < ξ := by linarith
  have hy0 : (0 : ℝ) < Real.log ξ := by linarith
  have hz0 : (0 : ℝ) < Real.log (Real.log ξ) := by linarith
  have h3 : HasDerivAt (fun v : ℝ => Real.log (Real.log (Real.log v)))
      (ξ⁻¹ / Real.log ξ / Real.log (Real.log ξ)) ξ :=
    ((Real.hasDerivAt_log hξ0.ne').log hy0.ne').log hz0.ne'
  have hfun : iteratedLog 3 = fun v : ℝ => Real.log (Real.log (Real.log v)) := by
    funext v; exact cert_iteratedLog_three_eq v
  rw [hfun]
  refine h3.congr_deriv ?_
  rw [cert_iteratedLogThreeDeriv]
  simp only [div_eq_mul_inv, mul_inv]

/-- The positive product `ξ·log ξ·log₂ ξ` is differentiable with derivative
`log ξ·log₂ ξ + log₂ ξ + 1`. -/
theorem cert_hasDerivAt_logProduct {ξ : ℝ} (hξ : (3.9e6 : ℝ) < ξ) :
    HasDerivAt (fun v : ℝ => v * Real.log v * Real.log (Real.log v))
      (Real.log ξ * Real.log (Real.log ξ) + Real.log (Real.log ξ) + 1) ξ := by
  obtain ⟨hy, hz⟩ := cert_logs_pos hξ
  have hξ0 : (0 : ℝ) < ξ := by linarith
  have hy0 : (0 : ℝ) < Real.log ξ := by linarith
  have h1 : HasDerivAt (fun v : ℝ => v * Real.log v) (Real.log ξ + 1) ξ := by
    refine ((hasDerivAt_id ξ).mul (Real.hasDerivAt_log hξ0.ne')).congr_deriv ?_
    simp only [id_eq, one_mul, mul_inv_cancel₀ hξ0.ne']
  have h2 : HasDerivAt (fun v : ℝ => Real.log (Real.log v))
      (ξ⁻¹ / Real.log ξ) ξ := (Real.hasDerivAt_log hξ0.ne').log hy0.ne'
  refine (h1.mul h2).congr_deriv ?_
  field_simp

/-- `cert_iteratedLogThreeDeriv` is itself differentiable on the working
range, with derivative `cert_iteratedLogThreeDeriv2`. -/
theorem cert_hasDerivAt_iteratedLogThreeDeriv {ξ : ℝ}
    (hξ : (3.9e6 : ℝ) < ξ) :
    HasDerivAt cert_iteratedLogThreeDeriv (cert_iteratedLogThreeDeriv2 ξ) ξ := by
  obtain ⟨hy, hz⟩ := cert_logs_pos hξ
  have hξ0 : (0 : ℝ) < ξ := by linarith
  have hy0 : (0 : ℝ) < Real.log ξ := by linarith
  have hz0 : (0 : ℝ) < Real.log (Real.log ξ) := by linarith
  have hPpos : (0 : ℝ) < ξ * Real.log ξ * Real.log (Real.log ξ) :=
    mul_pos (mul_pos hξ0 hy0) hz0
  have h := (cert_hasDerivAt_logProduct hξ).inv hPpos.ne'
  have hfun : cert_iteratedLogThreeDeriv
      = fun v : ℝ => (v * Real.log v * Real.log (Real.log v))⁻¹ := rfl
  rw [hfun]
  refine h.congr_deriv ?_
  rw [cert_iteratedLogThreeDeriv2]
  ring

/-! ## `qLimit`, `qCore`: first and second derivatives -/

/-- **The paper's `q_br`** (`eq:q-breakpoint-coordinate`): the *limit*
reference profile in the breakpoint coordinate, `q_br(ξ) = Q₄*(log₃ ξ)`. -/
noncomputable def qLimit (ξ : ℝ) : ℝ := QrefLimit 4 (iteratedLog 3 ξ)

/-- `qLimit` is differentiable on the working range, with derivative
`(Q₄*)'(log₃ ξ)·(log₃)'(ξ)`. -/
theorem cert_hasDerivAt_qLimit {ξ : ℝ} (hξ : (3.9e6 : ℝ) < ξ) :
    HasDerivAt qLimit
      (QrefLimitIterDeriv 1 4 (iteratedLog 3 ξ) * cert_iteratedLogThreeDeriv ξ)
      ξ := by
  have hu1 : 1 < iteratedLog 3 ξ := cert_one_lt_iteratedLog_three hξ
  have hQ : HasDerivAt (QrefLimit 4)
      (QrefLimitIterDeriv 1 4 (iteratedLog 3 ξ)) (iteratedLog 3 ξ) :=
    hasDerivAt_QrefLimit (by norm_num) hu1
  exact hQ.comp ξ (cert_hasDerivAt_iteratedLog_three hξ)

/-- `deriv qLimit` in closed form on the working range. -/
theorem cert_deriv_qLimit_eq {ξ : ℝ} (hξ : (3.9e6 : ℝ) < ξ) :
    deriv qLimit ξ
      = QrefLimitIterDeriv 1 4 (iteratedLog 3 ξ)
        * cert_iteratedLogThreeDeriv ξ :=
  (cert_hasDerivAt_qLimit hξ).deriv

/-- `qLimit` is differentiable with derivative `deriv qLimit` (the form the
chord lemma consumes). -/
theorem cert_hasDerivAt_qLimit_self {ξ : ℝ} (hξ : (3.9e6 : ℝ) < ξ) :
    HasDerivAt qLimit (deriv qLimit ξ) ξ := by
  rw [cert_deriv_qLimit_eq hξ]
  exact cert_hasDerivAt_qLimit hξ

/-- `deriv qLimit` is differentiable on the working range, with the
chain-rule second derivative. -/
theorem cert_hasDerivAt_deriv_qLimit {ξ : ℝ} (hξ : (3.9e6 : ℝ) < ξ) :
    HasDerivAt (deriv qLimit)
      (QrefLimitIterDeriv 2 4 (iteratedLog 3 ξ)
          * cert_iteratedLogThreeDeriv ξ ^ 2
        + QrefLimitIterDeriv 1 4 (iteratedLog 3 ξ)
          * cert_iteratedLogThreeDeriv2 ξ) ξ := by
  have hu1 : 1 < iteratedLog 3 ξ := cert_one_lt_iteratedLog_three hξ
  have h1 : HasDerivAt (fun v => QrefLimitIterDeriv 1 4 (iteratedLog 3 v))
      (QrefLimitIterDeriv 2 4 (iteratedLog 3 ξ)
        * cert_iteratedLogThreeDeriv ξ) ξ := by
    have hQ : HasDerivAt (QrefLimitIterDeriv 1 4)
        (QrefLimitIterDeriv 2 4 (iteratedLog 3 ξ)) (iteratedLog 3 ξ) :=
      hasDerivAt_QrefLimitIterDeriv (by norm_num) (by norm_num) hu1
    exact hQ.comp ξ (cert_hasDerivAt_iteratedLog_three hξ)
  have hfun : deriv qLimit =ᶠ[nhds ξ]
      fun v => QrefLimitIterDeriv 1 4 (iteratedLog 3 v)
        * cert_iteratedLogThreeDeriv v := by
    filter_upwards [Ioi_mem_nhds hξ] with v hv
    exact cert_deriv_qLimit_eq hv
  refine HasDerivAt.congr_of_eventuallyEq ?_ hfun
  refine (h1.mul (cert_hasDerivAt_iteratedLogThreeDeriv hξ)).congr_deriv ?_
  ring

/-- `deriv qLimit` is differentiable with derivative
`deriv (deriv qLimit)` (the form the chord lemma consumes). -/
theorem cert_hasDerivAt_deriv_qLimit_self {ξ : ℝ} (hξ : (3.9e6 : ℝ) < ξ) :
    HasDerivAt (deriv qLimit) (deriv (deriv qLimit) ξ) ξ := by
  rw [(cert_hasDerivAt_deriv_qLimit hξ).deriv]
  exact cert_hasDerivAt_deriv_qLimit hξ

/-- `deriv (deriv qLimit)` in closed form on the working range. -/
theorem cert_deriv2_qLimit_eq {ξ : ℝ} (hξ : (3.9e6 : ℝ) < ξ) :
    deriv (deriv qLimit) ξ
      = QrefLimitIterDeriv 2 4 (iteratedLog 3 ξ)
          * cert_iteratedLogThreeDeriv ξ ^ 2
        + QrefLimitIterDeriv 1 4 (iteratedLog 3 ξ)
          * cert_iteratedLogThreeDeriv2 ξ :=
  (cert_hasDerivAt_deriv_qLimit hξ).deriv

/-- The core profile `q̃ = qCore` is differentiable on the working range,
with derivative `Q̃₄'(log₃ ξ)·(log₃)'(ξ)`. -/
theorem cert_hasDerivAt_qCore {ξ : ℝ} (hξ : (3.9e6 : ℝ) < ξ) :
    HasDerivAt qCore
      (deriv QrefCore4 (iteratedLog 3 ξ) * cert_iteratedLogThreeDeriv ξ)
      ξ := by
  have hu1 : 1 < iteratedLog 3 ξ := cert_one_lt_iteratedLog_three hξ
  have hu0 : (0 : ℝ) < iteratedLog 3 ξ := by linarith
  have hev : HasDerivAt (evalComb QrefCore4Comb)
      (evalComb (derivComb QrefCore4Comb) (iteratedLog 3 ξ))
      (iteratedLog 3 ξ) := hasDerivAt_evalComb hu0 _
  have hQ : HasDerivAt QrefCore4
      (evalComb (derivComb QrefCore4Comb) (iteratedLog 3 ξ))
      (iteratedLog 3 ξ) := by
    refine HasDerivAt.congr_of_eventuallyEq hev ?_
    filter_upwards [Ioi_mem_nhds hu0] with v hv
    exact QrefCore4_eq_evalComb hv
  have h : HasDerivAt qCore
      (evalComb (derivComb QrefCore4Comb) (iteratedLog 3 ξ)
        * cert_iteratedLogThreeDeriv ξ) ξ :=
    hQ.comp ξ (cert_hasDerivAt_iteratedLog_three hξ)
  rw [deriv_QrefCore4_eq hu0]
  exact h

/-- `deriv qCore` in closed form on the working range. -/
theorem cert_deriv_qCore_eq {ξ : ℝ} (hξ : (3.9e6 : ℝ) < ξ) :
    deriv qCore ξ
      = deriv QrefCore4 (iteratedLog 3 ξ) * cert_iteratedLogThreeDeriv ξ :=
  (cert_hasDerivAt_qCore hξ).deriv

/-- `deriv qCore` is differentiable on the working range, with the
chain-rule second derivative. -/
theorem cert_hasDerivAt_deriv_qCore {ξ : ℝ} (hξ : (3.9e6 : ℝ) < ξ) :
    HasDerivAt (deriv qCore)
      (deriv (deriv QrefCore4) (iteratedLog 3 ξ)
          * cert_iteratedLogThreeDeriv ξ ^ 2
        + deriv QrefCore4 (iteratedLog 3 ξ)
          * cert_iteratedLogThreeDeriv2 ξ) ξ := by
  have hu1 : 1 < iteratedLog 3 ξ := cert_one_lt_iteratedLog_three hξ
  have hu0 : (0 : ℝ) < iteratedLog 3 ξ := by linarith
  have h1 : HasDerivAt
      (fun v => evalComb (derivComb QrefCore4Comb) (iteratedLog 3 v))
      (evalComb (derivComb (derivComb QrefCore4Comb)) (iteratedLog 3 ξ)
        * cert_iteratedLogThreeDeriv ξ) ξ :=
    HasDerivAt.comp ξ (hasDerivAt_evalComb hu0 _)
      (cert_hasDerivAt_iteratedLog_three hξ)
  have hfun : deriv qCore =ᶠ[nhds ξ]
      fun v => evalComb (derivComb QrefCore4Comb) (iteratedLog 3 v)
        * cert_iteratedLogThreeDeriv v := by
    filter_upwards [Ioi_mem_nhds hξ] with v hv
    have hv0 : (0 : ℝ) < iteratedLog 3 v := by
      linarith [cert_one_lt_iteratedLog_three hv]
    rw [cert_deriv_qCore_eq hv, deriv_QrefCore4_eq hv0]
  refine HasDerivAt.congr_of_eventuallyEq ?_ hfun
  refine (h1.mul (cert_hasDerivAt_iteratedLogThreeDeriv hξ)).congr_deriv ?_
  have hd2 : evalComb (derivComb (derivComb QrefCore4Comb)) (iteratedLog 3 ξ)
      = deriv (deriv QrefCore4) (iteratedLog 3 ξ) := by
    rw [deriv2_QrefCore4_eq hu0,
      show derivComb^[2] QrefCore4Comb = derivComb (derivComb QrefCore4Comb)
        from by
          rw [show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_succ_apply',
            Function.iterate_one]]
  have hd1 : evalComb (derivComb QrefCore4Comb) (iteratedLog 3 ξ)
      = deriv QrefCore4 (iteratedLog 3 ξ) := (deriv_QrefCore4_eq hu0).symm
  rw [hd1, hd2]
  ring

/-- `deriv qCore` is differentiable with derivative `deriv (deriv qCore)`. -/
theorem cert_hasDerivAt_deriv_qCore_self {ξ : ℝ} (hξ : (3.9e6 : ℝ) < ξ) :
    HasDerivAt (deriv qCore) (deriv (deriv qCore) ξ) ξ := by
  rw [(cert_hasDerivAt_deriv_qCore hξ).deriv]
  exact cert_hasDerivAt_deriv_qCore hξ

/-- `deriv (deriv qCore)` in closed form on the working range. -/
theorem cert_deriv2_qCore_eq {ξ : ℝ} (hξ : (3.9e6 : ℝ) < ξ) :
    deriv (deriv qCore) ξ
      = deriv (deriv QrefCore4) (iteratedLog 3 ξ)
          * cert_iteratedLogThreeDeriv ξ ^ 2
        + deriv QrefCore4 (iteratedLog 3 ξ)
          * cert_iteratedLogThreeDeriv2 ξ :=
  (cert_hasDerivAt_deriv_qCore hξ).deriv

/-! ## The exact slope identity (`eq:q-slope`) -/

/-- **`eq:q-slope` for the limit**: `ξ·q'(ξ) = Q₃*(log₃ ξ)/log ξ` on the
working range (via `Q₃* = (Q₄*)'/a₃` and `a₃(u) = E₁(u) = log₂ ξ`). -/
theorem cert_qLimit_slope {ξ : ℝ} (hξ : (3.9e6 : ℝ) < ξ) :
    ξ * deriv qLimit ξ = QrefLimit3 (iteratedLog 3 ξ) / Real.log ξ := by
  obtain ⟨hy, hz⟩ := cert_logs_pos hξ
  have hξ0 : (0 : ℝ) < ξ := by linarith
  have hy0 : (0 : ℝ) < Real.log ξ := by linarith
  have hz0 : (0 : ℝ) < Real.log (Real.log ξ) := by linarith
  have hE1 : E 1 (iteratedLog 3 ξ) = Real.log (Real.log ξ) := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, E_succ, E_zero,
      cert_iteratedLog_three_eq, Real.exp_log hz0]
  rw [cert_deriv_qLimit_eq hξ, QrefLimit3, a_three, hE1,
    cert_iteratedLogThreeDeriv]
  field_simp

/-- **`eq:q-slope` for the core**: `ξ·q̃'(ξ) = Q̃₃(log₃ ξ)/log ξ` on the
working range. -/
theorem cert_qCore_slope {ξ : ℝ} (hξ : (3.9e6 : ℝ) < ξ) :
    ξ * deriv qCore ξ = QrefCore3 (iteratedLog 3 ξ) / Real.log ξ := by
  obtain ⟨hy, hz⟩ := cert_logs_pos hξ
  have hξ0 : (0 : ℝ) < ξ := by linarith
  have hy0 : (0 : ℝ) < Real.log ξ := by linarith
  have hz0 : (0 : ℝ) < Real.log (Real.log ξ) := by linarith
  have hE1 : E 1 (iteratedLog 3 ξ) = Real.log (Real.log ξ) := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, E_succ, E_zero,
      cert_iteratedLog_three_eq, Real.exp_log hz0]
  rw [cert_deriv_qCore_eq hξ, QrefCore3, Lop, a_three, hE1,
    cert_iteratedLogThreeDeriv]
  field_simp

/-! ## `R7-tail` at the `ξ`-level: `q_br` vs `q̃` derivatives -/

/-- First-derivative tail at the `ξ`-level:
`|q'(ξ) − q̃'(ξ)| ≤ exp(−3.7·10⁶)` on the working range. -/
theorem cert_abs_deriv_qLimit_sub_qCore_le {ξ : ℝ} (hξ : (3.9e6 : ℝ) < ξ) :
    |deriv qLimit ξ - deriv qCore ξ| ≤ Real.exp (-(3.7e6 : ℝ)) := by
  have hu1 : 1 < iteratedLog 3 ξ := cert_one_lt_iteratedLog_three hξ
  obtain ⟨hL0, hL1⟩ := cert_iteratedLogThreeDeriv_bounds hξ
  have htail := abs_QrefLimitIterDeriv_one_four_sub_deriv_core_le hu1.le
  rw [cert_deriv_qLimit_eq hξ, cert_deriv_qCore_eq hξ, ← sub_mul, abs_mul,
    abs_of_pos hL0]
  calc |QrefLimitIterDeriv 1 4 (iteratedLog 3 ξ)
        - deriv QrefCore4 (iteratedLog 3 ξ)| * cert_iteratedLogThreeDeriv ξ
      ≤ Real.exp (-(3.7e6 : ℝ)) * 1 := by
        apply mul_le_mul htail hL1 hL0.le (Real.exp_pos _).le
    _ = Real.exp (-(3.7e6 : ℝ)) := mul_one _

/-- Second-derivative tail at the `ξ`-level:
`|q''(ξ) − q̃''(ξ)| ≤ exp(−3.6·10⁶)` on the working range (two `u`-level
tails, each times a chain-rule factor of size `≤ 1`). -/
theorem cert_abs_deriv2_qLimit_sub_qCore_le {ξ : ℝ} (hξ : (3.9e6 : ℝ) < ξ) :
    |deriv (deriv qLimit) ξ - deriv (deriv qCore) ξ|
      ≤ Real.exp (-(3.6e6 : ℝ)) := by
  have hu1 : 1 < iteratedLog 3 ξ := cert_one_lt_iteratedLog_three hξ
  obtain ⟨hL0, hL1⟩ := cert_iteratedLogThreeDeriv_bounds hξ
  have hL2 := cert_abs_iteratedLogThreeDeriv2_le_one hξ
  have ht1 := abs_QrefLimitIterDeriv_one_four_sub_deriv_core_le hu1.le
  have ht2 := abs_QrefLimitIterDeriv_two_four_sub_deriv2_core_le hu1.le
  have hid : deriv (deriv qLimit) ξ - deriv (deriv qCore) ξ
      = (QrefLimitIterDeriv 2 4 (iteratedLog 3 ξ)
          - deriv (deriv QrefCore4) (iteratedLog 3 ξ))
          * cert_iteratedLogThreeDeriv ξ ^ 2
        + (QrefLimitIterDeriv 1 4 (iteratedLog 3 ξ)
          - deriv QrefCore4 (iteratedLog 3 ξ))
          * cert_iteratedLogThreeDeriv2 ξ := by
    rw [cert_deriv2_qLimit_eq hξ, cert_deriv2_qCore_eq hξ]
    ring
  rw [hid]
  have hsq : cert_iteratedLogThreeDeriv ξ ^ 2 ≤ 1 := by nlinarith
  have hsq0 : (0 : ℝ) ≤ cert_iteratedLogThreeDeriv ξ ^ 2 := sq_nonneg _
  have hterm1 : |(QrefLimitIterDeriv 2 4 (iteratedLog 3 ξ)
        - deriv (deriv QrefCore4) (iteratedLog 3 ξ))
        * cert_iteratedLogThreeDeriv ξ ^ 2| ≤ Real.exp (-(3.7e6 : ℝ)) := by
    rw [abs_mul, abs_of_nonneg hsq0]
    calc |QrefLimitIterDeriv 2 4 (iteratedLog 3 ξ)
          - deriv (deriv QrefCore4) (iteratedLog 3 ξ)|
          * cert_iteratedLogThreeDeriv ξ ^ 2
        ≤ Real.exp (-(3.7e6 : ℝ)) * 1 :=
          mul_le_mul ht2 hsq hsq0 (Real.exp_pos _).le
      _ = Real.exp (-(3.7e6 : ℝ)) := mul_one _
  have hterm2 : |(QrefLimitIterDeriv 1 4 (iteratedLog 3 ξ)
        - deriv QrefCore4 (iteratedLog 3 ξ))
        * cert_iteratedLogThreeDeriv2 ξ| ≤ Real.exp (-(3.7e6 : ℝ)) := by
    rw [abs_mul]
    calc |QrefLimitIterDeriv 1 4 (iteratedLog 3 ξ)
          - deriv QrefCore4 (iteratedLog 3 ξ)|
          * |cert_iteratedLogThreeDeriv2 ξ|
        ≤ Real.exp (-(3.7e6 : ℝ)) * 1 :=
          mul_le_mul ht1 hL2 (abs_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (-(3.7e6 : ℝ)) := mul_one _
  calc |(QrefLimitIterDeriv 2 4 (iteratedLog 3 ξ)
        - deriv (deriv QrefCore4) (iteratedLog 3 ξ))
        * cert_iteratedLogThreeDeriv ξ ^ 2
      + (QrefLimitIterDeriv 1 4 (iteratedLog 3 ξ)
        - deriv QrefCore4 (iteratedLog 3 ξ))
        * cert_iteratedLogThreeDeriv2 ξ|
      ≤ |(QrefLimitIterDeriv 2 4 (iteratedLog 3 ξ)
          - deriv (deriv QrefCore4) (iteratedLog 3 ξ))
          * cert_iteratedLogThreeDeriv ξ ^ 2|
        + |(QrefLimitIterDeriv 1 4 (iteratedLog 3 ξ)
          - deriv QrefCore4 (iteratedLog 3 ξ))
          * cert_iteratedLogThreeDeriv2 ξ| := abs_add_le _ _
    _ ≤ 2 * Real.exp (-(3.7e6 : ℝ)) := by linarith
    _ ≤ Real.exp (-(3.6e6 : ℝ)) := cert_two_exp_le

/-! ## The low `ρ₄` ledger (`comp:low`, eq. `threshold-displacement`)

Mirrors `high_rho_abs_lt` on the low window with the paper's numeric budget:
`z − w < 17.6` from the elementary threshold bracket, `𝓑(w) ≤ 12.3` from the
harmonic split at `⌊w/log 2⌋`, `|𝓡(z)| < 1.2·10⁻⁵` from
`lem:explicit-low-averaging` at `z`, giving
`|ρ(w)| < 1.2·10⁻⁵ + 1.26·10⁻⁶ + 2.23·10⁻⁵ + 1.1·10⁻⁷ < 3.6·10⁻⁵`. -/

/-- **The elementary count-function bound on the low window**:
`𝓑(w) ≤ 12.3` for `w ∈ [9 725 449, 10 632 947]` (paper: the split
`𝓑(w) ≤ log 2·∑_{m ≤ w/log 2} 1/(m+1) + w/(⌊w/log 2⌋+1) < 12.57`; the
harmonic sum is `≤ log(K+1) ≤ 16.6`, so `𝓑(w) ≤ log 2·17.6 < 12.3`). -/
theorem cert_B_low_le {w : ℝ} (h1 : (9725449 : ℝ) ≤ w)
    (h2 : w ≤ 10632947) : B w ≤ 12.3 := by
  have hw0 : (0 : ℝ) < w := by linarith
  have hK1 : 1 ≤ ⌊w / Real.log 2⌋₊ := by
    apply Nat.le_floor
    rw [le_div_iff₀ low_log2_pos]
    push_cast
    nlinarith [Real.log_two_lt_d9]
  have hKle : ((⌊w / Real.log 2⌋₊ : ℕ) : ℝ) ≤ w / Real.log 2 :=
    Nat.floor_le (by positivity)
  have hKgt : w / Real.log 2 < ((⌊w / Real.log 2⌋₊ : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hBle := low_B_le_partial_add_tail (X := w) ⌊w / Real.log 2⌋₊
  -- each head term is at most `log 2/(m+1)`
  have hterm : ∀ m ∈ Finset.Icc 1 ⌊w / Real.log 2⌋₊,
      min (g m) w / ((m : ℝ) * ((m : ℝ) + 1))
        ≤ Real.log 2 * (1 / ((m : ℝ) + 1)) := by
    intro m hm
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
    have hg : min (g m) w ≤ (m : ℝ) * Real.log 2 :=
      le_trans (min_le_left _ _) (g_le_mul_log_two m)
    calc min (g m) w / ((m : ℝ) * ((m : ℝ) + 1))
        ≤ (m : ℝ) * Real.log 2 / ((m : ℝ) * ((m : ℝ) + 1)) :=
          div_le_div_of_nonneg_right hg (by positivity)
      _ = Real.log 2 * (1 / ((m : ℝ) + 1)) := by
          field_simp
  -- the shifted harmonic sum: `∑_{m=1}^{K} 1/(m+1) ≤ log(K+1)`
  have hshift : ∑ m ∈ Finset.Icc 1 ⌊w / Real.log 2⌋₊, (1 : ℝ) / ((m : ℝ) + 1)
      = ∑ m ∈ Finset.Icc 2 (⌊w / Real.log 2⌋₊ + 1), (1 : ℝ) / (m : ℝ) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl,
      ← Finset.map_add_right_Icc 1 ⌊w / Real.log 2⌋₊ 1, Finset.sum_map]
    apply Finset.sum_congr rfl
    intro m _
    simp only [addRightEmbedding_apply]
    push_cast
    ring
  have hIoc : Finset.Icc 2 (⌊w / Real.log 2⌋₊ + 1)
      = Finset.Ioc 1 (⌊w / Real.log 2⌋₊ + 1) := by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hcons : ∑ m ∈ Finset.Icc 1 (⌊w / Real.log 2⌋₊ + 1), (1 : ℝ) / (m : ℝ)
      = 1 + ∑ m ∈ Finset.Ioc 1 (⌊w / Real.log 2⌋₊ + 1), (1 : ℝ) / (m : ℝ) := by
    rw [Finset.Icc_eq_cons_Ioc (by omega), Finset.sum_cons]
    norm_num
  have hharm := sum_one_div_le_log (⌊w / Real.log 2⌋₊ + 1)
  have hsum_le : ∑ m ∈ Finset.Icc 1 ⌊w / Real.log 2⌋₊, (1 : ℝ) / ((m : ℝ) + 1)
      ≤ Real.log ((⌊w / Real.log 2⌋₊ + 1 : ℕ) : ℝ) := by
    rw [hshift, hIoc]
    linarith
  -- `log(K+1) ≤ 16.6`
  have hK45 : ((⌊w / Real.log 2⌋₊ + 1 : ℕ) : ℝ) ≤ 15417774 := by
    push_cast
    have hlog2 : (1 : ℝ) ≤ 1.4427 * Real.log 2 := by
      nlinarith [Real.log_two_gt_d9]
    have hdiv : w / Real.log 2 ≤ 1.4427 * w := by
      rw [div_le_iff₀ low_log2_pos]
      nlinarith
    nlinarith
  have hlogK : Real.log ((⌊w / Real.log 2⌋₊ + 1 : ℕ) : ℝ) ≤ 16.6 := by
    have hKpos : (0 : ℝ) < ((⌊w / Real.log 2⌋₊ + 1 : ℕ) : ℝ) := by
      push_cast
      positivity
    rw [Real.log_le_iff_le_exp hKpos]
    linarith [cert_exp_16_6_gt]
  -- the tail is at most `log 2`
  have htail : w / (((⌊w / Real.log 2⌋₊ : ℕ) : ℝ) + 1) ≤ Real.log 2 := by
    rw [div_le_iff₀ (by positivity)]
    have h := (div_lt_iff₀ low_log2_pos).mp hKgt
    nlinarith
  -- assemble
  have hhead : ∑ m ∈ Finset.Icc 1 ⌊w / Real.log 2⌋₊,
      min (g m) w / ((m : ℝ) * ((m : ℝ) + 1)) ≤ Real.log 2 * 16.6 := by
    calc ∑ m ∈ Finset.Icc 1 ⌊w / Real.log 2⌋₊,
          min (g m) w / ((m : ℝ) * ((m : ℝ) + 1))
        ≤ ∑ m ∈ Finset.Icc 1 ⌊w / Real.log 2⌋₊,
            Real.log 2 * (1 / ((m : ℝ) + 1)) := Finset.sum_le_sum hterm
      _ = Real.log 2
          * ∑ m ∈ Finset.Icc 1 ⌊w / Real.log 2⌋₊, (1 : ℝ) / ((m : ℝ) + 1) := by
          rw [← Finset.mul_sum]
      _ ≤ Real.log 2 * 16.6 := by
          apply mul_le_mul_of_nonneg_left _ low_log2_pos.le
          linarith
  calc B w ≤ (∑ m ∈ Finset.Icc 1 ⌊w / Real.log 2⌋₊,
        min (g m) w / ((m : ℝ) * ((m : ℝ) + 1)))
        + w / (((⌊w / Real.log 2⌋₊ : ℕ) : ℝ) + 1) := hBle
    _ ≤ Real.log 2 * 16.6 + Real.log 2 := by linarith
    _ = Real.log 2 * 17.6 := by ring
    _ ≤ 12.3 := by nlinarith [Real.log_two_lt_d9]

set_option maxHeartbeats 1000000 in
/-- **The low `ρ₄` ledger** (`comp:low` proof, the four-term budget for
eq. `threshold-displacement`): `|ρ(w)| < 3.6·10⁻⁵` on the enlarged low
window `[9 725 449, 10 632 947]`.  With `a = e^w`, `n = m_*(a)`,
`z = log n`: the elementary bracket `a/log 2 < n < 4a·log(2a)` places
`z ∈ [w, w + 17.6] ⊂ [9.7·10⁶, 1.07·10⁷]`, so `lem:explicit-low-averaging`
applies at `z`; the four displacement terms are then `< 1.2·10⁻⁵`,
`< 1.26·10⁻⁶`, `< 2.23·10⁻⁵`, `< 1.1·10⁻⁷`. -/
theorem cert_low_rho_ledger {w : ℝ} (h1 : (9725449 : ℝ) ≤ w)
    (h2 : w ≤ 10632947) : |rho w| < 3.6e-5 := by
  have hw0 : (0 : ℝ) < w := by linarith
  have ht0 : (0 : ℝ) < Real.exp w := Real.exp_pos w
  have ht9 : Real.exp (9 * 10 ^ 6 : ℝ) ≤ Real.exp w :=
    Real.exp_le_exp.mpr (by linarith)
  have hn_lb : Real.exp w / Real.log 2 < ((mStar (Real.exp w) : ℕ) : ℝ) :=
    mStar_lower (Real.exp w)
  have hn_ub : ((mStar (Real.exp w) : ℕ) : ℝ)
      < 4 * Real.exp w * Real.log (2 * Real.exp w) :=
    mStar_upper_explicit ht9
  have hn_pos : (0 : ℝ) < ((mStar (Real.exp w) : ℕ) : ℝ) :=
    lt_trans (by positivity) hn_lb
  have hnt : Real.exp w < ((mStar (Real.exp w) : ℕ) : ℝ) := by
    have hlog2lt1 : Real.log 2 < 1 := by nlinarith [Real.log_two_lt_d9]
    have hstep : Real.exp w < Real.exp w / Real.log 2 := by
      rw [lt_div_iff₀ low_log2_pos]
      nlinarith
    linarith
  have hwz : w ≤ Real.log ((mStar (Real.exp w) : ℕ) : ℝ) := by
    have h := Real.log_le_log ht0 hnt.le
    rwa [Real.log_exp] at h
  have hz0 : (0 : ℝ) < Real.log ((mStar (Real.exp w) : ℕ) : ℝ) := by linarith
  -- `z ≤ w + 17.6` via the sharp `log(log 2 + w) ≤ 16.18`
  have hz_ub : Real.log ((mStar (Real.exp w) : ℕ) : ℝ) ≤ w + 17.6 := by
    have hlog2t : Real.log (2 * Real.exp w) = Real.log 2 + w := by
      rw [Real.log_mul (by norm_num) ht0.ne', Real.log_exp]
    have hlog2tpos : (0 : ℝ) < Real.log (2 * Real.exp w) := by
      rw [hlog2t]
      linarith [low_log2_pos]
    have ha : Real.log ((mStar (Real.exp w) : ℕ) : ℝ)
        ≤ Real.log (4 * Real.exp w * Real.log (2 * Real.exp w)) :=
      Real.log_le_log hn_pos hn_ub.le
    have hb : Real.log (4 * Real.exp w * Real.log (2 * Real.exp w))
        = Real.log 4 + w + Real.log (Real.log (2 * Real.exp w)) := by
      rw [Real.log_mul (by positivity) hlog2tpos.ne',
        Real.log_mul (by norm_num) ht0.ne', Real.log_exp]
    have hc : Real.log (Real.log (2 * Real.exp w)) ≤ 16.18 := by
      rw [hlog2t, Real.log_le_iff_le_exp (by linarith [low_log2_pos])]
      have := Real.log_two_lt_d9
      linarith [cert_exp_16_18_gt]
    have hlog4 : Real.log 4 ≤ 1.3862943616 := by
      have h4 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
        norm_num
      linarith [Real.log_two_lt_d9]
    linarith [hb ▸ ha]
  -- the `z`-window is inside `lem:explicit-low-averaging`'s range
  have hz_low : (9.7e6 : ℝ) ≤ Real.log ((mStar (Real.exp w) : ℕ) : ℝ) := by
    linarith
  have hz_high : Real.log ((mStar (Real.exp w) : ℕ) : ℝ) ≤ 1.07e7 := by
    linarith
  -- `δ = g(n) − a ∈ (0, log 2]`
  have hdelta_pos : Real.exp w < g (mStar (Real.exp w)) := lt_g_mStar (Real.exp w)
  have hdelta_ub : g (mStar (Real.exp w)) ≤ Real.exp w + Real.log 2 := by
    have ha : g (mStar (Real.exp w) - 1) ≤ Real.exp w := g_mStar_sub_one_le ht0.le
    have hn1 : 1 ≤ mStar (Real.exp w) := mStar_pos ht0.le
    have hs' := S_succ_le_two_mul (mStar (Real.exp w) - 1)
    have hn1' : mStar (Real.exp w) - 1 + 1 = mStar (Real.exp w) := by omega
    rw [hn1'] at hs'
    have hSpos : (0 : ℝ) < ((S (mStar (Real.exp w) - 1) : ℕ) : ℝ) := by
      exact_mod_cast S_pos (mStar (Real.exp w) - 1)
    have hlogstep : Real.log ((S (mStar (Real.exp w)) : ℕ) : ℝ)
        ≤ Real.log (2 * ((S (mStar (Real.exp w) - 1) : ℕ) : ℝ)) := by
      apply Real.log_le_log (by exact_mod_cast S_pos (mStar (Real.exp w)))
      exact_mod_cast hs'
    rw [Real.log_mul (by norm_num) hSpos.ne'] at hlogstep
    have hg1 : g (mStar (Real.exp w))
        = Real.log ((S (mStar (Real.exp w)) : ℕ) : ℝ) := rfl
    have hg2 : g (mStar (Real.exp w) - 1)
        = Real.log ((S (mStar (Real.exp w) - 1) : ℕ) : ℝ) := rfl
    rw [hg1]
    rw [hg2] at ha
    linarith
  -- the displacement identity (eq. `threshold-displacement`)
  have hexpz : Real.exp (Real.log ((mStar (Real.exp w) : ℕ) : ℝ))
      = ((mStar (Real.exp w) : ℕ) : ℝ) := Real.exp_log hn_pos
  have hRz : averagingError (Real.log ((mStar (Real.exp w) : ℕ) : ℝ))
      = Real.log ((mStar (Real.exp w) : ℕ) : ℝ) / ((mStar (Real.exp w) : ℕ) : ℝ)
          * g (mStar (Real.exp w))
        - B (Real.log ((mStar (Real.exp w) : ℕ) : ℝ)) := by
    rw [averagingError, hexpz, FReal, Nat.floor_natCast]
  have hrho_id : rho w
      = w / Real.log ((mStar (Real.exp w) : ℕ) : ℝ)
          * averagingError (Real.log ((mStar (Real.exp w) : ℕ) : ℝ))
        + (w / Real.log ((mStar (Real.exp w) : ℕ) : ℝ)
            * B (Real.log ((mStar (Real.exp w) : ℕ) : ℝ)) - B w)
        - w * (g (mStar (Real.exp w)) - Real.exp w)
            / ((mStar (Real.exp w) : ℕ) : ℝ) := by
    rw [rho, hRz]
    field_simp
    ring
  -- piece 1: `(w/z)·|𝓡(z)| < 1.2·10⁻⁵`
  have hwz_le_one : w / Real.log ((mStar (Real.exp w) : ℕ) : ℝ) ≤ 1 := by
    rw [div_le_one hz0]
    exact hwz
  have hwz0 : (0 : ℝ) ≤ w / Real.log ((mStar (Real.exp w) : ℕ) : ℝ) := by
    positivity
  have hRz_bound := explicit_low_averaging hz_low hz_high
  have hpiece1 : w / Real.log ((mStar (Real.exp w) : ℕ) : ℝ)
      * |averagingError (Real.log ((mStar (Real.exp w) : ℕ) : ℝ))| < 1.2e-5 := by
    calc w / Real.log ((mStar (Real.exp w) : ℕ) : ℝ)
        * |averagingError (Real.log ((mStar (Real.exp w) : ℕ) : ℝ))|
        ≤ 1 * |averagingError (Real.log ((mStar (Real.exp w) : ℕ) : ℝ))| :=
          mul_le_mul_of_nonneg_right hwz_le_one (abs_nonneg _)
      _ = |averagingError (Real.log ((mStar (Real.exp w) : ℕ) : ℝ))| := one_mul _
      _ < 1.2e-5 := hRz_bound
  -- piece 2: `|(w/z)·𝓑(z) − 𝓑(w)| ≤ 1.26·10⁻⁶ + 2.23·10⁻⁵`
  have hBw_ub : B w ≤ 12.3 := cert_B_low_le h1 h2
  have hBw0 : 0 ≤ B w := high_B_nonneg hw0.le
  have hBmono : B w ≤ B (Real.log ((mStar (Real.exp w) : ℕ) : ℝ)) := B_mono hwz
  have hBz_sub : B (Real.log ((mStar (Real.exp w) : ℕ) : ℝ)) - B w
      ≤ 1.26e-6 := by
    have ha := B_sub_le_div_mStar hw0.le hwz
    have hm := mStar_lower w
    have hmw : (0 : ℝ) < w / Real.log 2 := by positivity
    have hb : (Real.log ((mStar (Real.exp w) : ℕ) : ℝ) - w) / (mStar w : ℝ)
        ≤ (Real.log ((mStar (Real.exp w) : ℕ) : ℝ) - w) / (w / Real.log 2) :=
      div_le_div_of_nonneg_left (by linarith) hmw hm.le
    have hc : (Real.log ((mStar (Real.exp w) : ℕ) : ℝ) - w) / (w / Real.log 2)
        = Real.log 2 * (Real.log ((mStar (Real.exp w) : ℕ) : ℝ) - w) / w := by
      field_simp
    have hd : Real.log 2 * (Real.log ((mStar (Real.exp w) : ℕ) : ℝ) - w) / w
        ≤ 1.26e-6 := by
      rw [div_le_iff₀ hw0]
      nlinarith [Real.log_two_lt_d9, low_log2_pos]
    linarith [hc ▸ hb]
  have hpiece2 : |w / Real.log ((mStar (Real.exp w) : ℕ) : ℝ)
        * B (Real.log ((mStar (Real.exp w) : ℕ) : ℝ)) - B w|
      ≤ 1.26e-6 + 2.23e-5 := by
    have hid : w / Real.log ((mStar (Real.exp w) : ℕ) : ℝ)
          * B (Real.log ((mStar (Real.exp w) : ℕ) : ℝ)) - B w
        = w / Real.log ((mStar (Real.exp w) : ℕ) : ℝ)
            * (B (Real.log ((mStar (Real.exp w) : ℕ) : ℝ)) - B w)
          - (1 - w / Real.log ((mStar (Real.exp w) : ℕ) : ℝ)) * B w := by
      ring
    have hBzx0 : 0 ≤ B (Real.log ((mStar (Real.exp w) : ℕ) : ℝ)) - B w := by
      linarith
    have hup : w / Real.log ((mStar (Real.exp w) : ℕ) : ℝ)
          * (B (Real.log ((mStar (Real.exp w) : ℕ) : ℝ)) - B w) ≤ 1.26e-6 := by
      calc w / Real.log ((mStar (Real.exp w) : ℕ) : ℝ)
          * (B (Real.log ((mStar (Real.exp w) : ℕ) : ℝ)) - B w)
          ≤ 1 * (B (Real.log ((mStar (Real.exp w) : ℕ) : ℝ)) - B w) :=
            mul_le_mul_of_nonneg_right hwz_le_one hBzx0
        _ = B (Real.log ((mStar (Real.exp w) : ℕ) : ℝ)) - B w := one_mul _
        _ ≤ 1.26e-6 := hBz_sub
    have hfrac : 1 - w / Real.log ((mStar (Real.exp w) : ℕ) : ℝ)
        ≤ 17.6 / 9725449 := by
      have hid2 : 1 - w / Real.log ((mStar (Real.exp w) : ℕ) : ℝ)
          = (Real.log ((mStar (Real.exp w) : ℕ) : ℝ) - w)
            / Real.log ((mStar (Real.exp w) : ℕ) : ℝ) := by
        field_simp
      rw [hid2]
      calc (Real.log ((mStar (Real.exp w) : ℕ) : ℝ) - w)
            / Real.log ((mStar (Real.exp w) : ℕ) : ℝ)
          ≤ (Real.log ((mStar (Real.exp w) : ℕ) : ℝ) - w) / w :=
            div_le_div_of_nonneg_left (by linarith) hw0 hwz
        _ ≤ 17.6 / 9725449 := by
            apply div_le_div₀ (by norm_num) (by linarith) (by norm_num) h1
    have hfrac0 : 0 ≤ 1 - w / Real.log ((mStar (Real.exp w) : ℕ) : ℝ) := by
      linarith
    have hdown : (1 - w / Real.log ((mStar (Real.exp w) : ℕ) : ℝ)) * B w
        ≤ 2.23e-5 := by
      calc (1 - w / Real.log ((mStar (Real.exp w) : ℕ) : ℝ)) * B w
          ≤ (17.6 / 9725449) * 12.3 :=
            mul_le_mul hfrac hBw_ub hBw0 (by norm_num)
        _ ≤ 2.23e-5 := by norm_num
    have hp1 : 0 ≤ w / Real.log ((mStar (Real.exp w) : ℕ) : ℝ)
        * (B (Real.log ((mStar (Real.exp w) : ℕ) : ℝ)) - B w) := by
      positivity
    have hp2 : 0 ≤ (1 - w / Real.log ((mStar (Real.exp w) : ℕ) : ℝ)) * B w := by
      positivity
    rw [hid, abs_le]
    constructor <;> linarith
  -- piece 3: the rounding term is at most `1/w ≤ 1.1·10⁻⁷`
  have hpiece3 : w * (g (mStar (Real.exp w)) - Real.exp w)
      / ((mStar (Real.exp w) : ℕ) : ℝ) ≤ 1.1e-7 := by
    have hdelta0 : 0 ≤ g (mStar (Real.exp w)) - Real.exp w := by linarith
    have ha : w * (g (mStar (Real.exp w)) - Real.exp w)
        / ((mStar (Real.exp w) : ℕ) : ℝ)
        ≤ w / ((mStar (Real.exp w) : ℕ) : ℝ) := by
      apply div_le_div_of_nonneg_right _ hn_pos.le
      have hd1 : g (mStar (Real.exp w)) - Real.exp w ≤ 1 := by
        nlinarith [Real.log_two_lt_d9]
      nlinarith
    have hb : w / ((mStar (Real.exp w) : ℕ) : ℝ) ≤ w / Real.exp w :=
      div_le_div_of_nonneg_left hw0.le ht0 hnt.le
    have hc : w / Real.exp w ≤ 1 / w := by
      rw [div_le_div_iff₀ ht0 hw0]
      have hq : w / 4 + 1 ≤ Real.exp (w / 4) := Real.add_one_le_exp _
      have hp4 : Real.exp (w / 4) ^ (4 : ℕ) = Real.exp w := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      have hw4 : (w / 4 : ℝ) ^ (4 : ℕ) ≤ Real.exp (w / 4) ^ (4 : ℕ) :=
        pow_le_pow_left₀ (by positivity) (by linarith) 4
      have h256 : (256 : ℝ) ≤ w ^ 2 := by nlinarith
      have hkey : 256 * w ^ 2 ≤ w ^ 2 * w ^ 2 :=
        mul_le_mul_of_nonneg_right h256 (sq_nonneg w)
      nlinarith [hp4 ▸ hw4]
    have hd : (1 : ℝ) / w ≤ 1.1e-7 := by
      rw [div_le_iff₀ hw0]
      nlinarith
    linarith
  have hpiece3_0 : 0 ≤ w * (g (mStar (Real.exp w)) - Real.exp w)
      / ((mStar (Real.exp w) : ℕ) : ℝ) := by
    have hdelta0 : 0 ≤ g (mStar (Real.exp w)) - Real.exp w := by linarith
    positivity
  -- assemble the ledger
  have habs3 : |rho w| ≤ w / Real.log ((mStar (Real.exp w) : ℕ) : ℝ)
        * |averagingError (Real.log ((mStar (Real.exp w) : ℕ) : ℝ))|
      + |w / Real.log ((mStar (Real.exp w) : ℕ) : ℝ)
          * B (Real.log ((mStar (Real.exp w) : ℕ) : ℝ)) - B w|
      + w * (g (mStar (Real.exp w)) - Real.exp w)
          / ((mStar (Real.exp w) : ℕ) : ℝ) := by
    rw [hrho_id]
    have hma : |w / Real.log ((mStar (Real.exp w) : ℕ) : ℝ)
        * averagingError (Real.log ((mStar (Real.exp w) : ℕ) : ℝ))|
        = w / Real.log ((mStar (Real.exp w) : ℕ) : ℝ)
          * |averagingError (Real.log ((mStar (Real.exp w) : ℕ) : ℝ))| := by
      rw [abs_mul, abs_of_nonneg hwz0]
    have t1 := abs_add_le
      (w / Real.log ((mStar (Real.exp w) : ℕ) : ℝ)
        * averagingError (Real.log ((mStar (Real.exp w) : ℕ) : ℝ)))
      (w / Real.log ((mStar (Real.exp w) : ℕ) : ℝ)
        * B (Real.log ((mStar (Real.exp w) : ℕ) : ℝ)) - B w)
    have t2 := abs_add_le
      (w / Real.log ((mStar (Real.exp w) : ℕ) : ℝ)
          * averagingError (Real.log ((mStar (Real.exp w) : ℕ) : ℝ))
        + (w / Real.log ((mStar (Real.exp w) : ℕ) : ℝ)
            * B (Real.log ((mStar (Real.exp w) : ℕ) : ℝ)) - B w))
      (-(w * (g (mStar (Real.exp w)) - Real.exp w)
          / ((mStar (Real.exp w) : ℕ) : ℝ)))
    rw [← sub_eq_add_neg, abs_neg, abs_of_nonneg hpiece3_0] at t2
    linarith [hma ▸ t1]
  linarith

/-- **The low `ρ₄` ledger in phase coordinates** (the form the
constant-phase-backward consumer uses): if `E₃(v)` lies in the enlarged low
window then `|ρ₄(v)| < 3.6·10⁻⁵`. -/
theorem cert_low_rhoDepth_ledger {v : ℝ} (h1 : (9725449 : ℝ) ≤ E 3 v)
    (h2 : E 3 v ≤ 10632947) : |rhoDepth 4 v| < 3.6e-5 := by
  have hEq : rhoDepth 4 v = rho (E 3 v) := by
    rw [rhoDepth]
  rw [hEq]
  exact cert_low_rho_ledger h1 h2

/-- Shared field identity for the curvature-bound certificates: the normalized
combination `κ·(a/D) + x·((b − a·p)/D²)` collapses over the common denominator
`D²`.  Both the low (`κ = 1.0601`) and high (`κ = 1.0201`) curvature proofs
instantiate it with `a = Q̃₄'`, `b = Q̃₄''`, `p = log ξ·log₂ ξ + log₂ ξ + 1`,
`x = ξ`, `D = ξ·log ξ·log₂ ξ`. -/
theorem curvatureComb (κ a b p x dd : ℝ) (hdd : dd ≠ 0) :
    κ * (a / dd) + x * ((b - a * p) / dd ^ 2)
      = (κ * a * dd + x * (b - a * p)) / dd ^ 2 := by
  field_simp

end Erdos320
