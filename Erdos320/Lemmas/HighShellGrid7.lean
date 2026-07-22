import Erdos320.Lemmas.HighShellTight

/-!
# High finite input: tight per-shell ledger, grid file 7/8

Tight per-shell contribution lemmas `shell_tight_115`..`shell_tight_134`, one per
prime shell `m = 115..134` at `N₁ = ⌊e⁶⁵⌋`, feeding the high finite input
(`comp:high`) — a proved theorem, not an axiom. The shells span collision regimes
`b = 1` (m = 115–120) and `b = 2` (m = 121–134).

Each invokes the reusable lower bound `shell_contribution_ge_tight`
(`HighShellTight.lean`) to prove
`Pₘ·(ℓ − pen) ≤ ∑_{p ∈ shellPrimes highN m} log σ(p, m)`, where `Pₘ` is the tight
Dusart prime-count floor, `ℓ` a `log(sL)` lower bound, `pen` the `b`-collision
penalty (`eq:high-collision-bound`), and `sL` a BGMS lower bound on `S m`. The
literals are discharged in place by `norm_num`/`native_decide` with the
`exp`-comparison log bounds (`log_ge_of` for `ℓ`, `log_le_of_real` for `pen`). The
eight grid files together cover the 154-shell ledger.
-/

namespace Erdos320

open Finset

set_option maxHeartbeats 4000000 in
/-- Shell `m = 115`, regime `b = 1`. -/
theorem shell_tight_115 :
    ((20537127576672026000430 : ℚ) : ℝ) * (((50 : ℝ) + 0.584954) - (((0 : ℕ) : ℝ) + 0.373723))
      ≤ ∑ p ∈ shellPrimes highN 115, Real.log (sigma p 115) := by
  apply shell_contribution_ge_tight 115 1 20537127576672026000430 (((50 : ℝ) + 0.584954)) ((((0 : ℕ) : ℝ) + 0.373723)) 9306072980415389368320
  · norm_num
  · norm_num
  · norm_num [highN]
  · norm_num [highN]
  · norm_num [highN]
  · norm_num [highN]
  · native_decide
  · norm_num [lbLoQt, logNatHi]
  · norm_num [laLoQt, logNatHi]
  · norm_num [lbUpQt, logNatLo]
  · norm_num
  · norm_num
  · norm_num [lbLoQt, laLoQt, lbUpQt, logNatHi, logNatLo, highN]
  · native_decide
  · norm_num
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.584954 : ℝ) by norm_num)
      (show (0.584954 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 9306072980415389368320 (by norm_num) 50 0.584954 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 0 0.373723 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.373723 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 116`, regime `b = 1`. -/
theorem shell_tight_116 :
    ((20184217967729971529550 : ℚ) : ℝ) * (((51 : ℝ) + 0.278101) - (((0 : ℕ) : ℝ) + 0.653426))
      ≤ ∑ p ∈ shellPrimes highN 116, Real.log (sigma p 116) := by
  apply shell_contribution_ge_tight 116 1 20184217967729971529550 (((51 : ℝ) + 0.278101)) ((((0 : ℕ) : ℝ) + 0.653426)) 18612145960830778736640
  · norm_num
  · norm_num
  · norm_num [highN]
  · norm_num [highN]
  · norm_num [highN]
  · norm_num [highN]
  · native_decide
  · norm_num [lbLoQt, logNatHi]
  · norm_num [laLoQt, logNatHi]
  · norm_num [lbUpQt, logNatLo]
  · norm_num
  · norm_num
  · norm_num [lbLoQt, laLoQt, lbUpQt, logNatHi, logNatLo, highN]
  · native_decide
  · norm_num
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.278101 : ℝ) by norm_num)
      (show (0.278101 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 18612145960830778736640 (by norm_num) 51 0.278101 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 0 0.653426 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.653426 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 117`, regime `b = 1`. -/
theorem shell_tight_117 :
    ((19840270657106603772103 : ℚ) : ℝ) * (((51 : ℝ) + 0.278101) - (((0 : ℕ) : ℝ) + 0.661708))
      ≤ ∑ p ∈ shellPrimes highN 117, Real.log (sigma p 117) := by
  apply shell_contribution_ge_tight 117 1 19840270657106603772103 (((51 : ℝ) + 0.278101)) ((((0 : ℕ) : ℝ) + 0.661708)) 18612145960830778736640
  · norm_num
  · norm_num
  · norm_num [highN]
  · norm_num [highN]
  · norm_num [highN]
  · norm_num [highN]
  · native_decide
  · norm_num [lbLoQt, logNatHi]
  · norm_num [laLoQt, logNatHi]
  · norm_num [lbUpQt, logNatLo]
  · norm_num
  · norm_num
  · norm_num [lbLoQt, laLoQt, lbUpQt, logNatHi, logNatLo, highN]
  · native_decide
  · norm_num
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.278101 : ℝ) by norm_num)
      (show (0.278101 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 18612145960830778736640 (by norm_num) 51 0.278101 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 0 0.661708 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.661708 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 118`, regime `b = 1`. -/
theorem shell_tight_118 :
    ((19504984981170076034151 : ℚ) : ℝ) * (((51 : ℝ) + 0.971248) - (((1 : ℕ) : ℝ) + 0.067621))
      ≤ ∑ p ∈ shellPrimes highN 118, Real.log (sigma p 118) := by
  apply shell_contribution_ge_tight 118 1 19504984981170076034151 (((51 : ℝ) + 0.971248)) ((((1 : ℕ) : ℝ) + 0.067621)) 37224291921661557473280
  · norm_num
  · norm_num
  · norm_num [highN]
  · norm_num [highN]
  · norm_num [highN]
  · norm_num [highN]
  · native_decide
  · norm_num [lbLoQt, logNatHi]
  · norm_num [laLoQt, logNatHi]
  · norm_num [lbUpQt, logNatLo]
  · norm_num
  · norm_num
  · norm_num [lbLoQt, laLoQt, lbUpQt, logNatHi, logNatLo, highN]
  · native_decide
  · norm_num
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.971248 : ℝ) by norm_num)
      (show (0.971248 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 37224291921661557473280 (by norm_num) 51 0.971248 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 1 0.067621 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.067621 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 119`, regime `b = 1`. -/
theorem shell_tight_119 :
    ((19178072693982302917334 : ℚ) : ℝ) * (((51 : ℝ) + 0.971248) - (((1 : ℕ) : ℝ) + 0.078744))
      ≤ ∑ p ∈ shellPrimes highN 119, Real.log (sigma p 119) := by
  apply shell_contribution_ge_tight 119 1 19178072693982302917334 (((51 : ℝ) + 0.971248)) ((((1 : ℕ) : ℝ) + 0.078744)) 37224291921661557473280
  · norm_num
  · norm_num
  · norm_num [highN]
  · norm_num [highN]
  · norm_num [highN]
  · norm_num [highN]
  · native_decide
  · norm_num [lbLoQt, logNatHi]
  · norm_num [laLoQt, logNatHi]
  · norm_num [lbUpQt, logNatLo]
  · norm_num
  · norm_num
  · norm_num [lbLoQt, laLoQt, lbUpQt, logNatHi, logNatLo, highN]
  · native_decide
  · norm_num
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.971248 : ℝ) by norm_num)
      (show (0.971248 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 37224291921661557473280 (by norm_num) 51 0.971248 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 1 0.078744 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.078744 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 120`, regime `b = 1`. -/
theorem shell_tight_120 :
    ((18859257449564762799769 : ℚ) : ℝ) * (((51 : ℝ) + 0.971248) - (((1 : ℕ) : ℝ) + 0.089839))
      ≤ ∑ p ∈ shellPrimes highN 120, Real.log (sigma p 120) := by
  apply shell_contribution_ge_tight 120 1 18859257449564762799769 (((51 : ℝ) + 0.971248)) ((((1 : ℕ) : ℝ) + 0.089839)) 37224291921661557473280
  · norm_num
  · norm_num
  · norm_num [highN]
  · norm_num [highN]
  · norm_num [highN]
  · norm_num [highN]
  · native_decide
  · norm_num [lbLoQt, logNatHi]
  · norm_num [laLoQt, logNatHi]
  · norm_num [lbUpQt, logNatLo]
  · norm_num
  · norm_num
  · norm_num [lbLoQt, laLoQt, lbUpQt, logNatHi, logNatLo, highN]
  · native_decide
  · norm_num
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.971248 : ℝ) by norm_num)
      (show (0.971248 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 37224291921661557473280 (by norm_num) 51 0.971248 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 1 0.089839 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.089839 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 121`, regime `b = 2`. -/
theorem shell_tight_121 :
    ((18548274492603876355665 : ℚ) : ℝ) * (((52 : ℝ) + 0.664395) - (((2 : ℕ) : ℝ) + 0.200281))
      ≤ ∑ p ∈ shellPrimes highN 121, Real.log (sigma p 121) := by
  apply shell_contribution_ge_tight 121 2 18548274492603876355665 (((52 : ℝ) + 0.664395)) ((((2 : ℕ) : ℝ) + 0.200281)) 74448583843323114946560
  · norm_num
  · norm_num
  · norm_num [highN]
  · norm_num [highN]
  · norm_num [highN]
  · norm_num [highN]
  · native_decide
  · norm_num [lbLoQt, logNatHi]
  · norm_num [laLoQt, logNatHi]
  · norm_num [lbUpQt, logNatLo]
  · norm_num
  · norm_num
  · norm_num [lbLoQt, laLoQt, lbUpQt, logNatHi, logNatLo, highN]
  · native_decide
  · norm_num
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.664395 : ℝ) by norm_num)
      (show (0.664395 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 74448583843323114946560 (by norm_num) 52 0.664395 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 2 0.200281 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.200281 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 122`, regime `b = 2`. -/
theorem shell_tight_122 :
    ((18244869388169072106839 : ℚ) : ℝ) * (((53 : ℝ) + 0.357542) - (((2 : ℕ) : ℝ) + 0.851983))
      ≤ ∑ p ∈ shellPrimes highN 122, Real.log (sigma p 122) := by
  apply shell_contribution_ge_tight 122 2 18244869388169072106839 (((53 : ℝ) + 0.357542)) ((((2 : ℕ) : ℝ) + 0.851983)) 148897167686646229893120
  · norm_num
  · norm_num
  · norm_num [highN]
  · norm_num [highN]
  · norm_num [highN]
  · norm_num [highN]
  · native_decide
  · norm_num [lbLoQt, logNatHi]
  · norm_num [laLoQt, logNatHi]
  · norm_num [lbUpQt, logNatLo]
  · norm_num
  · norm_num
  · norm_num [lbLoQt, laLoQt, lbUpQt, logNatHi, logNatLo, highN]
  · native_decide
  · norm_num
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.357542 : ℝ) by norm_num)
      (show (0.357542 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 148897167686646229893120 (by norm_num) 53 0.357542 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 2 0.851983 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.851983 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 123`, regime `b = 2`. -/
theorem shell_tight_123 :
    ((17948798193457782383824 : ℚ) : ℝ) * (((54 : ℝ) + 0.050690) - (((3 : ℕ) : ℝ) + 0.531719))
      ≤ ∑ p ∈ shellPrimes highN 123, Real.log (sigma p 123) := by
  apply shell_contribution_ge_tight 123 2 17948798193457782383824 (((54 : ℝ) + 0.050690)) ((((3 : ℕ) : ℝ) + 0.531719)) 297794335373292459786240
  · norm_num
  · norm_num
  · norm_num [highN]
  · norm_num [highN]
  · norm_num [highN]
  · norm_num [highN]
  · native_decide
  · norm_num [lbLoQt, logNatHi]
  · norm_num [laLoQt, logNatHi]
  · norm_num [lbUpQt, logNatLo]
  · norm_num
  · norm_num
  · norm_num [lbLoQt, laLoQt, lbUpQt, logNatHi, logNatLo, highN]
  · native_decide
  · norm_num
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.050690 : ℝ) by norm_num)
      (show (0.050690 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 297794335373292459786240 (by norm_num) 54 0.050690 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 3 0.531719 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.531719 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 124`, regime `b = 2`. -/
theorem shell_tight_124 :
    ((17659826652483026039928 : ℚ) : ℝ) * (((54 : ℝ) + 0.743837) - (((4 : ℕ) : ℝ) + 0.226122))
      ≤ ∑ p ∈ shellPrimes highN 124, Real.log (sigma p 124) := by
  apply shell_contribution_ge_tight 124 2 17659826652483026039928 (((54 : ℝ) + 0.743837)) ((((4 : ℕ) : ℝ) + 0.226122)) 595588670746584919572480
  · norm_num
  · norm_num
  · norm_num [highN]
  · norm_num [highN]
  · norm_num [highN]
  · norm_num [highN]
  · native_decide
  · norm_num [lbLoQt, logNatHi]
  · norm_num [laLoQt, logNatHi]
  · norm_num [lbUpQt, logNatLo]
  · norm_num
  · norm_num
  · norm_num [lbLoQt, laLoQt, lbUpQt, logNatHi, logNatLo, highN]
  · native_decide
  · norm_num
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.743837 : ℝ) by norm_num)
      (show (0.743837 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 595588670746584919572480 (by norm_num) 54 0.743837 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 4 0.226122 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.226122 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 125`, regime `b = 2`. -/
theorem shell_tight_125 :
    ((17377729825779089913825 : ℚ) : ℝ) * (((55 : ℝ) + 0.436984) - (((4 : ℕ) : ℝ) + 0.927924))
      ≤ ∑ p ∈ shellPrimes highN 125, Real.log (sigma p 125) := by
  apply shell_contribution_ge_tight 125 2 17377729825779089913825 (((55 : ℝ) + 0.436984)) ((((4 : ℕ) : ℝ) + 0.927924)) 1191177341493169839144960
  · norm_num
  · norm_num
  · norm_num [highN]
  · norm_num [highN]
  · norm_num [highN]
  · norm_num [highN]
  · native_decide
  · norm_num [lbLoQt, logNatHi]
  · norm_num [laLoQt, logNatHi]
  · norm_num [lbUpQt, logNatLo]
  · norm_num
  · norm_num
  · norm_num [lbLoQt, laLoQt, lbUpQt, logNatHi, logNatLo, highN]
  · native_decide
  · norm_num
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.436984 : ℝ) by norm_num)
      (show (0.436984 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 1191177341493169839144960 (by norm_num) 55 0.436984 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 4 0.927924 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.927924 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 126`, regime `b = 2`. -/
theorem shell_tight_126 :
    ((17102291418532200095974 : ℚ) : ℝ) * (((55 : ℝ) + 0.436984) - (((4 : ℕ) : ℝ) + 0.943786))
      ≤ ∑ p ∈ shellPrimes highN 126, Real.log (sigma p 126) := by
  apply shell_contribution_ge_tight 126 2 17102291418532200095974 (((55 : ℝ) + 0.436984)) ((((4 : ℕ) : ℝ) + 0.943786)) 1191177341493169839144960
  · norm_num
  · norm_num
  · norm_num [highN]
  · norm_num [highN]
  · norm_num [highN]
  · norm_num [highN]
  · native_decide
  · norm_num [lbLoQt, logNatHi]
  · norm_num [laLoQt, logNatHi]
  · norm_num [lbUpQt, logNatLo]
  · norm_num
  · norm_num
  · norm_num [lbLoQt, laLoQt, lbUpQt, logNatHi, logNatLo, highN]
  · native_decide
  · norm_num
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.436984 : ℝ) by norm_num)
      (show (0.436984 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 1191177341493169839144960 (by norm_num) 55 0.436984 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 4 0.943786 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.943786 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 127`, regime `b = 2`. -/
theorem shell_tight_127 :
    ((16833303969469618887775 : ℚ) : ℝ) * (((56 : ℝ) + 0.130131) - (((5 : ℕ) : ℝ) + 0.649160))
      ≤ ∑ p ∈ shellPrimes highN 127, Real.log (sigma p 127) := by
  apply shell_contribution_ge_tight 127 2 16833303969469618887775 (((56 : ℝ) + 0.130131)) ((((5 : ℕ) : ℝ) + 0.649160)) 2382354682986339678289920
  · norm_num
  · norm_num
  · norm_num [highN]
  · norm_num [highN]
  · norm_num [highN]
  · norm_num [highN]
  · native_decide
  · norm_num [lbLoQt, logNatHi]
  · norm_num [laLoQt, logNatHi]
  · norm_num [lbUpQt, logNatLo]
  · norm_num
  · norm_num
  · norm_num [lbLoQt, laLoQt, lbUpQt, logNatHi, logNatLo, highN]
  · native_decide
  · norm_num
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.130131 : ℝ) by norm_num)
      (show (0.130131 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 2382354682986339678289920 (by norm_num) 56 0.130131 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 5 0.649160 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.649160 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 128`, regime `b = 2`. -/
theorem shell_tight_128 :
    ((16570567468762563598019 : ℚ) : ℝ) * (((56 : ℝ) + 0.823278) - (((6 : ℕ) : ℝ) + 0.356249))
      ≤ ∑ p ∈ shellPrimes highN 128, Real.log (sigma p 128) := by
  apply shell_contribution_ge_tight 128 2 16570567468762563598019 (((56 : ℝ) + 0.823278)) ((((6 : ℕ) : ℝ) + 0.356249)) 4764709365972679356579840
  · norm_num
  · norm_num
  · norm_num [highN]
  · norm_num [highN]
  · norm_num [highN]
  · norm_num [highN]
  · native_decide
  · norm_num [lbLoQt, logNatHi]
  · norm_num [laLoQt, logNatHi]
  · norm_num [lbUpQt, logNatLo]
  · norm_num
  · norm_num
  · norm_num [lbLoQt, laLoQt, lbUpQt, logNatHi, logNatLo, highN]
  · native_decide
  · norm_num
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.823278 : ℝ) by norm_num)
      (show (0.823278 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 4764709365972679356579840 (by norm_num) 56 0.823278 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 6 0.356249 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.356249 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 129`, regime `b = 2`. -/
theorem shell_tight_129 :
    ((16313890357853818969854 : ℚ) : ℝ) * (((57 : ℝ) + 0.516425) - (((7 : ℕ) : ℝ) + 0.064125))
      ≤ ∑ p ∈ shellPrimes highN 129, Real.log (sigma p 129) := by
  apply shell_contribution_ge_tight 129 2 16313890357853818969854 (((57 : ℝ) + 0.516425)) ((((7 : ℕ) : ℝ) + 0.064125)) 9529418731945358713159680
  · norm_num
  · norm_num
  · norm_num [highN]
  · norm_num [highN]
  · norm_num [highN]
  · norm_num [highN]
  · native_decide
  · norm_num [lbLoQt, logNatHi]
  · norm_num [laLoQt, logNatHi]
  · norm_num [lbUpQt, logNatLo]
  · norm_num
  · norm_num
  · norm_num [lbLoQt, laLoQt, lbUpQt, logNatHi, logNatLo, highN]
  · native_decide
  · norm_num
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.516425 : ℝ) by norm_num)
      (show (0.516425 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 9529418731945358713159680 (by norm_num) 57 0.516425 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 7 0.064125 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.064125 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 130`, regime `b = 2`. -/
theorem shell_tight_130 :
    ((16063087543183786457692 : ℚ) : ℝ) * (((57 : ℝ) + 0.516425) - (((7 : ℕ) : ℝ) + 0.079605))
      ≤ ∑ p ∈ shellPrimes highN 130, Real.log (sigma p 130) := by
  apply shell_contribution_ge_tight 130 2 16063087543183786457692 (((57 : ℝ) + 0.516425)) ((((7 : ℕ) : ℝ) + 0.079605)) 9529418731945358713159680
  · norm_num
  · norm_num
  · norm_num [highN]
  · norm_num [highN]
  · norm_num [highN]
  · norm_num [highN]
  · native_decide
  · norm_num [lbLoQt, logNatHi]
  · norm_num [laLoQt, logNatHi]
  · norm_num [lbUpQt, logNatLo]
  · norm_num
  · norm_num
  · norm_num [lbLoQt, laLoQt, lbUpQt, logNatHi, logNatLo, highN]
  · native_decide
  · norm_num
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.516425 : ℝ) by norm_num)
      (show (0.516425 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 9529418731945358713159680 (by norm_num) 57 0.516425 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 7 0.079605 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.079605 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 131`, regime `b = 2`. -/
theorem shell_tight_131 :
    ((15817981496751024524769 : ℚ) : ℝ) * (((58 : ℝ) + 0.209573) - (((7 : ℕ) : ℝ) + 0.787701))
      ≤ ∑ p ∈ shellPrimes highN 131, Real.log (sigma p 131) := by
  apply shell_contribution_ge_tight 131 2 15817981496751024524769 (((58 : ℝ) + 0.209573)) ((((7 : ℕ) : ℝ) + 0.787701)) 19058837463890717426319360
  · norm_num
  · norm_num
  · norm_num [highN]
  · norm_num [highN]
  · norm_num [highN]
  · norm_num [highN]
  · native_decide
  · norm_num [lbLoQt, logNatHi]
  · norm_num [laLoQt, logNatHi]
  · norm_num [lbUpQt, logNatLo]
  · norm_num
  · norm_num
  · norm_num [lbLoQt, laLoQt, lbUpQt, logNatHi, logNatLo, highN]
  · native_decide
  · norm_num
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.209573 : ℝ) by norm_num)
      (show (0.209573 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 19058837463890717426319360 (by norm_num) 58 0.209573 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 7 0.787701 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.787701 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 132`, regime `b = 2`. -/
theorem shell_tight_132 :
    ((15578401016318740772105 : ℚ) : ℝ) * (((58 : ℝ) + 0.209573) - (((7 : ℕ) : ℝ) + 0.802957))
      ≤ ∑ p ∈ shellPrimes highN 132, Real.log (sigma p 132) := by
  apply shell_contribution_ge_tight 132 2 15578401016318740772105 (((58 : ℝ) + 0.209573)) ((((7 : ℕ) : ℝ) + 0.802957)) 19058837463890717426319360
  · norm_num
  · norm_num
  · norm_num [highN]
  · norm_num [highN]
  · norm_num [highN]
  · norm_num [highN]
  · native_decide
  · norm_num [lbLoQt, logNatHi]
  · norm_num [laLoQt, logNatHi]
  · norm_num [lbUpQt, logNatLo]
  · norm_num
  · norm_num
  · norm_num [lbLoQt, laLoQt, lbUpQt, logNatHi, logNatLo, highN]
  · native_decide
  · norm_num
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.209573 : ℝ) by norm_num)
      (show (0.209573 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 19058837463890717426319360 (by norm_num) 58 0.209573 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 7 0.802957 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.802957 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 133`, regime `b = 2`. -/
theorem shell_tight_133 :
    ((15344181668480200736473 : ℚ) : ℝ) * (((58 : ℝ) + 0.209573) - (((7 : ℕ) : ℝ) + 0.818100))
      ≤ ∑ p ∈ shellPrimes highN 133, Real.log (sigma p 133) := by
  apply shell_contribution_ge_tight 133 2 15344181668480200736473 (((58 : ℝ) + 0.209573)) ((((7 : ℕ) : ℝ) + 0.818100)) 19058837463890717426319360
  · norm_num
  · norm_num
  · norm_num [highN]
  · norm_num [highN]
  · norm_num [highN]
  · norm_num [highN]
  · native_decide
  · norm_num [lbLoQt, logNatHi]
  · norm_num [laLoQt, logNatHi]
  · norm_num [lbUpQt, logNatLo]
  · norm_num
  · norm_num
  · norm_num [lbLoQt, laLoQt, lbUpQt, logNatHi, logNatLo, highN]
  · native_decide
  · norm_num
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.209573 : ℝ) by norm_num)
      (show (0.209573 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 19058837463890717426319360 (by norm_num) 58 0.209573 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 7 0.818100 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.818100 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 134`, regime `b = 2`. -/
theorem shell_tight_134 :
    ((15115164696175261234121 : ℚ) : ℝ) * (((58 : ℝ) + 0.902720) - (((8 : ℕ) : ℝ) + 0.526081))
      ≤ ∑ p ∈ shellPrimes highN 134, Real.log (sigma p 134) := by
  apply shell_contribution_ge_tight 134 2 15115164696175261234121 (((58 : ℝ) + 0.902720)) ((((8 : ℕ) : ℝ) + 0.526081)) 38117674927781434852638720
  · norm_num
  · norm_num
  · norm_num [highN]
  · norm_num [highN]
  · norm_num [highN]
  · norm_num [highN]
  · native_decide
  · norm_num [lbLoQt, logNatHi]
  · norm_num [laLoQt, logNatHi]
  · norm_num [lbUpQt, logNatLo]
  · norm_num
  · norm_num
  · norm_num [lbLoQt, laLoQt, lbUpQt, logNatHi, logNatLo, highN]
  · native_decide
  · norm_num
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.902720 : ℝ) by norm_num)
      (show (0.902720 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 38117674927781434852638720 (by norm_num) 58 0.902720 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 8 0.526081 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.526081 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

end Erdos320
