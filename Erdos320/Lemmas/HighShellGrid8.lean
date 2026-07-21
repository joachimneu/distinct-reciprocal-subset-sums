import Erdos320.Lemmas.HighShellTight

/-!
# High-finite-input tight per-shell ledger, grid file 8/8

Machine-generated (`gen_shells.py`) tight contribution lemmas `shell_tight_135`..`shell_tight_154`, cloning the proven three-shell template of `HighShellTight.lean` (`shell_contribution_ge_tight`).
Each shell's literals (`Pm`, `sL`, `ℓ`, `pen`) are Lean-verified by the `norm_num`/`native_decide` bullet discharges; nothing is assumed.
-/

namespace Erdos320

open Finset

set_option maxHeartbeats 4000000 in
/-- Shell `m = 135`, regime `b = 2`. -/
theorem shell_tight_135 :
    ((14891197325948856076345 : ℚ) : ℝ) * (((58 : ℝ) + 0.902720) - (((8 : ℕ) : ℝ) + 0.541006))
      ≤ ∑ p ∈ shellPrimes highN 135, Real.log (sigma p 135) := by
  apply shell_contribution_ge_tight 135 2 14891197325948856076345 (((58 : ℝ) + 0.902720)) ((((8 : ℕ) : ℝ) + 0.541006)) 38117674927781434852638720
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
  · apply log_le_of_real _ _ 8 0.541006 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.541006 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 136`, regime `b = 2`. -/
theorem shell_tight_136 :
    ((14672132452398894182352 : ℚ) : ℝ) * (((58 : ℝ) + 0.902720) - (((8 : ℕ) : ℝ) + 0.555824))
      ≤ ∑ p ∈ shellPrimes highN 136, Real.log (sigma p 136) := by
  apply shell_contribution_ge_tight 136 2 14672132452398894182352 (((58 : ℝ) + 0.902720)) ((((8 : ℕ) : ℝ) + 0.555824)) 38117674927781434852638720
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
  · apply log_le_of_real _ _ 8 0.555824 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.555824 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 137`, regime `b = 2`. -/
theorem shell_tight_137 :
    ((14457828220226312778974 : ℚ) : ℝ) * (((59 : ℝ) + 0.595867) - (((9 : ℕ) : ℝ) + 0.263587))
      ≤ ∑ p ∈ shellPrimes highN 137, Real.log (sigma p 137) := by
  apply shell_contribution_ge_tight 137 2 14457828220226312778974 (((59 : ℝ) + 0.595867)) ((((9 : ℕ) : ℝ) + 0.263587)) 76235349855562869705277440
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.595867 : ℝ) by norm_num)
      (show (0.595867 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 76235349855562869705277440 (by norm_num) 59 0.595867 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 9 0.263587 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.263587 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 138`, regime `b = 2`. -/
theorem shell_tight_138 :
    ((14248147682438776229058 : ℚ) : ℝ) * (((59 : ℝ) + 0.595867) - (((9 : ℕ) : ℝ) + 0.278195))
      ≤ ∑ p ∈ shellPrimes highN 138, Real.log (sigma p 138) := by
  apply shell_contribution_ge_tight 138 2 14248147682438776229058 (((59 : ℝ) + 0.595867)) ((((9 : ℕ) : ℝ) + 0.278195)) 76235349855562869705277440
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.595867 : ℝ) by norm_num)
      (show (0.595867 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 76235349855562869705277440 (by norm_num) 59 0.595867 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 9 0.278195 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.278195 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 139`, regime `b = 2`. -/
theorem shell_tight_139 :
    ((14042959108789977833633 : ℚ) : ℝ) * (((60 : ℝ) + 0.289014) - (((9 : ℕ) : ℝ) + 0.985800))
      ≤ ∑ p ∈ shellPrimes highN 139, Real.log (sigma p 139) := by
  apply shell_contribution_ge_tight 139 2 14042959108789977833633 (((60 : ℝ) + 0.289014)) ((((9 : ℕ) : ℝ) + 0.985800)) 152470699711125739410554880
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.289014 : ℝ) by norm_num)
      (show (0.289014 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 152470699711125739410554880 (by norm_num) 60 0.289014 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 9 0.985800 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.985800 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 140`, regime `b = 2`. -/
theorem shell_tight_140 :
    ((13842135110309219940978 : ℚ) : ℝ) * (((60 : ℝ) + 0.289014) - (((10 : ℕ) : ℝ) + 0.000204))
      ≤ ∑ p ∈ shellPrimes highN 140, Real.log (sigma p 140) := by
  apply shell_contribution_ge_tight 140 2 13842135110309219940978 (((60 : ℝ) + 0.289014)) ((((10 : ℕ) : ℝ) + 0.000204)) 152470699711125739410554880
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.289014 : ℝ) by norm_num)
      (show (0.289014 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 152470699711125739410554880 (by norm_num) 60 0.289014 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 10 0.000204 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.000204 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 141`, regime `b = 2`. -/
theorem shell_tight_141 :
    ((13645553078362744854461 : ℚ) : ℝ) * (((60 : ℝ) + 0.982161) - (((10 : ℕ) : ℝ) + 0.707631))
      ≤ ∑ p ∈ shellPrimes highN 141, Real.log (sigma p 141) := by
  apply shell_contribution_ge_tight 141 2 13645553078362744854461 (((60 : ℝ) + 0.982161)) ((((10 : ℕ) : ℝ) + 0.707631)) 304941399422251478821109760
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.982161 : ℝ) by norm_num)
      (show (0.982161 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 304941399422251478821109760 (by norm_num) 60 0.982161 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 10 0.707631 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.707631 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 142`, regime `b = 2`. -/
theorem shell_tight_142 :
    ((13453094413824037548851 : ℚ) : ℝ) * (((61 : ℝ) + 0.675309) - (((11 : ℕ) : ℝ) + 0.414972))
      ≤ ∑ p ∈ shellPrimes highN 142, Real.log (sigma p 142) := by
  apply shell_contribution_ge_tight 142 2 13453094413824037548851 (((61 : ℝ) + 0.675309)) ((((11 : ℕ) : ℝ) + 0.414972)) 609882798844502957642219520
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.675309 : ℝ) by norm_num)
      (show (0.675309 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 609882798844502957642219520 (by norm_num) 61 0.675309 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 11 0.414972 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.414972 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 143`, regime `b = 2`. -/
theorem shell_tight_143 :
    ((13264644812145983256851 : ℚ) : ℝ) * (((61 : ℝ) + 0.675309) - (((11 : ℕ) : ℝ) + 0.429078))
      ≤ ∑ p ∈ shellPrimes highN 143, Real.log (sigma p 143) := by
  apply shell_contribution_ge_tight 143 2 13264644812145983256851 (((61 : ℝ) + 0.675309)) ((((11 : ℕ) : ℝ) + 0.429078)) 609882798844502957642219520
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.675309 : ℝ) by norm_num)
      (show (0.675309 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 609882798844502957642219520 (by norm_num) 61 0.675309 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 11 0.429078 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.429078 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 144`, regime `b = 2`. -/
theorem shell_tight_144 :
    ((13080093731459612972551 : ℚ) : ℝ) * (((61 : ℝ) + 0.675309) - (((11 : ℕ) : ℝ) + 0.443089))
      ≤ ∑ p ∈ shellPrimes highN 144, Real.log (sigma p 144) := by
  apply shell_contribution_ge_tight 144 2 13080093731459612972551 (((61 : ℝ) + 0.675309)) ((((11 : ℕ) : ℝ) + 0.443089)) 609882798844502957642219520
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.675309 : ℝ) by norm_num)
      (show (0.675309 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 609882798844502957642219520 (by norm_num) 61 0.675309 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 11 0.443089 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.443089 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 145`, regime `b = 2`. -/
theorem shell_tight_145 :
    ((12899334780115870729600 : ℚ) : ℝ) * (((61 : ℝ) + 0.675309) - (((11 : ℕ) : ℝ) + 0.457005))
      ≤ ∑ p ∈ shellPrimes highN 145, Real.log (sigma p 145) := by
  apply shell_contribution_ge_tight 145 2 12899334780115870729600 (((61 : ℝ) + 0.675309)) ((((11 : ℕ) : ℝ) + 0.457005)) 609882798844502957642219520
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.675309 : ℝ) by norm_num)
      (show (0.675309 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 609882798844502957642219520 (by norm_num) 61 0.675309 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 11 0.457005 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.457005 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 146`, regime `b = 2`. -/
theorem shell_tight_146 :
    ((12722264624773243513586 : ℚ) : ℝ) * (((62 : ℝ) + 0.368456) - (((12 : ℕ) : ℝ) + 0.163969))
      ≤ ∑ p ∈ shellPrimes highN 146, Real.log (sigma p 146) := by
  apply shell_contribution_ge_tight 146 2 12722264624773243513586 (((62 : ℝ) + 0.368456)) ((((12 : ℕ) : ℝ) + 0.163969)) 1219765597689005915284439040
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.368456 : ℝ) by norm_num)
      (show (0.368456 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 1219765597689005915284439040 (by norm_num) 62 0.368456 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 12 0.163969 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.163969 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 147`, regime `b = 2`. -/
theorem shell_tight_147 :
    ((12548783823269880754345 : ℚ) : ℝ) * (((62 : ℝ) + 0.368456) - (((12 : ℕ) : ℝ) + 0.177698))
      ≤ ∑ p ∈ shellPrimes highN 147, Real.log (sigma p 147) := by
  apply shell_contribution_ge_tight 147 2 12548783823269880754345 (((62 : ℝ) + 0.368456)) ((((12 : ℕ) : ℝ) + 0.177698)) 1219765597689005915284439040
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.368456 : ℝ) by norm_num)
      (show (0.368456 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 1219765597689005915284439040 (by norm_num) 62 0.368456 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 12 0.177698 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.177698 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 148`, regime `b = 2`. -/
theorem shell_tight_148 :
    ((12378796163129356596090 : ℚ) : ℝ) * (((63 : ℝ) + 0.061603) - (((12 : ℕ) : ℝ) + 0.884482))
      ≤ ∑ p ∈ shellPrimes highN 148, Real.log (sigma p 148) := by
  apply shell_contribution_ge_tight 148 2 12378796163129356596090 (((63 : ℝ) + 0.061603)) ((((12 : ℕ) : ℝ) + 0.884482)) 2439531195378011830568878080
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.061603 : ℝ) by norm_num)
      (show (0.061603 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 2439531195378011830568878080 (by norm_num) 63 0.061603 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 12 0.884482 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.884482 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 149`, regime `b = 2`. -/
theorem shell_tight_149 :
    ((12212208634907088731316 : ℚ) : ℝ) * (((63 : ℝ) + 0.754750) - (((13 : ℕ) : ℝ) + 0.591176))
      ≤ ∑ p ∈ shellPrimes highN 149, Real.log (sigma p 149) := by
  apply shell_contribution_ge_tight 149 2 12212208634907088731316 (((63 : ℝ) + 0.754750)) ((((13 : ℕ) : ℝ) + 0.591176)) 4879062390756023661137756160
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.754750 : ℝ) by norm_num)
      (show (0.754750 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 4879062390756023661137756160 (by norm_num) 63 0.754750 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 13 0.591176 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.591176 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 150`, regime `b = 2`. -/
theorem shell_tight_150 :
    ((12048931186943488856130 : ℚ) : ℝ) * (((63 : ℝ) + 0.754750) - (((13 : ℕ) : ℝ) + 0.604637))
      ≤ ∑ p ∈ shellPrimes highN 150, Real.log (sigma p 150) := by
  apply shell_contribution_ge_tight 150 2 12048931186943488856130 (((63 : ℝ) + 0.754750)) ((((13 : ℕ) : ℝ) + 0.604637)) 4879062390756023661137756160
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.754750 : ℝ) by norm_num)
      (show (0.754750 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 4879062390756023661137756160 (by norm_num) 63 0.754750 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 13 0.604637 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.604637 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 151`, regime `b = 2`. -/
theorem shell_tight_151 :
    ((11888876966558339110458 : ℚ) : ℝ) * (((64 : ℝ) + 0.447897) - (((14 : ℕ) : ℝ) + 0.311156))
      ≤ ∑ p ∈ shellPrimes highN 151, Real.log (sigma p 151) := by
  apply shell_contribution_ge_tight 151 2 11888876966558339110458 (((64 : ℝ) + 0.447897)) ((((14 : ℕ) : ℝ) + 0.311156)) 9758124781512047322275512320
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.447897 : ℝ) by norm_num)
      (show (0.447897 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 9758124781512047322275512320 (by norm_num) 64 0.447897 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 14 0.311156 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.311156 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 152`, regime `b = 2`. -/
theorem shell_tight_152 :
    ((11731961660185549160212 : ℚ) : ℝ) * (((64 : ℝ) + 0.447897) - (((14 : ℕ) : ℝ) + 0.324442))
      ≤ ∑ p ∈ shellPrimes highN 152, Real.log (sigma p 152) := by
  apply shell_contribution_ge_tight 152 2 11731961660185549160212 (((64 : ℝ) + 0.447897)) ((((14 : ℕ) : ℝ) + 0.324442)) 9758124781512047322275512320
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.447897 : ℝ) by norm_num)
      (show (0.447897 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 9758124781512047322275512320 (by norm_num) 64 0.447897 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 14 0.324442 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.324442 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 153`, regime `b = 2`. -/
theorem shell_tight_153 :
    ((11578104002834200343539 : ℚ) : ℝ) * (((64 : ℝ) + 0.447897) - (((14 : ℕ) : ℝ) + 0.337643))
      ≤ ∑ p ∈ shellPrimes highN 153, Real.log (sigma p 153) := by
  apply shell_contribution_ge_tight 153 2 11578104002834200343539 (((64 : ℝ) + 0.447897)) ((((14 : ℕ) : ℝ) + 0.337643)) 9758124781512047322275512320
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.447897 : ℝ) by norm_num)
      (show (0.447897 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 9758124781512047322275512320 (by norm_num) 64 0.447897 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 14 0.337643 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.337643 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 154`, regime `b = 2`. -/
theorem shell_tight_154 :
    ((11427225097325626651083 : ℚ) : ℝ) * (((64 : ℝ) + 0.447897) - (((14 : ℕ) : ℝ) + 0.350760))
      ≤ ∑ p ∈ shellPrimes highN 154, Real.log (sigma p 154) := by
  apply shell_contribution_ge_tight 154 2 11427225097325626651083 (((64 : ℝ) + 0.447897)) ((((14 : ℕ) : ℝ) + 0.350760)) 9758124781512047322275512320
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.447897 : ℝ) by norm_num)
      (show (0.447897 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 9758124781512047322275512320 (by norm_num) 64 0.447897 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 14 0.350760 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.350760 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

end Erdos320
