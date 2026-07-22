import Erdos320.Lemmas.HighShellTight

/-!
# High-finite-input tight per-shell ledger, grid file 4/8

Machine-generated tight contribution lemmas `shell_tight_58`..`shell_tight_76`, cloning the proven three-shell template of `HighShellTight.lean` (`shell_contribution_ge_tight`).
Each shell's literals (`Pm`, `sL`, `ℓ`, `pen`) are Lean-verified by the `norm_num`/`native_decide` bullet discharges; nothing is assumed.
-/

namespace Erdos320

open Finset

set_option maxHeartbeats 4000000 in
/-- Shell `m = 58`, regime `b = 0`. -/
theorem shell_tight_58 :
    ((80216565432828451375078 : ℚ) : ℝ) * (((29 : ℝ) + 0.586608) - 0)
      ≤ ∑ p ∈ shellPrimes highN 58, Real.log (sigma p 58) := by
  apply shell_contribution_ge_tight 58 0 80216565432828451375078 (((29 : ℝ) + 0.586608)) (0) 7068068085760
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.586608 : ℝ) by norm_num)
      (show (0.586608 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 7068068085760 (by norm_num) 29 0.586608 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · simp

set_option maxHeartbeats 4000000 in
/-- Shell `m = 59`, regime `b = 0`. -/
theorem shell_tight_59 :
    ((77546637694800151491609 : ℚ) : ℝ) * (((30 : ℝ) + 0.279755) - 0)
      ≤ ∑ p ∈ shellPrimes highN 59, Real.log (sigma p 59) := by
  apply shell_contribution_ge_tight 59 0 77546637694800151491609 (((30 : ℝ) + 0.279755)) (0) 14136136171520
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.279755 : ℝ) by norm_num)
      (show (0.279755 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 14136136171520 (by norm_num) 30 0.279755 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · simp

set_option maxHeartbeats 4000000 in
/-- Shell `m = 60`, regime `b = 0`. -/
theorem shell_tight_60 :
    ((75007596126019673078163 : ℚ) : ℝ) * (((30 : ℝ) + 0.287480) - 0)
      ≤ ∑ p ∈ shellPrimes highN 60, Real.log (sigma p 60) := by
  apply shell_contribution_ge_tight 60 0 75007596126019673078163 (((30 : ℝ) + 0.287480)) (0) 14245758500864
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.287480 : ℝ) by norm_num)
      (show (0.287480 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 14245758500864 (by norm_num) 30 0.287480 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · simp

set_option maxHeartbeats 4000000 in
/-- Shell `m = 61`, regime `b = 1`. -/
theorem shell_tight_61 :
    ((72591021963302951272348 : ℚ) : ℝ) * (((30 : ℝ) + 0.980627) - (((0 : ℕ) : ℝ) + 0.000001))
      ≤ ∑ p ∈ shellPrimes highN 61, Real.log (sigma p 61) := by
  apply shell_contribution_ge_tight 61 1 72591021963302951272348 (((30 : ℝ) + 0.980627)) ((((0 : ℕ) : ℝ) + 0.000001)) 28491517001728
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.980627 : ℝ) by norm_num)
      (show (0.980627 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 28491517001728 (by norm_num) 30 0.980627 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 0 0.000001 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.000001 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 62`, regime `b = 1`. -/
theorem shell_tight_62 :
    ((70289161327389758341463 : ℚ) : ℝ) * (((31 : ℝ) + 0.673774) - (((0 : ℕ) : ℝ) + 0.000001))
      ≤ ∑ p ∈ shellPrimes highN 62, Real.log (sigma p 62) := by
  apply shell_contribution_ge_tight 62 1 70289161327389758341463 (((31 : ℝ) + 0.673774)) ((((0 : ℕ) : ℝ) + 0.000001)) 56983034003456
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.673774 : ℝ) by norm_num)
      (show (0.673774 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 56983034003456 (by norm_num) 31 0.673774 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 0 0.000001 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.000001 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 63`, regime `b = 1`. -/
theorem shell_tight_63 :
    ((68094865441889009135520 : ℚ) : ℝ) * (((31 : ℝ) + 0.682712) - (((0 : ℕ) : ℝ) + 0.000001))
      ≤ ∑ p ∈ shellPrimes highN 63, Real.log (sigma p 63) := by
  apply shell_contribution_ge_tight 63 1 68094865441889009135520 (((31 : ℝ) + 0.682712)) ((((0 : ℕ) : ℝ) + 0.000001)) 57494604873728
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.682712 : ℝ) by norm_num)
      (show (0.682712 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 57494604873728 (by norm_num) 31 0.682712 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 0 0.000001 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.000001 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 64`, regime `b = 1`. -/
theorem shell_tight_64 :
    ((66001533947971867187181 : ℚ) : ℝ) * (((32 : ℝ) + 0.375859) - (((0 : ℕ) : ℝ) + 0.000001))
      ≤ ∑ p ∈ shellPrimes highN 64, Real.log (sigma p 64) := by
  apply shell_contribution_ge_tight 64 1 66001533947971867187181 (((32 : ℝ) + 0.375859)) ((((0 : ℕ) : ℝ) + 0.000001)) 114989209747456
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.375859 : ℝ) by norm_num)
      (show (0.375859 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 114989209747456 (by norm_num) 32 0.375859 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 0 0.000001 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.000001 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 65`, regime `b = 1`. -/
theorem shell_tight_65 :
    ((64003066087506431042221 : ℚ) : ℝ) * (((32 : ℝ) + 0.557000) - (((0 : ℕ) : ℝ) + 0.000001))
      ≤ ∑ p ∈ shellPrimes highN 65, Real.log (sigma p 65) := by
  apply shell_contribution_ge_tight 65 1 64003066087506431042221 (((32 : ℝ) + 0.557000)) ((((0 : ℕ) : ℝ) + 0.000001)) 137824242237440
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.557000 : ℝ) by norm_num)
      (show (0.557000 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 137824242237440 (by norm_num) 32 0.557000 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 0 0.000001 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.000001 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 66`, regime `b = 1`. -/
theorem shell_tight_66 :
    ((62093813124910437658137 : ℚ) : ℝ) * (((32 : ℝ) + 0.565735) - (((0 : ℕ) : ℝ) + 0.000001))
      ≤ ∑ p ∈ shellPrimes highN 66, Real.log (sigma p 66) := by
  apply shell_contribution_ge_tight 66 1 62093813124910437658137 (((32 : ℝ) + 0.565735)) ((((0 : ℕ) : ℝ) + 0.000001)) 139033409748992
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.565735 : ℝ) by norm_num)
      (show (0.565735 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 139033409748992 (by norm_num) 32 0.565735 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 0 0.000001 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.000001 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 67`, regime `b = 1`. -/
theorem shell_tight_67 :
    ((60268542915851096663466 : ℚ) : ℝ) * (((33 : ℝ) + 0.258882) - (((0 : ℕ) : ℝ) + 0.000001))
      ≤ ∑ p ∈ shellPrimes highN 67, Real.log (sigma p 67) := by
  apply shell_contribution_ge_tight 67 1 60268542915851096663466 (((33 : ℝ) + 0.258882)) ((((0 : ℕ) : ℝ) + 0.000001)) 278066819497984
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.258882 : ℝ) by norm_num)
      (show (0.258882 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 278066819497984 (by norm_num) 33 0.258882 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 0 0.000001 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.000001 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 68`, regime `b = 1`. -/
theorem shell_tight_68 :
    ((58522399761546911203318 : ℚ) : ℝ) * (((33 : ℝ) + 0.888939) - (((0 : ℕ) : ℝ) + 0.000001))
      ≤ ∑ p ∈ shellPrimes highN 68, Real.log (sigma p 68) := by
  apply shell_contribution_ge_tight 68 1 58522399761546911203318 (((33 : ℝ) + 0.888939)) ((((0 : ℕ) : ℝ) + 0.000001)) 522131016253440
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.888939 : ℝ) by norm_num)
      (show (0.888939 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 522131016253440 (by norm_num) 33 0.888939 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 0 0.000001 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.000001 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 69`, regime `b = 1`. -/
theorem shell_tight_69 :
    ((56850875377868693895126 : ℚ) : ℝ) * (((34 : ℝ) + 0.582086) - (((0 : ℕ) : ℝ) + 0.000001))
      ≤ ∑ p ∈ shellPrimes highN 69, Real.log (sigma p 69) := by
  apply shell_contribution_ge_tight 69 1 56850875377868693895126 (((34 : ℝ) + 0.582086)) ((((0 : ℕ) : ℝ) + 0.000001)) 1044262032506880
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.582086 : ℝ) by norm_num)
      (show (0.582086 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 1044262032506880 (by norm_num) 34 0.582086 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 0 0.000001 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.000001 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 70`, regime `b = 1`. -/
theorem shell_tight_70 :
    ((55249777143227086266588 : ℚ) : ℝ) * (((34 : ℝ) + 0.588887) - (((0 : ℕ) : ℝ) + 0.000001))
      ≤ ∑ p ∈ shellPrimes highN 70, Real.log (sigma p 70) := by
  apply shell_contribution_ge_tight 70 1 55249777143227086266588 (((34 : ℝ) + 0.588887)) ((((0 : ℕ) : ℝ) + 0.000001)) 1051387483914240
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.588887 : ℝ) by norm_num)
      (show (0.588887 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 1051387483914240 (by norm_num) 34 0.588887 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 0 0.000001 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.000001 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 71`, regime `b = 1`. -/
theorem shell_tight_71 :
    ((53715203480759880209157 : ℚ) : ℝ) * (((35 : ℝ) + 0.282034) - (((0 : ℕ) : ℝ) + 0.000001))
      ≤ ∑ p ∈ shellPrimes highN 71, Real.log (sigma p 71) := by
  apply shell_contribution_ge_tight 71 1 53715203480759880209157 (((35 : ℝ) + 0.282034)) ((((0 : ℕ) : ℝ) + 0.000001)) 2102774967828480
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.282034 : ℝ) by norm_num)
      (show (0.282034 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 2102774967828480 (by norm_num) 35 0.282034 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 0 0.000001 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.000001 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 72`, regime `b = 1`. -/
theorem shell_tight_72 :
    ((52243518740526820857159 : ℚ) : ℝ) * (((35 : ℝ) + 0.288686) - (((0 : ℕ) : ℝ) + 0.000001))
      ≤ ∑ p ∈ shellPrimes highN 72, Real.log (sigma p 72) := by
  apply shell_contribution_ge_tight 72 1 52243518740526820857159 (((35 : ℝ) + 0.288686)) ((((0 : ℕ) : ℝ) + 0.000001)) 2116809947873280
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.288686 : ℝ) by norm_num)
      (show (0.288686 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 2116809947873280 (by norm_num) 35 0.288686 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 0 0.000001 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.000001 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 73`, regime `b = 1`. -/
theorem shell_tight_73 :
    ((50831333718340665218090 : ℚ) : ℝ) * (((35 : ℝ) + 0.981833) - (((0 : ℕ) : ℝ) + 0.000001))
      ≤ ∑ p ∈ shellPrimes highN 73, Real.log (sigma p 73) := by
  apply shell_contribution_ge_tight 73 1 50831333718340665218090 (((35 : ℝ) + 0.981833)) ((((0 : ℕ) : ℝ) + 0.000001)) 4233619895746560
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.981833 : ℝ) by norm_num)
      (show (0.981833 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 4233619895746560 (by norm_num) 35 0.981833 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 0 0.000001 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.000001 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 74`, regime `b = 1`. -/
theorem shell_tight_74 :
    ((49475482716512154232394 : ℚ) : ℝ) * (((36 : ℝ) + 0.674980) - (((0 : ℕ) : ℝ) + 0.000001))
      ≤ ∑ p ∈ shellPrimes highN 74, Real.log (sigma p 74) := by
  apply shell_contribution_ge_tight 74 1 49475482716512154232394 (((36 : ℝ) + 0.674980)) ((((0 : ℕ) : ℝ) + 0.000001)) 8467239791493120
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.674980 : ℝ) by norm_num)
      (show (0.674980 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 8467239791493120 (by norm_num) 36 0.674980 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 0 0.000001 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.000001 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 75`, regime `b = 1`. -/
theorem shell_tight_75 :
    ((48173009124861405295313 : ℚ) : ℝ) * (((36 : ℝ) + 0.903252) - (((0 : ℕ) : ℝ) + 0.000001))
      ≤ ∑ p ∈ shellPrimes highN 75, Real.log (sigma p 75) := by
  apply shell_contribution_ge_tight 75 1 48173009124861405295313 (((36 : ℝ) + 0.903252)) ((((0 : ℕ) : ℝ) + 0.000001)) 10638462277386240
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.903252 : ℝ) by norm_num)
      (show (0.903252 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 10638462277386240 (by norm_num) 36 0.903252 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 0 0.000001 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.000001 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 76`, regime `b = 1`. -/
theorem shell_tight_76 :
    ((46921147380157998946219 : ℚ) : ℝ) * (((37 : ℝ) + 0.393666) - (((0 : ℕ) : ℝ) + 0.000001))
      ≤ ∑ p ∈ shellPrimes highN 76, Real.log (sigma p 76) := by
  apply shell_contribution_ge_tight 76 1 46921147380157998946219 (((37 : ℝ) + 0.393666)) ((((0 : ℕ) : ℝ) + 0.000001)) 17372520791408640
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.393666 : ℝ) by norm_num)
      (show (0.393666 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 17372520791408640 (by norm_num) 37 0.393666 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 0 0.000001 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.000001 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

end Erdos320
