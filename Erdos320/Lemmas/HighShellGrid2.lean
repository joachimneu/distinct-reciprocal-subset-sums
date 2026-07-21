import Erdos320.Lemmas.HighShellTight

/-!
# High-finite-input tight per-shell ledger, grid file 2/8

Machine-generated (`gen_shells.py`) tight contribution lemmas `shell_tight_20`..`shell_tight_38`, cloning the proven three-shell template of `HighShellTight.lean` (`shell_contribution_ge_tight`).
Each shell's literals (`Pm`, `sL`, `ℓ`, `pen`) are Lean-verified by the `norm_num`/`native_decide` bullet discharges; nothing is assumed.
-/

namespace Erdos320

open Finset

set_option maxHeartbeats 4000000 in
/-- Shell `m = 20`, regime `b = 0`. -/
theorem shell_tight_20 :
    ((647911902638555182713302 : ℚ) : ℝ) * (((11 : ℝ) + 0.751753) - 0)
      ≤ ∑ p ∈ shellPrimes highN 20, Real.log (sigma p 20) := by
  apply shell_contribution_ge_tight 20 0 647911902638555182713302 (((11 : ℝ) + 0.751753)) (0) 126976
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.751753 : ℝ) by norm_num)
      (show (0.751753 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 126976 (by norm_num) 11 0.751753 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · simp

set_option maxHeartbeats 4000000 in
/-- Shell `m = 21`, regime `b = 0`. -/
theorem shell_tight_21 :
    ((589342821991328128309872 : ℚ) : ℝ) * (((12 : ℝ) + 0.319972) - 0)
      ≤ ∑ p ∈ shellPrimes highN 21, Real.log (sigma p 21) := by
  apply shell_contribution_ge_tight 21 0 589342821991328128309872 (((12 : ℝ) + 0.319972)) (0) 224128
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.319972 : ℝ) by norm_num)
      (show (0.319972 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 224128 (by norm_num) 12 0.319972 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · simp

set_option maxHeartbeats 4000000 in
/-- Shell `m = 22`, regime `b = 0`. -/
theorem shell_tight_22 :
    ((538379394681274204941285 : ℚ) : ℝ) * (((13 : ℝ) + 0.013119) - 0)
      ≤ ∑ p ∈ shellPrimes highN 22, Real.log (sigma p 22) := by
  apply shell_contribution_ge_tight 22 0 538379394681274204941285 (((13 : ℝ) + 0.013119)) (0) 448256
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.013119 : ℝ) by norm_num)
      (show (0.013119 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 448256 (by norm_num) 13 0.013119 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · simp

set_option maxHeartbeats 4000000 in
/-- Shell `m = 23`, regime `b = 0`. -/
theorem shell_tight_23 :
    ((493758375781123300776118 : ℚ) : ℝ) * (((13 : ℝ) + 0.706266) - 0)
      ≤ ∑ p ∈ shellPrimes highN 23, Real.log (sigma p 23) := by
  apply shell_contribution_ge_tight 23 0 493758375781123300776118 (((13 : ℝ) + 0.706266)) (0) 896512
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.706266 : ℝ) by norm_num)
      (show (0.706266 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 896512 (by norm_num) 13 0.706266 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · simp

set_option maxHeartbeats 4000000 in
/-- Shell `m = 24`, regime `b = 0`. -/
theorem shell_tight_24 :
    ((454468460072633480138853 : ℚ) : ℝ) * (((13 : ℝ) + 0.750259) - 0)
      ≤ ∑ p ∈ shellPrimes highN 24, Real.log (sigma p 24) := by
  apply shell_contribution_ge_tight 24 0 454468460072633480138853 (((13 : ℝ) + 0.750259)) (0) 936832
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.750259 : ℝ) by norm_num)
      (show (0.750259 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 936832 (by norm_num) 13 0.750259 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · simp

set_option maxHeartbeats 4000000 in
/-- Shell `m = 25`, regime `b = 0`. -/
theorem shell_tight_25 :
    ((419692294977197246663100 : ℚ) : ℝ) * (((14 : ℝ) + 0.443406) - 0)
      ≤ ∑ p ∈ shellPrimes highN 25, Real.log (sigma p 25) := by
  apply shell_contribution_ge_tight 25 0 419692294977197246663100 (((14 : ℝ) + 0.443406)) (0) 1873664
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.443406 : ℝ) by norm_num)
      (show (0.443406 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 1873664 (by norm_num) 14 0.443406 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · simp

set_option maxHeartbeats 4000000 in
/-- Shell `m = 26`, regime `b = 0`. -/
theorem shell_tight_26 :
    ((388763454600444074917037 : ℚ) : ℝ) * (((15 : ℝ) + 0.136553) - 0)
      ≤ ∑ p ∈ shellPrimes highN 26, Real.log (sigma p 26) := by
  apply shell_contribution_ge_tight 26 0 388763454600444074917037 (((15 : ℝ) + 0.136553)) (0) 3747328
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.136553 : ℝ) by norm_num)
      (show (0.136553 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 3747328 (by norm_num) 15 0.136553 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · simp

set_option maxHeartbeats 4000000 in
/-- Shell `m = 27`, regime `b = 0`. -/
theorem shell_tight_27 :
    ((361134196263837917460230 : ℚ) : ℝ) * (((15 : ℝ) + 0.829700) - 0)
      ≤ ∑ p ∈ shellPrimes highN 27, Real.log (sigma p 27) := by
  apply shell_contribution_ge_tight 27 0 361134196263837917460230 (((15 : ℝ) + 0.829700)) (0) 7494656
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.829700 : ℝ) by norm_num)
      (show (0.829700 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 7494656 (by norm_num) 15 0.829700 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · simp

set_option maxHeartbeats 4000000 in
/-- Shell `m = 28`, regime `b = 0`. -/
theorem shell_tight_28 :
    ((336350952281461915258618 : ℚ) : ℝ) * (((15 : ℝ) + 0.865926) - 0)
      ≤ ∑ p ∈ shellPrimes highN 28, Real.log (sigma p 28) := by
  apply shell_contribution_ge_tight 28 0 336350952281461915258618 (((15 : ℝ) + 0.865926)) (0) 7771136
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.865926 : ℝ) by norm_num)
      (show (0.865926 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 7771136 (by norm_num) 15 0.865926 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · simp

set_option maxHeartbeats 4000000 in
/-- Shell `m = 29`, regime `b = 0`. -/
theorem shell_tight_29 :
    ((314035538677870658767931 : ℚ) : ℝ) * (((16 : ℝ) + 0.559074) - 0)
      ≤ ∑ p ∈ shellPrimes highN 29, Real.log (sigma p 29) := by
  apply shell_contribution_ge_tight 29 0 314035538677870658767931 (((16 : ℝ) + 0.559074)) (0) 15542272
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.559074 : ℝ) by norm_num)
      (show (0.559074 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 15542272 (by norm_num) 16 0.559074 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · simp

set_option maxHeartbeats 4000000 in
/-- Shell `m = 30`, regime `b = 0`. -/
theorem shell_tight_30 :
    ((293870598247315734782347 : ℚ) : ℝ) * (((16 : ℝ) + 0.580969) - 0)
      ≤ ∑ p ∈ shellPrimes highN 30, Real.log (sigma p 30) := by
  apply shell_contribution_ge_tight 30 0 293870598247315734782347 (((16 : ℝ) + 0.580969)) (0) 15886336
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.580969 : ℝ) by norm_num)
      (show (0.580969 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 15886336 (by norm_num) 16 0.580969 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · simp

set_option maxHeartbeats 4000000 in
/-- Shell `m = 31`, regime `b = 0`. -/
theorem shell_tight_31 :
    ((275588229055105472856769 : ℚ) : ℝ) * (((17 : ℝ) + 0.274117) - 0)
      ≤ ∑ p ∈ shellPrimes highN 31, Real.log (sigma p 31) := by
  apply shell_contribution_ge_tight 31 0 275588229055105472856769 (((17 : ℝ) + 0.274117)) (0) 31772672
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.274117 : ℝ) by norm_num)
      (show (0.274117 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 31772672 (by norm_num) 17 0.274117 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · simp

set_option maxHeartbeats 4000000 in
/-- Shell `m = 32`, regime `b = 0`. -/
theorem shell_tight_32 :
    ((258961001564129049265075 : ℚ) : ℝ) * (((17 : ℝ) + 0.967264) - 0)
      ≤ ∑ p ∈ shellPrimes highN 32, Real.log (sigma p 32) := by
  apply shell_contribution_ge_tight 32 0 258961001564129049265075 (((17 : ℝ) + 0.967264)) (0) 63545344
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.967264 : ℝ) by norm_num)
      (show (0.967264 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 63545344 (by norm_num) 17 0.967264 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · simp

set_option maxHeartbeats 4000000 in
/-- Shell `m = 33`, regime `b = 0`. -/
theorem shell_tight_33 :
    ((243794848423115947923731 : ℚ) : ℝ) * (((18 : ℝ) + 0.534585) - 0)
      ≤ ∑ p ∈ shellPrimes highN 33, Real.log (sigma p 33) := by
  apply shell_contribution_ge_tight 33 0 243794848423115947923731 (((18 : ℝ) + 0.534585)) (0) 112064512
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.534585 : ℝ) by norm_num)
      (show (0.534585 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 112064512 (by norm_num) 18 0.534585 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · simp

set_option maxHeartbeats 4000000 in
/-- Shell `m = 34`, regime `b = 0`. -/
theorem shell_tight_34 :
    ((229923341905312063165082 : ℚ) : ℝ) * (((19 : ℝ) + 0.227732) - 0)
      ≤ ∑ p ∈ shellPrimes highN 34, Real.log (sigma p 34) := by
  apply shell_contribution_ge_tight 34 0 229923341905312063165082 (((19 : ℝ) + 0.227732)) (0) 224129024
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.227732 : ℝ) by norm_num)
      (show (0.227732 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 224129024 (by norm_num) 19 0.227732 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · simp

set_option maxHeartbeats 4000000 in
/-- Shell `m = 35`, regime `b = 0`. -/
theorem shell_tight_35 :
    ((217203109944863732059403 : ℚ) : ℝ) * (((19 : ℝ) + 0.257972) - 0)
      ≤ ∑ p ∈ shellPrimes highN 35, Real.log (sigma p 35) := by
  apply shell_contribution_ge_tight 35 0 217203109944863732059403 (((19 : ℝ) + 0.257972)) (0) 231010304
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.257972 : ℝ) by norm_num)
      (show (0.257972 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 231010304 (by norm_num) 19 0.257972 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · simp

set_option maxHeartbeats 4000000 in
/-- Shell `m = 36`, regime `b = 0`. -/
theorem shell_tight_36 :
    ((205510100007638925075780 : ℚ) : ℝ) * (((19 : ℝ) + 0.283703) - 0)
      ≤ ∑ p ∈ shellPrimes highN 36, Real.log (sigma p 36) := by
  apply shell_contribution_ge_tight 36 0 205510100007638925075780 (((19 : ℝ) + 0.283703)) (0) 237031424
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.283703 : ℝ) by norm_num)
      (show (0.283703 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 237031424 (by norm_num) 19 0.283703 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · simp

set_option maxHeartbeats 4000000 in
/-- Shell `m = 37`, regime `b = 0`. -/
theorem shell_tight_37 :
    ((194736541957647516061748 : ℚ) : ℝ) * (((19 : ℝ) + 0.976850) - 0)
      ≤ ∑ p ∈ shellPrimes highN 37, Real.log (sigma p 37) := by
  apply shell_contribution_ge_tight 37 0 194736541957647516061748 (((19 : ℝ) + 0.976850)) (0) 474062848
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.976850 : ℝ) by norm_num)
      (show (0.976850 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 474062848 (by norm_num) 19 0.976850 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · simp

set_option maxHeartbeats 4000000 in
/-- Shell `m = 38`, regime `b = 0`. -/
theorem shell_tight_38 :
    ((184788438415488159447741 : ℚ) : ℝ) * (((20 : ℝ) + 0.669997) - 0)
      ≤ ∑ p ∈ shellPrimes highN 38, Real.log (sigma p 38) := by
  apply shell_contribution_ge_tight 38 0 184788438415488159447741 (((20 : ℝ) + 0.669997)) (0) 948125696
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.669997 : ℝ) by norm_num)
      (show (0.669997 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 948125696 (by norm_num) 20 0.669997 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · simp

end Erdos320
