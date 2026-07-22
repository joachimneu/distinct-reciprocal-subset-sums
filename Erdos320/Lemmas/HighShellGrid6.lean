import Erdos320.Lemmas.HighShellTight

/-!
# High-finite-input tight per-shell ledger, grid file 6/8

Machine-generated tight contribution lemmas `shell_tight_96`..`shell_tight_114`, each a clone of the proven per-shell template `shell_contribution_ge_tight` from `HighShellTight.lean`.
Each shell's literals (`Pm`, `sL`, `ℓ`, `pen`) are Lean-verified by the `norm_num`/`native_decide` bullet discharges; nothing is assumed.
-/

namespace Erdos320

open Finset

set_option maxHeartbeats 4000000 in
/-- Shell `m = 96`, regime `b = 1`. -/
theorem shell_tight_96 :
    ((29463641956089800965556 : ℚ) : ℝ) * (((44 : ℝ) + 0.346629) - (((0 : ℕ) : ℝ) + 0.000617))
      ≤ ∑ p ∈ shellPrimes highN 96, Real.log (sigma p 96) := by
  apply shell_contribution_ge_tight 96 1 29463641956089800965556 (((44 : ℝ) + 0.346629)) ((((0 : ℕ) : ℝ) + 0.000617)) 18175923789873807360
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.346629 : ℝ) by norm_num)
      (show (0.346629 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 18175923789873807360 (by norm_num) 44 0.346629 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 0 0.000617 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.000617 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 97`, regime `b = 1`. -/
theorem shell_tight_97 :
    ((28860553985324473531664 : ℚ) : ℝ) * (((45 : ℝ) + 0.039776) - (((0 : ℕ) : ℝ) + 0.001259))
      ≤ ∑ p ∈ shellPrimes highN 97, Real.log (sigma p 97) := by
  apply shell_contribution_ge_tight 97 1 28860553985324473531664 (((45 : ℝ) + 0.039776)) ((((0 : ℕ) : ℝ) + 0.001259)) 36351847579747614720
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.039776 : ℝ) by norm_num)
      (show (0.039776 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 36351847579747614720 (by norm_num) 45 0.039776 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 0 0.001259 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.001259 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 98`, regime `b = 1`. -/
theorem shell_tight_98 :
    ((28275707753950429084582 : ℚ) : ℝ) * (((45 : ℝ) + 0.732923) - (((0 : ℕ) : ℝ) + 0.002568))
      ≤ ∑ p ∈ shellPrimes highN 98, Real.log (sigma p 98) := by
  apply shell_contribution_ge_tight 98 1 28275707753950429084582 (((45 : ℝ) + 0.732923)) ((((0 : ℕ) : ℝ) + 0.002568)) 72703695159495229440
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.732923 : ℝ) by norm_num)
      (show (0.732923 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 72703695159495229440 (by norm_num) 45 0.732923 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 0 0.002568 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.002568 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 99`, regime `b = 1`. -/
theorem shell_tight_99 :
    ((27708375498262540550213 : ℚ) : ℝ) * (((45 : ℝ) + 0.732923) - (((0 : ℕ) : ℝ) + 0.002621))
      ≤ ∑ p ∈ shellPrimes highN 99, Real.log (sigma p 99) := by
  apply shell_contribution_ge_tight 99 1 27708375498262540550213 (((45 : ℝ) + 0.732923)) ((((0 : ℕ) : ℝ) + 0.002621)) 72703695159495229440
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.732923 : ℝ) by norm_num)
      (show (0.732923 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 72703695159495229440 (by norm_num) 45 0.732923 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 0 0.002621 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.002621 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 100`, regime `b = 1`. -/
theorem shell_tight_100 :
    ((27157865202650649518395 : ℚ) : ℝ) * (((45 : ℝ) + 0.732923) - (((0 : ℕ) : ℝ) + 0.002674))
      ≤ ∑ p ∈ shellPrimes highN 100, Real.log (sigma p 100) := by
  apply shell_contribution_ge_tight 100 1 27157865202650649518395 (((45 : ℝ) + 0.732923)) ((((0 : ℕ) : ℝ) + 0.002674)) 72703695159495229440
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.732923 : ℝ) by norm_num)
      (show (0.732923 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 72703695159495229440 (by norm_num) 45 0.732923 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 0 0.002674 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.002674 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 101`, regime `b = 1`. -/
theorem shell_tight_101 :
    ((26623518639003033723123 : ℚ) : ℝ) * (((46 : ℝ) + 0.426071) - (((0 : ℕ) : ℝ) + 0.005447))
      ≤ ∑ p ∈ shellPrimes highN 101, Real.log (sigma p 101) := by
  apply shell_contribution_ge_tight 101 1 26623518639003033723123 (((46 : ℝ) + 0.426071)) ((((0 : ℕ) : ℝ) + 0.005447)) 145407390318990458880
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.426071 : ℝ) by norm_num)
      (show (0.426071 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 145407390318990458880 (by norm_num) 46 0.426071 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 0 0.005447 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.005447 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 102`, regime `b = 1`. -/
theorem shell_tight_102 :
    ((26104709272364487046160 : ℚ) : ℝ) * (((46 : ℝ) + 0.426071) - (((0 : ℕ) : ℝ) + 0.005555))
      ≤ ∑ p ∈ shellPrimes highN 102, Real.log (sigma p 102) := by
  apply shell_contribution_ge_tight 102 1 26104709272364487046160 (((46 : ℝ) + 0.426071)) ((((0 : ℕ) : ℝ) + 0.005555)) 145407390318990458880
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.426071 : ℝ) by norm_num)
      (show (0.426071 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 145407390318990458880 (by norm_num) 46 0.426071 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 0 0.005555 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.005555 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 103`, regime `b = 1`. -/
theorem shell_tight_103 :
    ((25600841123445862189423 : ℚ) : ℝ) * (((47 : ℝ) + 0.119218) - (((0 : ℕ) : ℝ) + 0.011296))
      ≤ ∑ p ∈ shellPrimes highN 103, Real.log (sigma p 103) := by
  apply shell_contribution_ge_tight 103 1 25600841123445862189423 (((47 : ℝ) + 0.119218)) ((((0 : ℕ) : ℝ) + 0.011296)) 290814780637980917760
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.119218 : ℝ) by norm_num)
      (show (0.119218 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 290814780637980917760 (by norm_num) 47 0.119218 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 0 0.011296 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.011296 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 104`, regime `b = 1`. -/
theorem shell_tight_104 :
    ((25111345965121788241104 : ℚ) : ℝ) * (((47 : ℝ) + 0.119218) - (((0 : ℕ) : ℝ) + 0.011515))
      ≤ ∑ p ∈ shellPrimes highN 104, Real.log (sigma p 104) := by
  apply shell_contribution_ge_tight 104 1 25111345965121788241104 (((47 : ℝ) + 0.119218)) ((((0 : ℕ) : ℝ) + 0.011515)) 290814780637980917760
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.119218 : ℝ) by norm_num)
      (show (0.119218 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 290814780637980917760 (by norm_num) 47 0.119218 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 0 0.011515 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.011515 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 105`, regime `b = 1`. -/
theorem shell_tight_105 :
    ((24635682878768773153387 : ℚ) : ℝ) * (((47 : ℝ) + 0.119218) - (((0 : ℕ) : ℝ) + 0.011736))
      ≤ ∑ p ∈ shellPrimes highN 105, Real.log (sigma p 105) := by
  apply shell_contribution_ge_tight 105 1 24635682878768773153387 (((47 : ℝ) + 0.119218)) ((((0 : ℕ) : ℝ) + 0.011736)) 290814780637980917760
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.119218 : ℝ) by norm_num)
      (show (0.119218 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 290814780637980917760 (by norm_num) 47 0.119218 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 0 0.011736 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.011736 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 106`, regime `b = 1`. -/
theorem shell_tight_106 :
    ((24173335699776170338227 : ℚ) : ℝ) * (((47 : ℝ) + 0.812365) - (((0 : ℕ) : ℝ) + 0.023776))
      ≤ ∑ p ∈ shellPrimes highN 106, Real.log (sigma p 106) := by
  apply shell_contribution_ge_tight 106 1 24173335699776170338227 (((47 : ℝ) + 0.812365)) ((((0 : ℕ) : ℝ) + 0.023776)) 581629561275961835520
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.812365 : ℝ) by norm_num)
      (show (0.812365 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 581629561275961835520 (by norm_num) 47 0.812365 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 0 0.023776 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.023776 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 107`, regime `b = 1`. -/
theorem shell_tight_107 :
    ((23723812330917237699776 : ℚ) : ℝ) * (((48 : ℝ) + 0.505512) - (((0 : ℕ) : ℝ) + 0.047870))
      ≤ ∑ p ∈ shellPrimes highN 107, Real.log (sigma p 107) := by
  apply shell_contribution_ge_tight 107 1 23723812330917237699776 (((48 : ℝ) + 0.505512)) ((((0 : ℕ) : ℝ) + 0.047870)) 1163259122551923671040
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.505512 : ℝ) by norm_num)
      (show (0.505512 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 1163259122551923671040 (by norm_num) 48 0.505512 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 0 0.047870 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.047870 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 108`, regime `b = 1`. -/
theorem shell_tight_108 :
    ((23286642988103507957707 : ℚ) : ℝ) * (((48 : ℝ) + 0.505512) - (((0 : ℕ) : ℝ) + 0.048747))
      ≤ ∑ p ∈ shellPrimes highN 108, Real.log (sigma p 108) := by
  apply shell_contribution_ge_tight 108 1 23286642988103507957707 (((48 : ℝ) + 0.505512)) ((((0 : ℕ) : ℝ) + 0.048747)) 1163259122551923671040
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.505512 : ℝ) by norm_num)
      (show (0.505512 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 1163259122551923671040 (by norm_num) 48 0.505512 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 0 0.048747 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.048747 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 109`, regime `b = 1`. -/
theorem shell_tight_109 :
    ((22861379824787552314629 : ℚ) : ℝ) * (((49 : ℝ) + 0.198659) - (((0 : ℕ) : ℝ) + 0.096915))
      ≤ ∑ p ∈ shellPrimes highN 109, Real.log (sigma p 109) := by
  apply shell_contribution_ge_tight 109 1 22861379824787552314629 (((49 : ℝ) + 0.198659)) ((((0 : ℕ) : ℝ) + 0.096915)) 2326518245103847342080
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.198659 : ℝ) by norm_num)
      (show (0.198659 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 2326518245103847342080 (by norm_num) 49 0.198659 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 0 0.096915 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.096915 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 110`, regime `b = 1`. -/
theorem shell_tight_110 :
    ((22447594238079464818599 : ℚ) : ℝ) * (((49 : ℝ) + 0.198659) - (((0 : ℕ) : ℝ) + 0.098616))
      ≤ ∑ p ∈ shellPrimes highN 110, Real.log (sigma p 110) := by
  apply shell_contribution_ge_tight 110 1 22447594238079464818599 (((49 : ℝ) + 0.198659)) ((((0 : ℕ) : ℝ) + 0.098616)) 2326518245103847342080
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.198659 : ℝ) by norm_num)
      (show (0.198659 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 2326518245103847342080 (by norm_num) 49 0.198659 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 0 0.098616 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.098616 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 111`, regime `b = 1`. -/
theorem shell_tight_111 :
    ((22044877369027909920049 : ℚ) : ℝ) * (((49 : ℝ) + 0.891806) - (((0 : ℕ) : ℝ) + 0.191506))
      ≤ ∑ p ∈ shellPrimes highN 111, Real.log (sigma p 111) := by
  apply shell_contribution_ge_tight 111 1 22044877369027909920049 (((49 : ℝ) + 0.891806)) ((((0 : ℕ) : ℝ) + 0.191506)) 4653036490207694684160
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.891806 : ℝ) by norm_num)
      (show (0.891806 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 4653036490207694684160 (by norm_num) 49 0.891806 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 0 0.191506 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.191506 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 112`, regime `b = 1`. -/
theorem shell_tight_112 :
    ((21652838026167713842746 : ℚ) : ℝ) * (((49 : ℝ) + 0.891806) - (((0 : ℕ) : ℝ) + 0.194656))
      ≤ ∑ p ∈ shellPrimes highN 112, Real.log (sigma p 112) := by
  apply shell_contribution_ge_tight 112 1 21652838026167713842746 (((49 : ℝ) + 0.891806)) ((((0 : ℕ) : ℝ) + 0.194656)) 4653036490207694684160
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.891806 : ℝ) by norm_num)
      (show (0.891806 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 4653036490207694684160 (by norm_num) 49 0.891806 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 0 0.194656 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.194656 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 113`, regime `b = 1`. -/
theorem shell_tight_113 :
    ((21271102654062792450823 : ℚ) : ℝ) * (((50 : ℝ) + 0.584954) - (((0 : ℕ) : ℝ) + 0.362905))
      ≤ ∑ p ∈ shellPrimes highN 113, Real.log (sigma p 113) := by
  apply shell_contribution_ge_tight 113 1 21271102654062792450823 (((50 : ℝ) + 0.584954)) ((((0 : ℕ) : ℝ) + 0.362905)) 9306072980415389368320
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
  · apply log_le_of_real _ _ 0 0.362905 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.362905 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 114`, regime `b = 1`. -/
theorem shell_tight_114 :
    ((20899313146370885631295 : ℚ) : ℝ) * (((50 : ℝ) + 0.584954) - (((0 : ℕ) : ℝ) + 0.368304))
      ≤ ∑ p ∈ shellPrimes highN 114, Real.log (sigma p 114) := by
  apply shell_contribution_ge_tight 114 1 20899313146370885631295 (((50 : ℝ) + 0.584954)) ((((0 : ℕ) : ℝ) + 0.368304)) 9306072980415389368320
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
  · apply log_le_of_real _ _ 0 0.368304 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.368304 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

end Erdos320
