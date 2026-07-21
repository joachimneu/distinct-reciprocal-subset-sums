import Erdos320.Lemmas.HighShellTight

/-!
# High-finite-input tight per-shell ledger, grid file 1/8

Machine-generated (`gen_shells.py`) tight contribution lemmas `shell_tight_1`..`shell_tight_19`, cloning the proven three-shell template of `HighShellTight.lean` (`shell_contribution_ge_tight`).
Each shell's literals (`Pm`, `sL`, `ℓ`, `pen`) are Lean-verified by the `norm_num`/`native_decide` bullet discharges; nothing is assumed.
-/

namespace Erdos320

open Finset

set_option maxHeartbeats 4000000 in
/-- Shell `m = 1`, regime `b = 0`. -/
theorem shell_tight_1 :
    ((130335101134591742971392711 : ℚ) : ℝ) * ((logNatLo 2 : ℝ) - 0)
      ≤ ∑ p ∈ shellPrimes highN 1, Real.log (sigma p 1) := by
  apply shell_contribution_ge_tight 1 0 130335101134591742971392711 ((logNatLo 2 : ℝ)) (0) 2
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
  · exact logNat_lower 2 (by norm_num) (by norm_num)
  · simp

set_option maxHeartbeats 4000000 in
/-- Shell `m = 2`, regime `b = 0`. -/
theorem shell_tight_2 :
    ((43903885284047038401140085 : ℚ) : ℝ) * ((logNatLo 4 : ℝ) - 0)
      ≤ ∑ p ∈ shellPrimes highN 2, Real.log (sigma p 2) := by
  apply shell_contribution_ge_tight 2 0 43903885284047038401140085 ((logNatLo 4 : ℝ)) (0) 4
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
  · exact logNat_lower 4 (by norm_num) (by norm_num)
  · simp

set_option maxHeartbeats 4000000 in
/-- Shell `m = 3`, regime `b = 0`. -/
theorem shell_tight_3 :
    ((22086459339424609926699217 : ℚ) : ℝ) * ((logNatLo 8 : ℝ) - 0)
      ≤ ∑ p ∈ shellPrimes highN 3, Real.log (sigma p 3) := by
  apply shell_contribution_ge_tight 3 0 22086459339424609926699217 ((logNatLo 8 : ℝ)) (0) 8
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
  · exact logNat_lower 8 (by norm_num) (by norm_num)
  · simp

set_option maxHeartbeats 4000000 in
/-- Shell `m = 4`, regime `b = 0`. -/
theorem shell_tight_4 :
    ((13308916275517358886755658 : ℚ) : ℝ) * ((logNatLo 16 : ℝ) - 0)
      ≤ ∑ p ∈ shellPrimes highN 4, Real.log (sigma p 4) := by
  apply shell_contribution_ge_tight 4 0 13308916275517358886755658 ((logNatLo 16 : ℝ)) (0) 16
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
  · exact logNat_lower 16 (by norm_num) (by norm_num)
  · simp

set_option maxHeartbeats 4000000 in
/-- Shell `m = 5`, regime `b = 0`. -/
theorem shell_tight_5 :
    ((8901904464121883709779871 : ℚ) : ℝ) * ((logNatLo 32 : ℝ) - 0)
      ≤ ∑ p ∈ shellPrimes highN 5, Real.log (sigma p 5) := by
  apply shell_contribution_ge_tight 5 0 8901904464121883709779871 ((logNatLo 32 : ℝ)) (0) 32
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
  · exact logNat_lower 32 (by norm_num) (by norm_num)
  · simp

set_option maxHeartbeats 4000000 in
/-- Shell `m = 6`, regime `b = 0`. -/
theorem shell_tight_6 :
    ((6375450873868716212598810 : ℚ) : ℝ) * ((logNatLo 52 : ℝ) - 0)
      ≤ ∑ p ∈ shellPrimes highN 6, Real.log (sigma p 6) := by
  apply shell_contribution_ge_tight 6 0 6375450873868716212598810 ((logNatLo 52 : ℝ)) (0) 52
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
  · exact logNat_lower 52 (by norm_num) (by norm_num)
  · simp

set_option maxHeartbeats 4000000 in
/-- Shell `m = 7`, regime `b = 0`. -/
theorem shell_tight_7 :
    ((4792227921263671669278521 : ℚ) : ℝ) * ((logNatLo 104 : ℝ) - 0)
      ≤ ∑ p ∈ shellPrimes highN 7, Real.log (sigma p 7) := by
  apply shell_contribution_ge_tight 7 0 4792227921263671669278521 ((logNatLo 104 : ℝ)) (0) 104
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
  · exact logNat_lower 104 (by norm_num) (by norm_num)
  · simp

set_option maxHeartbeats 4000000 in
/-- Shell `m = 8`, regime `b = 0`. -/
theorem shell_tight_8 :
    ((3734378384723773090062943 : ℚ) : ℝ) * (((5 : ℝ) + 0.337538) - 0)
      ≤ ∑ p ∈ shellPrimes highN 8, Real.log (sigma p 8) := by
  apply shell_contribution_ge_tight 8 0 3734378384723773090062943 (((5 : ℝ) + 0.337538)) (0) 208
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.337538 : ℝ) by norm_num)
      (show (0.337538 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 208 (by norm_num) 5 0.337538 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · simp

set_option maxHeartbeats 4000000 in
/-- Shell `m = 9`, regime `b = 0`. -/
theorem shell_tight_9 :
    ((2992447034301634418793078 : ℚ) : ℝ) * (((6 : ℝ) + 0.030685) - 0)
      ≤ ∑ p ∈ shellPrimes highN 9, Real.log (sigma p 9) := by
  apply shell_contribution_ge_tight 9 0 2992447034301634418793078 (((6 : ℝ) + 0.030685)) (0) 416
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.030685 : ℝ) by norm_num)
      (show (0.030685 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 416 (by norm_num) 6 0.030685 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · simp

set_option maxHeartbeats 4000000 in
/-- Shell `m = 10`, regime `b = 0`. -/
theorem shell_tight_10 :
    ((2451939491280506327185505 : ℚ) : ℝ) * (((6 : ℝ) + 0.723832) - 0)
      ≤ ∑ p ∈ shellPrimes highN 10, Real.log (sigma p 10) := by
  apply shell_contribution_ge_tight 10 0 2451939491280506327185505 (((6 : ℝ) + 0.723832)) (0) 832
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.723832 : ℝ) by norm_num)
      (show (0.723832 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 832 (by norm_num) 6 0.723832 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · simp

set_option maxHeartbeats 4000000 in
/-- Shell `m = 11`, regime `b = 0`. -/
theorem shell_tight_11 :
    ((2045941838106167449781592 : ℚ) : ℝ) * (((7 : ℝ) + 0.416979) - 0)
      ≤ ∑ p ∈ shellPrimes highN 11, Real.log (sigma p 11) := by
  apply shell_contribution_ge_tight 11 0 2045941838106167449781592 (((7 : ℝ) + 0.416979)) (0) 1664
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.416979 : ℝ) by norm_num)
      (show (0.416979 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 1664 (by norm_num) 7 0.416979 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · simp

set_option maxHeartbeats 4000000 in
/-- Shell `m = 12`, regime `b = 0`. -/
theorem shell_tight_12 :
    ((1733207623113912589805636 : ℚ) : ℝ) * (((7 : ℝ) + 0.526178) - 0)
      ≤ ∑ p ∈ shellPrimes highN 12, Real.log (sigma p 12) := by
  apply shell_contribution_ge_tight 12 0 1733207623113912589805636 (((7 : ℝ) + 0.526178)) (0) 1856
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.526178 : ℝ) by norm_num)
      (show (0.526178 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 1856 (by norm_num) 7 0.526178 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · simp

set_option maxHeartbeats 4000000 in
/-- Shell `m = 13`, regime `b = 0`. -/
theorem shell_tight_13 :
    ((1487181576630209171731127 : ℚ) : ℝ) * (((8 : ℝ) + 0.219326) - 0)
      ≤ ∑ p ∈ shellPrimes highN 13, Real.log (sigma p 13) := by
  apply shell_contribution_ge_tight 13 0 1487181576630209171731127 (((8 : ℝ) + 0.219326)) (0) 3712
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.219326 : ℝ) by norm_num)
      (show (0.219326 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 3712 (by norm_num) 8 0.219326 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · simp

set_option maxHeartbeats 4000000 in
/-- Shell `m = 14`, regime `b = 0`. -/
theorem shell_tight_14 :
    ((1290136100886233872261381 : ℚ) : ℝ) * (((8 : ℝ) + 0.912473) - 0)
      ≤ ∑ p ∈ shellPrimes highN 14, Real.log (sigma p 14) := by
  apply shell_contribution_ge_tight 14 0 1290136100886233872261381 (((8 : ℝ) + 0.912473)) (0) 7424
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.912473 : ℝ) by norm_num)
      (show (0.912473 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 7424 (by norm_num) 8 0.912473 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · simp

set_option maxHeartbeats 4000000 in
/-- Shell `m = 15`, regime `b = 0`. -/
theorem shell_tight_15 :
    ((1129868341140007262348173 : ℚ) : ℝ) * (((9 : ℝ) + 0.176162) - 0)
      ≤ ∑ p ∈ shellPrimes highN 15, Real.log (sigma p 15) := by
  apply shell_contribution_ge_tight 15 0 1129868341140007262348173 (((9 : ℝ) + 0.176162)) (0) 9664
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.176162 : ℝ) by norm_num)
      (show (0.176162 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 9664 (by norm_num) 9 0.176162 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · simp

set_option maxHeartbeats 4000000 in
/-- Shell `m = 16`, regime `b = 0`. -/
theorem shell_tight_16 :
    ((997754639669026582059512 : ℚ) : ℝ) * (((9 : ℝ) + 0.869310) - 0)
      ≤ ∑ p ∈ shellPrimes highN 16, Real.log (sigma p 16) := by
  apply shell_contribution_ge_tight 16 0 997754639669026582059512 (((9 : ℝ) + 0.869310)) (0) 19328
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.869310 : ℝ) by norm_num)
      (show (0.869310 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 19328 (by norm_num) 9 0.869310 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · simp

set_option maxHeartbeats 4000000 in
/-- Shell `m = 17`, regime `b = 0`. -/
theorem shell_tight_17 :
    ((887560206146485338577252 : ℚ) : ℝ) * (((10 : ℝ) + 0.562457) - 0)
      ≤ ∑ p ∈ shellPrimes highN 17, Real.log (sigma p 17) := by
  apply shell_contribution_ge_tight 17 0 887560206146485338577252 (((10 : ℝ) + 0.562457)) (0) 38656
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.562457 : ℝ) by norm_num)
      (show (0.562457 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 38656 (by norm_num) 10 0.562457 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · simp

set_option maxHeartbeats 4000000 in
/-- Shell `m = 18`, regime `b = 0`. -/
theorem shell_tight_18 :
    ((794686419977607661535071 : ℚ) : ℝ) * (((10 : ℝ) + 0.989757) - 0)
      ≤ ∑ p ∈ shellPrimes highN 18, Real.log (sigma p 18) := by
  apply shell_contribution_ge_tight 18 0 794686419977607661535071 (((10 : ℝ) + 0.989757)) (0) 59264
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.989757 : ℝ) by norm_num)
      (show (0.989757 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 59264 (by norm_num) 10 0.989757 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · simp

set_option maxHeartbeats 4000000 in
/-- Shell `m = 19`, regime `b = 0`. -/
theorem shell_tight_19 :
    ((715681150687561695143264 : ℚ) : ℝ) * (((11 : ℝ) + 0.682904) - 0)
      ≤ ∑ p ∈ shellPrimes highN 19, Real.log (sigma p 19) := by
  apply shell_contribution_ge_tight 19 0 715681150687561695143264 (((11 : ℝ) + 0.682904)) (0) 118528
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.682904 : ℝ) by norm_num)
      (show (0.682904 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 118528 (by norm_num) 11 0.682904 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · simp

end Erdos320
