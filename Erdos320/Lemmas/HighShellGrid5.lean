import Erdos320.Lemmas.HighShellTight

/-!
# High-finite-input tight per-shell ledger, grid file 5/8

Machine-generated tight contribution lemmas `shell_tight_77`..`shell_tight_95`, each a clone of the proven per-shell template `shell_contribution_ge_tight` from `HighShellTight.lean`.
Each shell's literals (`Pm`, `sL`, `ℓ`, `pen`) are Lean-verified by the `norm_num`/`native_decide` bullet discharges; nothing is assumed.
-/

namespace Erdos320

open Finset

set_option maxHeartbeats 4000000 in
/-- Shell `m = 77`, regime `b = 1`. -/
theorem shell_tight_77 :
    ((45717309148593725037957 : ℚ) : ℝ) * (((37 : ℝ) + 0.402276) - (((0 : ℕ) : ℝ) + 0.000001))
      ≤ ∑ p ∈ shellPrimes highN 77, Real.log (sigma p 77) := by
  apply shell_contribution_ge_tight 77 1 45717309148593725037957 (((37 : ℝ) + 0.402276)) ((((0 : ℕ) : ℝ) + 0.000001)) 17522758873251840
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.402276 : ℝ) by norm_num)
      (show (0.402276 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 17522758873251840 (by norm_num) 37 0.402276 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 0 0.000001 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.000001 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 78`, regime `b = 1`. -/
theorem shell_tight_78 :
    ((44559068915503747181745 : ℚ) : ℝ) * (((37 : ℝ) + 0.409367) - (((0 : ℕ) : ℝ) + 0.000001))
      ≤ ∑ p ∈ shellPrimes highN 78, Real.log (sigma p 78) := by
  apply shell_contribution_ge_tight 78 1 44559068915503747181745 (((37 : ℝ) + 0.409367)) ((((0 : ℕ) : ℝ) + 0.000001)) 17647454272880640
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.409367 : ℝ) by norm_num)
      (show (0.409367 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 17647454272880640 (by norm_num) 37 0.409367 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 0 0.000001 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.000001 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 79`, regime `b = 1`. -/
theorem shell_tight_79 :
    ((43444153108519236956150 : ℚ) : ℝ) * (((38 : ℝ) + 0.102515) - (((0 : ℕ) : ℝ) + 0.000001))
      ≤ ∑ p ∈ shellPrimes highN 79, Real.log (sigma p 79) := by
  apply shell_contribution_ge_tight 79 1 43444153108519236956150 (((38 : ℝ) + 0.102515)) ((((0 : ℕ) : ℝ) + 0.000001)) 35294908545761280
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.102515 : ℝ) by norm_num)
      (show (0.102515 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 35294908545761280 (by norm_num) 38 0.102515 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 0 0.000001 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.000001 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 80`, regime `b = 1`. -/
theorem shell_tight_80 :
    ((42370427292491119290867 : ℚ) : ℝ) * (((38 : ℝ) + 0.108304) - (((0 : ℕ) : ℝ) + 0.000001))
      ≤ ∑ p ∈ shellPrimes highN 80, Real.log (sigma p 80) := by
  apply shell_contribution_ge_tight 80 1 42370427292491119290867 (((38 : ℝ) + 0.108304)) ((((0 : ℕ) : ℝ) + 0.000001)) 35499851152097280
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.108304 : ℝ) by norm_num)
      (show (0.108304 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 35499851152097280 (by norm_num) 38 0.108304 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 0 0.000001 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.000001 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 81`, regime `b = 1`. -/
theorem shell_tight_81 :
    ((41335887884640114598365 : ℚ) : ℝ) * (((38 : ℝ) + 0.801452) - (((0 : ℕ) : ℝ) + 0.000002))
      ≤ ∑ p ∈ shellPrimes highN 81, Real.log (sigma p 81) := by
  apply shell_contribution_ge_tight 81 1 41335887884640114598365 (((38 : ℝ) + 0.801452)) ((((0 : ℕ) : ℝ) + 0.000002)) 70999702304194560
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.801452 : ℝ) by norm_num)
      (show (0.801452 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 70999702304194560 (by norm_num) 38 0.801452 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 0 0.000002 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.000002 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 82`, regime `b = 1`. -/
theorem shell_tight_82 :
    ((40338651196772256046871 : ℚ) : ℝ) * (((39 : ℝ) + 0.494599) - (((0 : ℕ) : ℝ) + 0.000004))
      ≤ ∑ p ∈ shellPrimes highN 82, Real.log (sigma p 82) := by
  apply shell_contribution_ge_tight 82 1 40338651196772256046871 (((39 : ℝ) + 0.494599)) ((((0 : ℕ) : ℝ) + 0.000004)) 141999404608389120
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.494599 : ℝ) by norm_num)
      (show (0.494599 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 141999404608389120 (by norm_num) 39 0.494599 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 0 0.000004 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.000004 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 83`, regime `b = 1`. -/
theorem shell_tight_83 :
    ((39376945238369427206189 : ℚ) : ℝ) * (((40 : ℝ) + 0.187746) - (((0 : ℕ) : ℝ) + 0.000008))
      ≤ ∑ p ∈ shellPrimes highN 83, Real.log (sigma p 83) := by
  apply shell_contribution_ge_tight 83 1 39376945238369427206189 (((40 : ℝ) + 0.187746)) ((((0 : ℕ) : ℝ) + 0.000008)) 283998809216778240
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.187746 : ℝ) by norm_num)
      (show (0.187746 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 283998809216778240 (by norm_num) 40 0.187746 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 0 0.000008 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.000008 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 84`, regime `b = 1`. -/
theorem shell_tight_84 :
    ((38449101975327814983127 : ℚ) : ℝ) * (((40 : ℝ) + 0.187746) - (((0 : ℕ) : ℝ) + 0.000008))
      ≤ ∑ p ∈ shellPrimes highN 84, Real.log (sigma p 84) := by
  apply shell_contribution_ge_tight 84 1 38449101975327814983127 (((40 : ℝ) + 0.187746)) ((((0 : ℕ) : ℝ) + 0.000008)) 283998809216778240
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.187746 : ℝ) by norm_num)
      (show (0.187746 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 283998809216778240 (by norm_num) 40 0.187746 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 0 0.000008 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.000008 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 85`, regime `b = 1`. -/
theorem shell_tight_85 :
    ((37553550959346484421469 : ℚ) : ℝ) * (((40 : ℝ) + 0.187746) - (((0 : ℕ) : ℝ) + 0.000008))
      ≤ ∑ p ∈ shellPrimes highN 85, Real.log (sigma p 85) := by
  apply shell_contribution_ge_tight 85 1 37553550959346484421469 (((40 : ℝ) + 0.187746)) ((((0 : ℕ) : ℝ) + 0.000008)) 283998809216778240
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.187746 : ℝ) by norm_num)
      (show (0.187746 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 283998809216778240 (by norm_num) 40 0.187746 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 0 0.000008 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.000008 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 86`, regime `b = 1`. -/
theorem shell_tight_86 :
    ((36688810691452652324579 : ℚ) : ℝ) * (((40 : ℝ) + 0.880893) - (((0 : ℕ) : ℝ) + 0.000016))
      ≤ ∑ p ∈ shellPrimes highN 86, Real.log (sigma p 86) := by
  apply shell_contribution_ge_tight 86 1 36688810691452652324579 (((40 : ℝ) + 0.880893)) ((((0 : ℕ) : ℝ) + 0.000016)) 567997618433556480
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.880893 : ℝ) by norm_num)
      (show (0.880893 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 567997618433556480 (by norm_num) 40 0.880893 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 0 0.000016 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.000016 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 87`, regime `b = 1`. -/
theorem shell_tight_87 :
    ((35853484332773575463372 : ℚ) : ℝ) * (((41 : ℝ) + 0.574040) - (((0 : ℕ) : ℝ) + 0.000032))
      ≤ ∑ p ∈ shellPrimes highN 87, Real.log (sigma p 87) := by
  apply shell_contribution_ge_tight 87 1 35853484332773575463372 (((41 : ℝ) + 0.574040)) ((((0 : ℕ) : ℝ) + 0.000032)) 1135995236867112960
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.574040 : ℝ) by norm_num)
      (show (0.574040 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 1135995236867112960 (by norm_num) 41 0.574040 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 0 0.000032 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.000032 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 88`, regime `b = 1`. -/
theorem shell_tight_88 :
    ((35046253051019276950721 : ℚ) : ℝ) * (((41 : ℝ) + 0.574040) - (((0 : ℕ) : ℝ) + 0.000033))
      ≤ ∑ p ∈ shellPrimes highN 88, Real.log (sigma p 88) := by
  apply shell_contribution_ge_tight 88 1 35046253051019276950721 (((41 : ℝ) + 0.574040)) ((((0 : ℕ) : ℝ) + 0.000033)) 1135995236867112960
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.574040 : ℝ) by norm_num)
      (show (0.574040 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 1135995236867112960 (by norm_num) 41 0.574040 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 0 0.000033 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.000033 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 89`, regime `b = 1`. -/
theorem shell_tight_89 :
    ((34265871574473230013277 : ℚ) : ℝ) * (((42 : ℝ) + 0.267187) - (((0 : ℕ) : ℝ) + 0.000067))
      ≤ ∑ p ∈ shellPrimes highN 89, Real.log (sigma p 89) := by
  apply shell_contribution_ge_tight 89 1 34265871574473230013277 (((42 : ℝ) + 0.267187)) ((((0 : ℕ) : ℝ) + 0.000067)) 2271990473734225920
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.267187 : ℝ) by norm_num)
      (show (0.267187 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 2271990473734225920 (by norm_num) 42 0.267187 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 0 0.000067 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.000067 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 90`, regime `b = 1`. -/
theorem shell_tight_90 :
    ((33511162057482963843649 : ℚ) : ℝ) * (((42 : ℝ) + 0.267187) - (((0 : ℕ) : ℝ) + 0.000068))
      ≤ ∑ p ∈ shellPrimes highN 90, Real.log (sigma p 90) := by
  apply shell_contribution_ge_tight 90 1 33511162057482963843649 (((42 : ℝ) + 0.267187)) ((((0 : ℕ) : ℝ) + 0.000068)) 2271990473734225920
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.267187 : ℝ) by norm_num)
      (show (0.267187 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 2271990473734225920 (by norm_num) 42 0.267187 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 0 0.000068 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.000068 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 91`, regime `b = 1`. -/
theorem shell_tight_91 :
    ((32781011458960966018146 : ℚ) : ℝ) * (((42 : ℝ) + 0.267187) - (((0 : ℕ) : ℝ) + 0.000070))
      ≤ ∑ p ∈ shellPrimes highN 91, Real.log (sigma p 91) := by
  apply shell_contribution_ge_tight 91 1 32781011458960966018146 (((42 : ℝ) + 0.267187)) ((((0 : ℕ) : ℝ) + 0.000070)) 2271990473734225920
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.267187 : ℝ) by norm_num)
      (show (0.267187 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 2271990473734225920 (by norm_num) 42 0.267187 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 0 0.000070 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.000070 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 92`, regime `b = 1`. -/
theorem shell_tight_92 :
    ((32074365682726568501701 : ℚ) : ℝ) * (((42 : ℝ) + 0.960335) - (((0 : ℕ) : ℝ) + 0.000142))
      ≤ ∑ p ∈ shellPrimes highN 92, Real.log (sigma p 92) := by
  apply shell_contribution_ge_tight 92 1 32074365682726568501701 (((42 : ℝ) + 0.960335)) ((((0 : ℕ) : ℝ) + 0.000142)) 4543980947468451840
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.960335 : ℝ) by norm_num)
      (show (0.960335 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 4543980947468451840 (by norm_num) 42 0.960335 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 0 0.000142 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.000142 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 93`, regime `b = 1`. -/
theorem shell_tight_93 :
    ((31390227100242009477919 : ℚ) : ℝ) * (((43 : ℝ) + 0.653482) - (((0 : ℕ) : ℝ) + 0.000290))
      ≤ ∑ p ∈ shellPrimes highN 93, Real.log (sigma p 93) := by
  apply shell_contribution_ge_tight 93 1 31390227100242009477919 (((43 : ℝ) + 0.653482)) ((((0 : ℕ) : ℝ) + 0.000290)) 9087961894936903680
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.653482 : ℝ) by norm_num)
      (show (0.653482 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 9087961894936903680 (by norm_num) 43 0.653482 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · apply log_le_of_real _ _ 0 0.000290 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.000290 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 94`, regime `b = 1`. -/
theorem shell_tight_94 :
    ((30727650153431976110885 : ℚ) : ℝ) * (((44 : ℝ) + 0.346629) - (((0 : ℕ) : ℝ) + 0.000592))
      ≤ ∑ p ∈ shellPrimes highN 94, Real.log (sigma p 94) := by
  apply shell_contribution_ge_tight 94 1 30727650153431976110885 (((44 : ℝ) + 0.346629)) ((((0 : ℕ) : ℝ) + 0.000592)) 18175923789873807360
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
  · apply log_le_of_real _ _ 0 0.000592 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.000592 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
/-- Shell `m = 95`, regime `b = 1`. -/
theorem shell_tight_95 :
    ((30085738566740359092618 : ℚ) : ℝ) * (((44 : ℝ) + 0.346629) - (((0 : ℕ) : ℝ) + 0.000604))
      ≤ ∑ p ∈ shellPrimes highN 95, Real.log (sigma p 95) := by
  apply shell_contribution_ge_tight 95 1 30085738566740359092618 (((44 : ℝ) + 0.346629)) ((((0 : ℕ) : ℝ) + 0.000604)) 18175923789873807360
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
  · apply log_le_of_real _ _ 0 0.000604 _ _
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.000604 : ℝ) by norm_num) 12)
    all_goals
      first
      | positivity
      | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

end Erdos320
