import Erdos320.Lemmas.HighShellTight

/-!
# High finite input: tight per-shell ledger, grid file 3/8

Tight per-shell contribution lemmas `shell_tight_39`..`shell_tight_57`, one per
prime shell `m = 39..57` at `N₁ = ⌊e⁶⁵⌋`, feeding the high finite input
(`comp:high`) — a proved theorem, not an axiom. Every shell here is in collision
regime `b = 0`, so the penalty `pen` vanishes.

Each invokes the reusable lower bound `shell_contribution_ge_tight`
(`HighShellTight.lean`) to prove
`Pₘ·(ℓ − pen) ≤ ∑_{p ∈ shellPrimes highN m} log σ(p, m)`, where `Pₘ` is the tight
Dusart prime-count floor, `ℓ` a `log(sL)` lower bound, `pen` the `b`-collision
penalty (`eq:high-collision-bound`), and `sL` a BGMS lower bound on `S m`. The
literals are discharged in place by `norm_num`/`native_decide` with the
`exp`-comparison log bound `log_ge_of` for `ℓ` (`pen = 0`, so no penalty bound is
needed). The eight grid files together cover the 154-shell ledger.
-/

namespace Erdos320

open Finset

set_option maxHeartbeats 4000000 in
/-- Shell `m = 39`, regime `b = 0`. -/
theorem shell_tight_39 :
    ((175583514892663319199331 : ℚ) : ℝ) * (((21 : ℝ) + 0.363144) - 0)
      ≤ ∑ p ∈ shellPrimes highN 39, Real.log (sigma p 39) := by
  apply shell_contribution_ge_tight 39 0 175583514892663319199331 (((21 : ℝ) + 0.363144)) (0) 1896251392
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.363144 : ℝ) by norm_num)
      (show (0.363144 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 1896251392 (by norm_num) 21 0.363144 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · simp

set_option maxHeartbeats 4000000 in
/-- Shell `m = 40`, regime `b = 0`. -/
theorem shell_tight_40 :
    ((167049500565517738112939 : ℚ) : ℝ) * (((21 : ℝ) + 0.380056) - 0)
      ≤ ∑ p ∈ shellPrimes highN 40, Real.log (sigma p 40) := by
  apply shell_contribution_ge_tight 40 0 167049500565517738112939 (((21 : ℝ) + 0.380056)) (0) 1928593408
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.380056 : ℝ) by norm_num)
      (show (0.380056 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 1928593408 (by norm_num) 21 0.380056 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · simp

set_option maxHeartbeats 4000000 in
/-- Shell `m = 41`, regime `b = 0`. -/
theorem shell_tight_41 :
    ((159122706896002419847966 : ℚ) : ℝ) * (((22 : ℝ) + 0.073203) - 0)
      ≤ ∑ p ∈ shellPrimes highN 41, Real.log (sigma p 41) := by
  apply shell_contribution_ge_tight 41 0 159122706896002419847966 (((22 : ℝ) + 0.073203)) (0) 3857186816
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.073203 : ℝ) by norm_num)
      (show (0.073203 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 3857186816 (by norm_num) 22 0.073203 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · simp

set_option maxHeartbeats 4000000 in
/-- Shell `m = 42`, regime `b = 0`. -/
theorem shell_tight_42 :
    ((151746828350571358151046 : ℚ) : ℝ) * (((22 : ℝ) + 0.090886) - 0)
      ≤ ∑ p ∈ shellPrimes highN 42, Real.log (sigma p 42) := by
  apply shell_contribution_ge_tight 42 0 151746828350571358151046 (((22 : ℝ) + 0.090886)) (0) 3925999616
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.090886 : ℝ) by norm_num)
      (show (0.090886 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 3925999616 (by norm_num) 22 0.090886 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · simp

set_option maxHeartbeats 4000000 in
/-- Shell `m = 43`, regime `b = 0`. -/
theorem shell_tight_43 :
    ((144871943805377160384026 : ℚ) : ℝ) * (((22 : ℝ) + 0.784034) - 0)
      ≤ ∑ p ∈ shellPrimes highN 43, Real.log (sigma p 43) := by
  apply shell_contribution_ge_tight 43 0 144871943805377160384026 (((22 : ℝ) + 0.784034)) (0) 7851999232
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.784034 : ℝ) by norm_num)
      (show (0.784034 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 7851999232 (by norm_num) 22 0.784034 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · simp

set_option maxHeartbeats 4000000 in
/-- Shell `m = 44`, regime `b = 0`. -/
theorem shell_tight_44 :
    ((138453660628244410653994 : ℚ) : ℝ) * (((23 : ℝ) + 0.244586) - 0)
      ≤ ∑ p ∈ shellPrimes highN 44, Real.log (sigma p 44) := by
  apply shell_contribution_ge_tight 44 0 138453660628244410653994 (((23 : ℝ) + 0.244586)) (0) 12445024256
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.244586 : ℝ) by norm_num)
      (show (0.244586 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 12445024256 (by norm_num) 23 0.244586 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · simp

set_option maxHeartbeats 4000000 in
/-- Shell `m = 45`, regime `b = 0`. -/
theorem shell_tight_45 :
    ((132452401848142894144205 : ℚ) : ℝ) * (((23 : ℝ) + 0.257478) - 0)
      ≤ ∑ p ∈ shellPrimes highN 45, Real.log (sigma p 45) := by
  apply shell_contribution_ge_tight 45 0 132452401848142894144205 (((23 : ℝ) + 0.257478)) (0) 12606504960
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.257478 : ℝ) by norm_num)
      (show (0.257478 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 12606504960 (by norm_num) 23 0.257478 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · simp

set_option maxHeartbeats 4000000 in
/-- Shell `m = 46`, regime `b = 0`. -/
theorem shell_tight_46 :
    ((126832787637248154170442 : ℚ) : ℝ) * (((23 : ℝ) + 0.950625) - 0)
      ≤ ∑ p ∈ shellPrimes highN 46, Real.log (sigma p 46) := by
  apply shell_contribution_ge_tight 46 0 126832787637248154170442 (((23 : ℝ) + 0.950625)) (0) 25213009920
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.950625 : ℝ) by norm_num)
      (show (0.950625 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 25213009920 (by norm_num) 23 0.950625 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · simp

set_option maxHeartbeats 4000000 in
/-- Shell `m = 47`, regime `b = 0`. -/
theorem shell_tight_47 :
    ((121563114130847976571523 : ℚ) : ℝ) * (((24 : ℝ) + 0.643773) - 0)
      ≤ ∑ p ∈ shellPrimes highN 47, Real.log (sigma p 47) := by
  apply shell_contribution_ge_tight 47 0 121563114130847976571523 (((24 : ℝ) + 0.643773)) (0) 50426019840
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.643773 : ℝ) by norm_num)
      (show (0.643773 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 50426019840 (by norm_num) 24 0.643773 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · simp

set_option maxHeartbeats 4000000 in
/-- Shell `m = 48`, regime `b = 0`. -/
theorem shell_tight_48 :
    ((116614903115512374438378 : ℚ) : ℝ) * (((24 : ℝ) + 0.661625) - 0)
      ≤ ∑ p ∈ shellPrimes highN 48, Real.log (sigma p 48) := by
  apply shell_contribution_ge_tight 48 0 116614903115512374438378 (((24 : ℝ) + 0.661625)) (0) 51334348800
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.661625 : ℝ) by norm_num)
      (show (0.661625 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 51334348800 (by norm_num) 24 0.661625 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · simp

set_option maxHeartbeats 4000000 in
/-- Shell `m = 49`, regime `b = 0`. -/
theorem shell_tight_49 :
    ((111962519906591878062898 : ℚ) : ℝ) * (((25 : ℝ) + 0.354773) - 0)
      ≤ ∑ p ∈ shellPrimes highN 49, Real.log (sigma p 49) := by
  apply shell_contribution_ge_tight 49 0 111962519906591878062898 (((25 : ℝ) + 0.354773)) (0) 102668697600
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.354773 : ℝ) by norm_num)
      (show (0.354773 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 102668697600 (by norm_num) 25 0.354773 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · simp

set_option maxHeartbeats 4000000 in
/-- Shell `m = 50`, regime `b = 0`. -/
theorem shell_tight_50 :
    ((107582832285144133210517 : ℚ) : ℝ) * (((26 : ℝ) + 0.047920) - 0)
      ≤ ∑ p ∈ shellPrimes highN 50, Real.log (sigma p 50) := by
  apply shell_contribution_ge_tight 50 0 107582832285144133210517 (((26 : ℝ) + 0.047920)) (0) 205337395200
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.047920 : ℝ) by norm_num)
      (show (0.047920 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 205337395200 (by norm_num) 26 0.047920 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · simp

set_option maxHeartbeats 4000000 in
/-- Shell `m = 51`, regime `b = 0`. -/
theorem shell_tight_51 :
    ((103454928824168765899709 : ℚ) : ℝ) * (((26 : ℝ) + 0.741067) - 0)
      ≤ ∑ p ∈ shellPrimes highN 51, Real.log (sigma p 51) := by
  apply shell_contribution_ge_tight 51 0 103454928824168765899709 (((26 : ℝ) + 0.741067)) (0) 410674790400
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.741067 : ℝ) by norm_num)
      (show (0.741067 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 410674790400 (by norm_num) 26 0.741067 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · simp

set_option maxHeartbeats 4000000 in
/-- Shell `m = 52`, regime `b = 0`. -/
theorem shell_tight_52 :
    ((99559865128899173253671 : ℚ) : ℝ) * (((27 : ℝ) + 0.070187) - 0)
      ≤ ∑ p ∈ shellPrimes highN 52, Real.log (sigma p 52) := by
  apply shell_contribution_ge_tight 52 0 99559865128899173253671 (((27 : ℝ) + 0.070187)) (0) 570733363200
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.070187 : ℝ) by norm_num)
      (show (0.070187 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 570733363200 (by norm_num) 27 0.070187 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · simp

set_option maxHeartbeats 4000000 in
/-- Shell `m = 53`, regime `b = 0`. -/
theorem shell_tight_53 :
    ((95880446958121839179935 : ℚ) : ℝ) * (((27 : ℝ) + 0.763335) - 0)
      ≤ ∑ p ∈ shellPrimes highN 53, Real.log (sigma p 53) := by
  apply shell_contribution_ge_tight 53 0 95880446958121839179935 (((27 : ℝ) + 0.763335)) (0) 1141466726400
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.763335 : ℝ) by norm_num)
      (show (0.763335 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 1141466726400 (by norm_num) 27 0.763335 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · simp

set_option maxHeartbeats 4000000 in
/-- Shell `m = 54`, regime `b = 0`. -/
theorem shell_tight_54 :
    ((92401037304455107133068 : ℚ) : ℝ) * (((28 : ℝ) + 0.173974) - 0)
      ≤ ∑ p ∈ shellPrimes highN 54, Real.log (sigma p 54) := by
  apply shell_contribution_ge_tight 54 0 92401037304455107133068 (((28 : ℝ) + 0.173974)) (0) 1721081528320
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.173974 : ℝ) by norm_num)
      (show (0.173974 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 1721081528320 (by norm_num) 28 0.173974 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · simp

set_option maxHeartbeats 4000000 in
/-- Shell `m = 55`, regime `b = 0`. -/
theorem shell_tight_55 :
    ((89107394638659778999210 : ℚ) : ℝ) * (((28 : ℝ) + 0.191551) - 0)
      ≤ ∑ p ∈ shellPrimes highN 55, Real.log (sigma p 55) := by
  apply shell_contribution_ge_tight 55 0 89107394638659778999210 (((28 : ℝ) + 0.191551)) (0) 1751601381376
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.191551 : ℝ) by norm_num)
      (show (0.191551 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 1751601381376 (by norm_num) 28 0.191551 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · simp

set_option maxHeartbeats 4000000 in
/-- Shell `m = 56`, regime `b = 0`. -/
theorem shell_tight_56 :
    ((85986520284808707222056 : ℚ) : ℝ) * (((28 : ℝ) + 0.200313) - 0)
      ≤ ∑ p ∈ shellPrimes highN 56, Real.log (sigma p 56) := by
  apply shell_contribution_ge_tight 56 0 85986520284808707222056 (((28 : ℝ) + 0.200313)) (0) 1767017021440
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.200313 : ℝ) by norm_num)
      (show (0.200313 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 1767017021440 (by norm_num) 28 0.200313 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · simp

set_option maxHeartbeats 4000000 in
/-- Shell `m = 57`, regime `b = 0`. -/
theorem shell_tight_57 :
    ((83026535862131544755656 : ℚ) : ℝ) * (((28 : ℝ) + 0.893461) - 0)
      ≤ ∑ p ∈ shellPrimes highN 57, Real.log (sigma p 57) := by
  apply shell_contribution_ge_tight 57 0 83026535862131544755656 (((28 : ℝ) + 0.893461)) (0) 3534034042880
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.893461 : ℝ) by norm_num)
      (show (0.893461 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 3534034042880 (by norm_num) 28 0.893461 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · simp

end Erdos320
