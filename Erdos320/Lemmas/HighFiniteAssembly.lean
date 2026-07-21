import Erdos320.Lemmas.HighAggregate
import Erdos320.Lemmas.HighShellGrid1
import Erdos320.Lemmas.HighShellGrid2
import Erdos320.Lemmas.HighShellGrid3
import Erdos320.Lemmas.HighShellGrid4
import Erdos320.Lemmas.HighShellGrid5
import Erdos320.Lemmas.HighShellGrid6
import Erdos320.Lemmas.HighShellGrid7
import Erdos320.Lemmas.HighShellGrid8

/-!
# Final assembly of the high finite input `highFiniteInput : 3.2411 < F ⌊e⁶⁵⌋`

Combines the 154 individually-proved grid shells (`shell_tight_1 … shell_tight_154`,
`HighShellGrid1..8.lean`) with the aggregate tail block (`aggregate_lower`,
`HighAggregate.lean`) into the shell-sum lower bound `hK` consumed by
`highFiniteInput_of_shell_sum_ge` (`HighFiniteProof.lean`), discharging
`highFiniteInput_proof : 3.2411 < F ⌊e⁶⁵⌋` as a theorem.

The rational witness is `Krat = 1690292257250233856213705682207391 / 2000000`
(≈ `8.4515·10²⁶`): the 154 grid contributions
(`1489117561155600944906686268008873/2000000`, ≈ `7.4456·10²⁶`) plus the aggregate
`Cagg·(64.447897 − 9.279)` (≈ `1.0059·10²⁶`).  It clears `3.2411·N₁ / 64.999`
(≈ `8.4514·10²⁶`) with margin ≈ `5.98·10²³` in `64.999·Krat`.
-/

namespace Erdos320
open Finset

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
/-- The 154 grid shells sum to at least their combined proved contribution
`1489117561155600944906686268008873/2000000` (≈ `7.4456·10²⁶`).  Each `shell_tight_m` bound is normalized to its
exact rational contribution (`le_of_eq_of_le`, a sum-free `norm_num` identity)
before the linear combination. -/
theorem grid_sum_ge :
    ((1489117561155600944906686268008873/2000000 : ℚ) : ℝ)
      ≤ ∑ m ∈ Finset.Icc 1 154, ∑ p ∈ shellPrimes highN m, Real.log (sigma p m) := by
  rw [
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 153+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 152+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 151+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 150+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 149+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 148+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 147+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 146+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 145+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 144+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 143+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 142+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 141+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 140+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 139+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 138+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 137+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 136+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 135+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 134+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 133+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 132+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 131+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 130+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 129+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 128+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 127+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 126+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 125+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 124+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 123+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 122+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 121+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 120+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 119+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 118+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 117+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 116+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 115+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 114+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 113+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 112+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 111+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 110+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 109+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 108+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 107+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 106+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 105+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 104+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 103+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 102+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 101+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 100+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 99+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 98+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 97+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 96+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 95+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 94+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 93+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 92+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 91+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 90+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 89+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 88+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 87+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 86+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 85+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 84+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 83+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 82+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 81+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 80+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 79+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 78+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 77+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 76+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 75+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 74+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 73+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 72+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 71+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 70+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 69+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 68+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 67+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 66+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 65+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 64+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 63+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 62+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 61+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 60+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 59+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 58+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 57+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 56+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 55+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 54+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 53+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 52+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 51+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 50+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 49+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 48+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 47+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 46+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 45+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 44+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 43+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 42+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 41+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 40+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 39+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 38+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 37+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 36+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 35+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 34+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 33+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 32+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 31+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 30+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 29+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 28+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 27+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 26+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 25+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 24+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 23+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 22+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 21+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 20+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 19+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 18+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 17+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 16+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 15+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 14+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 13+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 12+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 11+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 10+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 9+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 8+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 7+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 6+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 5+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 4+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 3+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 2+1),
    Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ 1+1),
    Finset.Icc_self, Finset.sum_singleton]
  have h1 : ((903413973796489763245662405907881/10000000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 1, Real.log (sigma p 1) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_1
  have h2 : ((60863701526739761862677773223007/1000000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 2, Real.log (sigma p 2) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_2
  have h3 : ((459274957211702521179683245074621/10000000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 3, Real.log (sigma p 3) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_3
  have h4 : ((46125183602588291560069563756459/1250000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 4, Real.log (sigma p 4) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_4
  have h5 : ((61703292637831377399711592220241/2000000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 5, Real.log (sigma p 5) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_5
  have h6 : ((5038191764988616957675133224047/200000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 6, Real.log (sigma p 6) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_6
  have h7 : ((111284891552872684111417358571513/5000000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 7, Real.log (sigma p 7) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_7
  have h8 : ((9966193267420879185794190327167/500000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 8, Real.log (sigma p 8) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_8
  have h9 : ((1804650544305735216489913359843/100000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 9, Real.log (sigma p 9) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_9
  have h10 : ((412160730338389735473309211379/25000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 10, Real.log (sigma p 10) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_10
  have h11 : ((1896838456056855468189202806321/125000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 11, Real.log (sigma p 11) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_11
  have h12 : ((1630553635314027553414775242401/125000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 12, Real.log (sigma p 12) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_12
  have h13 : ((6111815099758835315324058580201/500000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 13, Real.log (sigma p 13) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_13
  have h14 : ((11498303165473835458215007105213/1000000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 14, Real.log (sigma p 14) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_14
  have h15 : ((5183927468485985660241667926013/500000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 15, Real.log (sigma p 15) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_15
  have h16 : ((123089373035399009207322029709/12500 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 16, Real.log (sigma p 16) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_16
  have h17 : ((2343704128083346772463166357041/250000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 17, Real.log (sigma p 17) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_17
  have h18 : ((8733410646753853641608677267747/1000000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 18, Real.log (sigma p 18) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_18
  have h19 : ((130644284032692457475562805604/15625 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 19, Real.log (sigma p 19) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_19
  have h20 : ((3807050322784174392058297459203/500000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 20, Real.log (sigma p 20) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_20
  have h21 : ((113448235395846043493594224431/15625 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 21, Real.log (sigma p 21) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_21
  have h22 : ((1401199026027077660106265943583/200000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 22, Real.log (sigma p 22) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_22
  have h23 : ((1691895909546008434808869938847/250000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 23, Real.log (sigma p 23) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_23
  have h24 : ((6249059033329869163980584712927/1000000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 24, Real.log (sigma p 24) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_24
  have h25 : ((30308931057137102878186492593/5000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 25, Real.log (sigma p 25) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_25
  have h26 : ((5884538635022715563517701153461/1000000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 26, Real.log (sigma p 26) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_26
  have h27 : ((5716645986597675082020202831/1000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 27, Real.log (sigma p 27) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_27
  have h28 : ((1334129829731801479827876012567/250000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 28, Real.log (sigma p 28) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_28
  have h29 : ((2600068861798361200483459127947/500000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 29, Real.log (sigma p 29) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_29
  have h30 : ((4872659279550196531638317354243/1000000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 30, Real.log (sigma p 30) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_30
  have h31 : ((4760543312520691385468151947973/1000000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 31, Real.log (sigma p 31) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_31
  have h32 : ((5816025851008899447768260631/1250 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 32, Real.log (sigma p 32) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_32
  have h33 : ((903727268132071700329593147327/200000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 33, Real.log (sigma p 33) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_33
  have h34 : ((552613049837463715863158556753/125000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 34, Real.log (sigma p 34) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_34
  have h35 : ((1045722852407776823953871327679/250000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 35, Real.log (sigma p 35) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_35
  have h36 : ((198149786602380338120029700667/50000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 36, Real.log (sigma p 36) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_36
  have h37 : ((19451113441033153906190652669/5000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 37, Real.log (sigma p 37) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_37
  have h38 : ((3819576467682825009320328126777/1000000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 38, Real.log (sigma p 38) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_38
  have h39 : ((468876989084763878946659107083/125000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 39, Real.log (sigma p 39) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_39
  have h40 : ((446440959607850113730996268073/125000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 40, Real.log (sigma p 40) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_40
  have h41 : ((1756173905612480650897691327549/500000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 41, Real.log (sigma p 41) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_41
  have h42 : ((838055471488509976944981991689/250000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 42, Real.log (sigma p 42) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_42
  have h43 : ((825191823326950651253275360221/250000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 43, Real.log (sigma p 43) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_43
  have h44 : ((804574505372010308116519944121/250000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 44, Real.log (sigma p 44) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_44
  have h45 : ((308050882203034270141517661499/100000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 45, Real.log (sigma p 45) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_45
  have h46 : ((2430179627523493257982753941/800 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 46, Real.log (sigma p 46) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_46
  have h47 : ((2995773789813709832137931076279/1000000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 47, Real.log (sigma p 47) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_47
  have h48 : ((11503652040184391445035455377/4000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 48, Real.log (sigma p 48) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_48
  have h49 : ((1419392138369809135964229256077/500000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 49, Real.log (sigma p 49) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_49
  have h50 : ((35028862609210644629211124683/12500 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 50, Real.log (sigma p 50) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_50
  have h51 : ((2766495183167328188231433649503/1000000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 51, Real.log (sigma p 51) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_51
  have h52 : ((2695104166734079724122272406477/1000000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 52, Real.log (sigma p 52) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_52
  have h53 : ((106478438753922703678746427329/40000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 53, Real.log (sigma p 53) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_53
  have h54 : ((325413052823593534066784046529/125000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 54, Real.log (sigma p 54) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_54
  have h55 : ((251207566043290373130495767471/100000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 55, Real.log (sigma p 55) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_55
  have h56 : ((303105848226556836098417462941/125000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 56, Real.log (sigma p 56) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_56
  have h57 : ((299865496987199895658412645677/125000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 57, Real.log (sigma p 57) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_57
  have h58 : ((74166752392732678815046679857/31250 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 58, Real.log (sigma p 58) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_58
  have h59 : ((469618638094462672225761015159/200000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 59, Real.log (sigma p 59) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_59
  have h60 : ((56794776687872458199035007481/25000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 60, Real.log (sigma p 60) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_60
  have h61 : ((281114412800359307258104691231/125000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 61, Real.log (sigma p 61) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_61
  have h62 : ((2226322940244121888232355549899/1000000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 62, Real.log (sigma p 62) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_62
  have h63 : ((13483937139870354815731499967/6250 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 63, Real.log (sigma p 63) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_63
  have h64 : ((1068428145440858280023515738149/500000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 64, Real.log (sigma p 64) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_64
  have h65 : ((2083747758607880787935158054779/1000000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 65, Real.log (sigma p 65) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_65
  have h66 : ((1011065300635771043299236238779/500000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 66, Real.log (sigma p 66) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_66
  have h67 : ((1002232148440842318824856370773/500000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 67, Real.log (sigma p 67) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_67
  have h68 : ((495815494282569514465187274071/250000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 68, Real.log (sigma p 68) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_68
  have h69 : ((196602180464186229112022841771/100000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 69, Real.log (sigma p 69) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_69
  have h70 : ((238878530391560919873397242621/125000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 70, Real.log (sigma p 70) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_70
  have h71 : ((1895181581809884958615524176181/1000000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 71, Real.log (sigma p 71) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_71
  have h72 : ((368721015225209543055942789183/200000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 72, Real.log (sigma p 72) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_72
  have h73 : ((22862556377365864183069471761/12500 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 73, Real.log (sigma p 73) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_73
  have h74 : ((907256144821473104858905534863/500000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 74, Real.log (sigma p 74) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_74
  have h75 : ((1777740647160050779825664762563/1000000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 75, Real.log (sigma p 75) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_75
  have h76 : ((350910733309851171933053260527/200000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 76, Real.log (sigma p 76) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_76
  have h77 : ((68397254761428734685762126087/40000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 77, Real.log (sigma p 77) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_77
  have h78 : ((166692651767930275269336722367/100000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 78, Real.log (sigma p 78) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_78
  have h79 : ((16553314520354977453910227611/10000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 79, Real.log (sigma p 79) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_79
  have h80 : ((1614665081501721198745504768701/1000000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 80, Real.log (sigma p 80) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_80
  have h81 : ((6415569547845876698330918517/4000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 81, Real.log (sigma p 81) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_81
  have h82 : ((318631738372557111961494232449/200000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 82, Real.log (sigma p 82) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_82
  have h83 : ((791235179239969043886197755241/500000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 83, Real.log (sigma p 83) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_83
  have h84 : ((772591218259878346327191148363/500000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 84, Real.log (sigma p 84) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_84
  have h85 : ((754596133461932583575538873561/500000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 85, Real.log (sigma p 85) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_85
  have h86 : ((1499870757153560831004878175783/1000000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 86, Real.log (sigma p 86) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_86
  have h87 : ((46580407639956352765713476093/31250 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 87, Real.log (sigma p 87) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_87
  have h88 : ((1457013169666846777084213509047/1000000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 88, Real.log (sigma p 88) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_88
  have h89 : ((18103996321785611871984756903/12500 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 89, Real.log (sigma p 89) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_89
  have h90 : ((1416420274511917273252209677231/1000000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 90, Real.log (sigma p 90) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_90
  have h91 : ((692779423357121924561000552541/500000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 91, Real.log (sigma p 91) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_91
  have h92 : ((1377920940082510149060795788293/1000000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 92, Real.log (sigma p 92) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_92
  have h93 : ((171285451316308460775677233431/125000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 93, Real.log (sigma p 93) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_93
  have h94 : ((272529902125430017919284462549/200000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 94, Real.log (sigma p 94) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_94
  have h95 : ((26683658292482642656604302869/20000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 95, Real.log (sigma p 95) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_95
  have h96 : ((81662188734278861668509872667/62500 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 96, Real.log (sigma p 96) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_96
  have h97 : ((81239784456090878229493693893/62500 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 97, Real.log (sigma p 97) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_97
  have h98 : ((129305815346440577444025988661/100000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 98, Real.log (sigma p 98) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_98
  have h99 : ((633556189732473227324243327163/500000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 99, Real.log (sigma p 99) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_99
  have h100 : ((248387187605129932497586686071/200000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 100, Real.log (sigma p 100) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_100
  have h101 : ((77242521768634472707525805547/62500 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 101, Real.log (sigma p 101) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_101
  have h102 : ((3786856482666075089868946933/3125 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 102, Real.log (sigma p 102) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_102
  have h103 : ((603001213388840023621043954503/500000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 103, Real.log (sigma p 103) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_103
  have h104 : ((73933614228450347455676226507/62500 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 104, Real.log (sigma p 104) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_104
  have h105 : ((580262493884654081742630670767/500000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 105, Real.log (sigma p 105) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_105
  have h106 : ((1155209604515630796287521091703/1000000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 106, Real.log (sigma p 106) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_106
  have h107 : ((17962500075105828688822638878/15625 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 107, Real.log (sigma p 107) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_107
  have h108 : ((225679077382685896156447607571/200000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 108, Real.log (sigma p 108) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_108
  have h109 : ((70158351227717703008720038311/62500 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 109, Real.log (sigma p 109) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_109
  have h110 : ((1102177842336253960010198099757/1000000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 110, Real.log (sigma p 110) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_110
  have h111 : ((10956370187038978313994113147/10000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 111, Real.log (sigma p 111) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_111
  have h112 : ((10760843393121608000000243739/10000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 112, Real.log (sigma p 112) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_112
  have h113 : ((1068278359776371611542062796327/1000000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 113, Real.log (sigma p 113) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_113
  have h114 : ((4197973974046822135747080247/4000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 114, Real.log (sigma p 114) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_114
  have h115 : ((103119445682874930874559682933/100000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 115, Real.log (sigma p 115) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_115
  have h116 : ((817455579796392237154177317/800 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 116, Real.log (sigma p 116) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_116
  have h117 : ((1004242936806476099424047884479/1000000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 117, Real.log (sigma p 117) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_117
  have h118 : ((992874480122083574004061765677/1000000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 118, Real.log (sigma p 118) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_118
  have h119 : ((61001258830674070446852016521/62500 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 119, Real.log (sigma p 119) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_119
  have h120 : ((959585591727601568003031594521/1000000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 120, Real.log (sigma p 120) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_120
  have h121 : ((93602223849805417325418310581/100000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 121, Real.log (sigma p 121) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_121
  have h122 : ((921467327331466973267211418001/1000000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 122, Real.log (sigma p 122) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_122
  have h123 : ((56672175963759131123294720319/62500 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 123, Real.log (sigma p 123) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_123
  have h124 : ((22303352244488538795566533113/25000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 124, Real.log (sigma p 124) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_124
  have h125 : ((1755465596868131198405563509/2000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 125, Real.log (sigma p 125) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_125
  have h126 : ((215887346712411812205408546213/250000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 126, Real.log (sigma p 126) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_126
  have h127 : ((33990461180679228658192881181/40000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 127, Real.log (sigma p 127) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_127
  have h128 : ((836267308992496891215569215551/1000000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 128, Real.log (sigma p 128) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_128
  have h129 : ((4115366452507741154063824821/5000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 129, Real.log (sigma p 129) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_129
  have h130 : ((10127138188247535806063112743/12500 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 130, Real.log (sigma p 130) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_130
  have h131 : ((49848264895471785903547709223/62500 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 131, Real.log (sigma p 131) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_131
  have h132 : ((19631361948089712492576006167/25000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 132, Real.log (sigma p 132) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_132
  have h133 : ((773215916254314986446559294729/1000000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 133, Real.log (sigma p 133) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_133
  have h134 : ((761451195324765815922008099319/1000000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 134, Real.log (sigma p 134) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_134
  have h135 : ((74994622084700106834404905533/100000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 135, Real.log (sigma p 135) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_135
  have h136 : ((11542130104361751186154393428/15625 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 136, Real.log (sigma p 136) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_136
  have h137 : ((9096193227154155476986218509/12500 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 137, Real.log (sigma p 137) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_137
  have h138 : ((44808351355782156398446082061/62500 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 138, Real.log (sigma p 138) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_138
  have h139 : ((353202988621355768010248598231/500000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 139, Real.log (sigma p 139) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_139
  have h140 : ((34805225127833470143002692809/50000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 140, Real.log (sigma p 140) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_140
  have h141 : ((68602376760474016706794517833/100000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 141, Real.log (sigma p 141) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_141
  have h142 : ((676157058931613585905905222787/1000000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 142, Real.log (sigma p 142) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_142
  have h143 : ((666498407364038680445867678581/1000000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 143, Real.log (sigma p 143) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_143
  have h144 : ((32852107296965009997601789661/50000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 144, Real.log (sigma p 144) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_144
  have h145 : ((404864197116019969702346624/625 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 145, Real.log (sigma p 145) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_145
  have h146 : ((319357384482494090962831330191/500000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 146, Real.log (sigma p 146) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_146
  have h147 : ((62983297206805335363018734351/100000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 147, Real.log (sigma p 147) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_147
  have h148 : ((62113235291167746457415605689/100000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 148, Real.log (sigma p 148) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_148
  have h149 : ((76576003945075091087242035423/125000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 149, Real.log (sigma p 149) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_149
  have h150 : ((60425526055444009074916024269/100000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 150, Real.log (sigma p 150) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_150
  have h151 : ((298034772626600554685601568689/500000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 151, Real.log (sigma p 151) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_151
  have h152 : ((29402322616801783249108698623/50000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 152, Real.log (sigma p 152) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_152
  have h153 : ((290090866210219249550813274453/500000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 153, Real.log (sigma p 153) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_153
  have h154 : ((572471261230560251950156249371/1000000 : ℚ) : ℝ) ≤ ∑ p ∈ shellPrimes highN 154, Real.log (sigma p 154) :=
    le_of_eq_of_le (by norm_num [logNatLo]) shell_tight_154
  linarith [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47, h48, h49, h50, h51, h52, h53, h54, h55, h56, h57, h58, h59, h60, h61, h62, h63, h64, h65, h66, h67, h68, h69, h70, h71, h72, h73, h74, h75, h76, h77, h78, h79, h80, h81, h82, h83, h84, h85, h86, h87, h88, h89, h90, h91, h92, h93, h94, h95, h96, h97, h98, h99, h100, h101, h102, h103, h104, h105, h106, h107, h108, h109, h110, h111, h112, h113, h114, h115, h116, h117, h118, h119, h120, h121, h122, h123, h124, h125, h126, h127, h128, h129, h130, h131, h132, h133, h134, h135, h136, h137, h138, h139, h140, h141, h142, h143, h144, h145, h146, h147, h148, h149, h150, h151, h152, h153, h154]

/-- **The high finite input, as a theorem.**  `3.2411 < F ⌊e⁶⁵⌋`. -/
theorem highFiniteInput_proof : (3.2411 : ℝ) < F highN := by
  have hdisj : Disjoint (Finset.Icc (1 : ℕ) 154) (Finset.Icc 155 1000000) := by
    rw [Finset.disjoint_left]; intro a ha hb
    rw [Finset.mem_Icc] at ha hb; omega
  have hsplit : Finset.Icc (1 : ℕ) 1000000 = Finset.Icc 1 154 ∪ Finset.Icc 155 1000000 := by
    ext p; rw [Finset.mem_union, Finset.mem_Icc, Finset.mem_Icc, Finset.mem_Icc]; omega
  have hK : ((1690292257250233856213705682207391/2000000 : ℚ) : ℝ)
      ≤ ∑ m ∈ Finset.Icc 1 1000000, ∑ p ∈ shellPrimes highN m, Real.log (sigma p m) := by
    rw [hsplit, Finset.sum_union hdisj]
    refine le_trans ?_ (add_le_add grid_sum_ge aggregate_lower)
    push_cast
    norm_num
  exact highFiniteInput_of_shell_sum_ge (1690292257250233856213705682207391/2000000)
    (by norm_num) (by norm_num [highN]) hK

/-- **High finite input (`comp:high`), as a proved theorem.**  This is the
paper's computational lemma `comp:high`, `F(N₁) > 3.2411`, proved in Lean:
`highFiniteInput_proof` stated at the literal `N₁ = ⌊e⁶⁵⌋` numeral (defeq to
`highN`).  Its trust boundary is `bgmsSTable` + `dusart_theta_k3` (consumed
via the derived theorem `dusart_theta_approx`) + Lean reasoning (see
`#print axioms`).  Consumed by `CertificateTransfer.cert_F_N1_bounds`. -/
theorem highFiniteInput :
    (3.2411 : ℝ) < F 16948892444103337141417836114 :=
  highFiniteInput_proof

end Erdos320
