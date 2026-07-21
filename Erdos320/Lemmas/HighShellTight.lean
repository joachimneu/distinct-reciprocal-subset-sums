import Erdos320.Lemmas.LogNatBounds
import Erdos320.Lemmas.HighFiniteProof
import Erdos320.Lemmas.HighShellLedger

/-!
# Tight per-shell machinery for the high-finite-input shell ledger

This file provides the precision-tight variant of the per-shell pipeline of
`HighShellLedger.lean` — the form consumed by the full 154-shell ledger
(`HighShellGrid1..8.lean`, `HighAggregate.lean`, `HighFiniteAssembly.lean`) —
and instantiates it on the three representative shells (`shell_2_tight`,
`shell_61_tight`, `shell_121_tight`, one per collision regime `b ∈ {0,1,2}`).
It tightens the three convenience loosenings of `HighShellLedger.lean`:

1. **`log N₁`.**  `HighShellLedger.lean` bounds `log N₁ ∈ [64.999, 65.001]`
   (a ±10⁻³ window).  `high_log_N1_lower_tight`/`high_log_N1_upper_tight`
   sharpen this to `[64.999999, 65.000001]` (a ±10⁻⁶ window), by the same
   `exp`-comparison but carrying enough digits of `e⁶⁵`
   (`(2.7182818286)⁶⁵` / `(2.7182818283)⁶⁵`).  Since `N₁ = ⌊e⁶⁵⌋`,
   `log N₁ = 65 − ε` with `ε ≈ 6·10⁻²⁹`, so both bounds hold
   with vast room; this is purely about digits carried.

2. **`ℓ = log(sL)`.**  Instead of coarse roundings of `log(sL)` (`30.9` for
   `m=61`, `52.6` for `m=121`), `ℓ` is taken to `~10⁻⁴`–`10⁻⁵` of the true
   value via `log_ge_of` at higher precision (`f` up to five/six fractional
   digits).

3. **The `b = 2` penalty.**  Instead of `log(1 + t) ≤ log 10` (with `t ≈ 8`,
   losing `≈ 0.10`), `log_le_of_real` below bounds `log(arg)` directly by a
   tight `exp`-comparison on the *explicit rational* argument
   `arg = 1 + b(sL−1)/Pm`, giving a penalty tight to `~10⁻⁴`.

The tightened count uses the sharper `log N₁` window through `lbLoQt`/`laLoQt`/
`lbUpQt` (mirroring `lbLoQ`/`laLoQ`/`lbUpQ` of `HighShellLedger.lean`), which
recovers the certificate's per-shell prime count to `~2·10⁻⁸` relative.
Nothing in this file is assumed — every bound below is Lean-checked.
-/

namespace Erdos320

open Finset

/-! ## Tightened `log N₁` bounds (`±10⁻⁶` window)

Same `exp`-comparison as `high_log_N1_lower`/`high_log_N1_upper`
(`HighFiniteProof.lean`), but with the split `exp 64.999999 · exp 10⁻⁶ = exp 65`
(resp. `exp 65.000001 = exp 65 · exp 10⁻⁶`) and enough digits of `e⁶⁵`:
`(2.7182818286)⁶⁵ ≤ 1.69489·10²⁸` and `(2.7182818283)⁶⁵ ≥ 1.69488923·10²⁸`. -/

/-- **Tight lower bound** `64.999999 ≤ log N₁`. -/
theorem high_log_N1_lower_tight : (64.999999 : ℝ) ≤ Real.log (highN : ℝ) := by
  have hpos : (0 : ℝ) < (highN : ℝ) := by norm_num [highN]
  rw [Real.le_log_iff_exp_le hpos]
  have heq : Real.exp (65 : ℝ) = Real.exp 1 ^ 65 := by
    rw [← Real.exp_nat_mul]; norm_num
  have hub : Real.exp (65 : ℝ) ≤ 1.69489e28 := by
    have h1 : Real.exp 1 ^ 65 ≤ (2.7182818286 : ℝ) ^ 65 :=
      pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 65
    have h2 : (2.7182818286 : ℝ) ^ 65 ≤ 1.69489e28 := by norm_num
    rw [heq]; linarith
  have hsplit : Real.exp (64.999999 : ℝ) * Real.exp (0.000001 : ℝ) = Real.exp (65 : ℝ) := by
    rw [← Real.exp_add]; norm_num
  have h1 : (1.000001 : ℝ) ≤ Real.exp (0.000001 : ℝ) := by
    have := Real.add_one_le_exp (0.000001 : ℝ); linarith
  have h2 : Real.exp (64.999999 : ℝ) * 1.000001 ≤ Real.exp (65 : ℝ) := by
    rw [← hsplit]; exact mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
  have h3 : Real.exp (64.999999 : ℝ) * 1.000001 ≤ 1.69489e28 := le_trans h2 hub
  have hN : (1.69489e28 : ℝ) ≤ (highN : ℝ) * 1.000001 := by norm_num [highN]
  nlinarith [Real.exp_pos (64.999999 : ℝ)]

/-- **Tight upper bound** `log N₁ ≤ 65.000001`. -/
theorem high_log_N1_upper_tight : Real.log (highN : ℝ) ≤ 65.000001 := by
  have hpos : (0 : ℝ) < (highN : ℝ) := by norm_num [highN]
  rw [Real.log_le_iff_le_exp hpos]
  have heq : Real.exp (65 : ℝ) = Real.exp 1 ^ 65 := by
    rw [← Real.exp_nat_mul]; norm_num
  have hlb : (1.69488923e28 : ℝ) ≤ Real.exp (65 : ℝ) := by
    have h1 : (2.7182818283 : ℝ) ^ 65 ≤ Real.exp 1 ^ 65 :=
      pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 65
    have h2 : (1.69488923e28 : ℝ) ≤ (2.7182818283 : ℝ) ^ 65 := by norm_num
    rw [heq]; linarith
  have h1 : (1.000001 : ℝ) ≤ Real.exp (0.000001 : ℝ) := by
    have := Real.add_one_le_exp (0.000001 : ℝ); linarith
  have hsplit : Real.exp (65.000001 : ℝ) = Real.exp (65 : ℝ) * Real.exp (0.000001 : ℝ) := by
    rw [← Real.exp_add]; norm_num
  rw [hsplit]
  have hprod : (1.69488923e28 : ℝ) * 1.000001 ≤ Real.exp (65 : ℝ) * Real.exp (0.000001 : ℝ) :=
    mul_le_mul hlb h1 (by norm_num) (Real.exp_pos _).le
  have hN : (highN : ℝ) ≤ 1.69488923e28 * 1.000001 := by norm_num [highN]
  linarith

/-! ## Tightened rational log enclosures for the shell endpoints

Mirror `lbLoQ`/`laLoQ`/`lbUpQ` of `HighShellLedger.lean`, but with the sharper
`64.999999`/`65.000001` window from the two lemmas above. -/

/-- Tight rational lower bound for `log(N₁/m) = log N₁ − log m`. -/
def lbLoQt (m : ℕ) : ℚ := 64.999999 - logNatHi m

/-- Tight rational lower bound for `log(N₁/(m+1)) = log N₁ − log(m+1)`. -/
def laLoQt (m : ℕ) : ℚ := 64.999999 - logNatHi (m + 1)

/-- Tight rational upper bound for `log(N₁/m) = log N₁ − log m`. -/
def lbUpQt (m : ℕ) : ℚ := 65.000001 - logNatLo m

theorem lbLoQt_le (m : ℕ) (h1 : 1 ≤ m) (h2 : m ≤ 155) :
    (lbLoQt m : ℝ) ≤ Real.log ((highN : ℝ) / (m : ℝ)) := by
  have hN0 : (highN : ℝ) ≠ 0 := by norm_num [highN]
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  rw [Real.log_div hN0 hm0]
  have hlogN := high_log_N1_lower_tight
  have hlogm := logNat_upper m h1 h2
  have hc : (lbLoQt m : ℝ) = 64.999999 - (logNatHi m : ℝ) := by
    simp only [lbLoQt]; push_cast; ring
  rw [hc]; linarith

theorem laLoQt_le (m : ℕ) (h2 : m + 1 ≤ 155) :
    (laLoQt m : ℝ) ≤ Real.log ((highN : ℝ) / ((m : ℝ) + 1)) := by
  have hN0 : (highN : ℝ) ≠ 0 := by norm_num [highN]
  have hm0 : ((m : ℝ) + 1) ≠ 0 := by positivity
  have hcast : ((m : ℝ) + 1) = ((m + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [Real.log_div hN0 hm0]
  have hlogN := high_log_N1_lower_tight
  have hlogm1 : Real.log ((m : ℝ) + 1) ≤ (logNatHi (m + 1) : ℝ) := by
    rw [hcast]; exact logNat_upper (m + 1) (by omega) h2
  have hc : (laLoQt m : ℝ) = 64.999999 - (logNatHi (m + 1) : ℝ) := by
    simp only [laLoQt]; push_cast; ring
  rw [hc]; linarith

theorem lbUpQt_ge (m : ℕ) (h1 : 1 ≤ m) (h2 : m ≤ 155) :
    Real.log ((highN : ℝ) / (m : ℝ)) ≤ (lbUpQt m : ℝ) := by
  have hN0 : (highN : ℝ) ≠ 0 := by norm_num [highN]
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  rw [Real.log_div hN0 hm0]
  have hlogN := high_log_N1_upper_tight
  have hlogm := logNat_lower m h1 h2
  have hc : (lbUpQt m : ℝ) = 65.000001 - (logNatLo m : ℝ) := by
    simp only [lbUpQt]; push_cast; ring
  rw [hc]; linarith

/-! ## A direct `log`-upper bound for a real argument by `exp`-comparison

Companion to `log_ge_of` (`HighShellLedger.lean`): bounds `log(arg)` *from
above* for an arbitrary positive real `arg`, given a rational-checkable
`arg ≤ (2.7182818283)^k · TL` with `TL ≤ exp f` a Taylor *lower* sum
(`Real.sum_le_exp_of_nonneg`).  Used to bound the `b = 2` collision penalty
`log(1 + b(sL−1)/Pm)` tightly on the explicit rational argument, rather than
through the coarse `log 10`. -/
theorem log_le_of_real (arg : ℝ) (hpos : 0 < arg) (k : ℕ) (f TL : ℝ)
    (hTL0 : 0 ≤ TL) (hTL : TL ≤ Real.exp f)
    (hle : arg ≤ (2.7182818283 : ℝ) ^ k * TL) :
    Real.log arg ≤ (k : ℝ) + f := by
  rw [Real.log_le_iff_le_exp hpos]
  have hk : Real.exp (k : ℝ) = Real.exp 1 ^ k := by
    rw [show (k : ℝ) = (k : ℝ) * 1 by ring, Real.exp_nat_mul]
  have h1 : Real.exp ((k : ℝ) + f) = Real.exp 1 ^ k * Real.exp f := by
    rw [Real.exp_add, hk]
  have he : (2.7182818283 : ℝ) ^ k ≤ Real.exp 1 ^ k :=
    pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le k
  rw [h1]
  calc arg ≤ (2.7182818283 : ℝ) ^ k * TL := hle
    _ ≤ Real.exp 1 ^ k * Real.exp f := mul_le_mul he hTL hTL0 (by positivity)

/-! ## The tightened reusable per-shell contribution lower bound

Identical to `shell_contribution_ge` (`HighShellLedger.lean`) except that the
prime count is enclosed with the tight `lbLoQt`/`laLoQt`/`lbUpQt` window. -/
theorem shell_contribution_ge_tight (m b : ℕ) (Pm : ℚ) (ℓ pen : ℝ) (sL : ℕ)
    (hm1 : 1 ≤ m) (hmU : m ≤ 154)
    (hb : (89967803 : ℝ) ≤ (highN : ℝ) / (m : ℝ))
    (ha : (89967803 : ℝ) ≤ (highN : ℝ) / ((m : ℝ) + 1))
    (hbig : (1 : ℝ) < (highN : ℝ) / ((m : ℝ) + 1))
    (hbN : m * (m + 1) ≤ highN)
    (hWlt : (((Finset.Icc 1 m).lcm id : ℕ) : ℚ) * harmonicSum m
              < ((highN : ℚ) / ((m : ℚ) + 1)) ^ (b + 1))
    (hlbpos : 0 < lbLoQt m) (hlapos : 0 < laLoQt m) (hLbpos : 0 < lbUpQt m)
    (hPmpos : 0 < Pm) (hbP : (b : ℚ) ≤ Pm)
    (hPmDus : (Pm : ℝ) ≤
      (((highN : ℝ) / (m : ℝ) - 0.006788 * ((highN : ℝ) / (m : ℝ)) / (lbLoQt m : ℝ))
        - ((highN : ℝ) / ((m : ℝ) + 1)
            + 0.006788 * ((highN : ℝ) / ((m : ℝ) + 1)) / (laLoQt m : ℝ))) / (lbUpQt m : ℝ))
    (hsLdef : sLowerBGMS m = sL) (hsL1 : 1 ≤ sL)
    (hℓ : ℓ ≤ Real.log (sL : ℝ))
    (hpen : Real.log (1 + (b : ℝ) * ((sL : ℝ) - 1) / (Pm : ℝ)) ≤ pen) :
    (Pm : ℝ) * (ℓ - pen) ≤ ∑ p ∈ shellPrimes highN m, Real.log (sigma p m) := by
  have hm155 : m ≤ 155 := by omega
  have hmU155 : m + 1 ≤ 155 := by omega
  have hcard : (Pm : ℝ) ≤ ((shellPrimes highN m).card : ℝ) :=
    le_trans hPmDus
      (shellPrimes_card_lower_dusart hm1 hb ha (lbLoQt m : ℝ) (laLoQt m : ℝ) (lbUpQt m : ℝ)
        (by exact_mod_cast hlbpos) (lbLoQt_le m hm1 hm155)
        (by exact_mod_cast hlapos) (laLoQt_le m hmU155)
        (lbUpQt_ge m hm1 hm155) (by exact_mod_cast hLbpos))
  have hsLS : sL ≤ S m := hsLdef ▸ S_ge_sLowerBGMS m hmU
  have hWltR := hWlt_of_ratLt hWlt
  have hPmposR : (0 : ℝ) < (Pm : ℝ) := by exact_mod_cast hPmpos
  have hbPR : (b : ℝ) ≤ (Pm : ℝ) := by exact_mod_cast hbP
  exact shell_contribution_pos b (Pm : ℝ) ℓ pen sL hbN hbig hWltR hPmposR hcard hbPR
    hsL1 hsLS hℓ hpen

/-! ## The three representative shells, proved tight

The per-shell rational count `Pm` is the floor of the tight-Dusart bound; `ℓ`
and `pen` are as tight as the `exp`-comparison cleanly supports (each shell's
docstring records the resulting values versus the certificate). -/

set_option maxHeartbeats 4000000 in
/-- **Shell `m = 2` (tight), regime `b = 0`.**  `Pm = 4.39038853…·10²⁵`
(cert `4.39038860·10²⁵`, ratio `0.99999998`), `ℓ = log 4` lower bound,
no penalty.  Proved `≈ 6.086370·10²⁵` (cert `6.0863710·10²⁵`). -/
theorem shell_2_tight :
    ((43903885284047038401140085 : ℚ) : ℝ) * ((logNatLo 4 : ℝ) - 0)
      ≤ ∑ p ∈ shellPrimes highN 2, Real.log (sigma p 2) := by
  apply shell_contribution_ge_tight 2 0 43903885284047038401140085 (logNatLo 4 : ℝ) 0 4
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
/-- **Shell `m = 61` (tight), regime `b = 1`.**  `Pm = 7.2591021963…·10²²`
(cert `7.2591023250·10²²`, ratio `0.99999998`), `ℓ = 30.980627` (true
`log(sL) = 30.9806275`), penalty `≤ 10⁻⁷`.  Proved `≈ 2.248914·10²⁴`
(cert `2.2489155·10²⁴`). -/
theorem shell_61_tight :
    ((72591021963302951272348 : ℚ) : ℝ) * (((30 : ℝ) + 0.980627) - (0.0000001 : ℝ))
      ≤ ∑ p ∈ shellPrimes highN 61, Real.log (sigma p 61) := by
  apply shell_contribution_ge_tight 61 1 72591021963302951272348 ((30 : ℝ) + 0.980627)
    (0.0000001 : ℝ) 28491517001728
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
  · refine (log_add_one_le (by norm_num)).trans (by norm_num)

set_option maxHeartbeats 4000000 in
/-- **Shell `m = 121` (tight), regime `b = 2`.**  `Pm = 1.85482744926…·10²²`
(cert `1.85482748547·10²²`, ratio `0.99999998`), `ℓ = 52.66439` (true
`log(sL) = 52.6643957`), penalty `≤ 2.2004` on the explicit argument
`arg = 9.02754821…` (true `log arg = 2.2002808`, versus the coarse `log 10`
of `HighShellLedger.lean`).
Proved `≈ 9.360220·10²³` (cert `9.3602227·10²³`). -/
theorem shell_121_tight :
    ((18548274492603876355665 : ℚ) : ℝ) * (((52 : ℝ) + 0.66439) - ((2 : ℝ) + 0.2004))
      ≤ ∑ p ∈ shellPrimes highN 121, Real.log (sigma p 121) := by
  apply shell_contribution_ge_tight 121 2 18548274492603876355665 ((52 : ℝ) + 0.66439)
    ((2 : ℝ) + 0.2004) 74448583843323114946560
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
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.66439 : ℝ) by norm_num)
      (show (0.66439 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 74448583843323114946560 (by norm_num) 52 0.66439 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · have hTL := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.2004 : ℝ) by norm_num) 12
    refine log_le_of_real _ (by positivity) 2 0.2004 _ (by positivity) hTL ?_
    norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

end Erdos320
