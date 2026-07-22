import Erdos320.Lemmas.LogNatBounds
import Erdos320.Lemmas.HighFiniteProof
import Erdos320.Lemmas.ShellCountDusart
import Erdos320.Lemmas.Doublings

/-!
# The high-finite-input shell ledger: composing the per-shell pipeline

This file assembles the reusable per-shell contribution lower bound for the high
finite input `highFiniteInput : 3.2411 < F ⌊e⁶⁵⌋` and instantiates it end-to-end
on three representative shells — one in each collision regime `b ∈ {0, 1, 2}`.
The full 154-shell ledger runs the tightened variant of this pipeline
(`HighShellTight.lean`) through `HighShellGrid1..8.lean` +
`HighFiniteAssembly.lean`.

The composition wires together four already-proved, hole-free pieces:

* `shellPrimes_card_lower_dusart` (`ShellCountDusart.lean`) — a *rational* lower
  bound on `(shellPrimes N₁ m).card`, fed the log-table enclosures for
  `log(N₁/m) = log N₁ − log m` and `log(N₁/(m+1)) = log N₁ − log(m+1)` obtained
  from `high_log_N1_lower/upper` (`HighFiniteProof.lean`) and `logNat_upper/lower`
  (`LogNatBounds.lean`);
* `shell_contribution_pos` (`HighFiniteProof.lean`) — the monotone per-shell
  bound `Pm·(ℓ − pen) ≤ ∑_{p∈shell} log σ`, valid for every `b` (the `b = 0`
  regime specializes with `pen = 0`);
* `S_ge_sLowerBGMS` (`Doublings.lean`) — the certified `S m ≥ sLowerBGMS m`
  lower bound driving `ℓ ≤ log(S m)`;
* `hWlt_of_ratLt` (`HighFiniteProof.lean`) — the tight collision check
  `L_m·H_m < (N₁/(m+1))^(b+1)` by `native_decide` in `ℚ`.

The single reusable lemma is `shell_contribution_ge`; the three concrete shells
are `shell_2` (`b = 0`), `shell_61` (`b = 1`), `shell_121` (`b = 2`).

## Bounding `log(S m)` for the huge certified counts

`S m` for the certified shells is astronomically large (e.g. `S 61 ≈ 2.85·10¹³`)
and its prime factorization contains primes far above the `155`-entry log table
(`617537 ∣ S 61`, `80677 ∣ S 83`), so the table's `logMul` tree cannot bound
`log(S m)`.  We therefore lower-bound `log(sL)` directly by the same
`exp`-comparison used in `LogNatBounds.lean` (`log_ge_of` below): `ℓ ≤ log(sL)`
follows from `exp(ℓ) = exp 1 ^ k · exp f ≤ (2.7182818286)^k · TU ≤ sL`, with
`TU ≥ exp f` a degree-12 Taylor upper sum (`Real.exp_bound'`) and
`exp 1 < 2.7182818286` (`Real.exp_one_lt_d9`).
-/

namespace Erdos320

open Finset

/-! ## Rational log enclosures for the shell endpoints

For `1 ≤ m ≤ 154` the endpoints `log(N₁/m)` and `log(N₁/(m+1))` are enclosed by
combining `64.999 ≤ log N₁ ≤ 65.001` (`high_log_N1_lower/upper`) with the
per-integer table `logNatLo/Hi`. -/

/-- Rational lower bound for `log(N₁/m) = log N₁ − log m`. -/
def lbLoQ (m : ℕ) : ℚ := 64.999 - logNatHi m

/-- Rational lower bound for `log(N₁/(m+1)) = log N₁ − log(m+1)`. -/
def laLoQ (m : ℕ) : ℚ := 64.999 - logNatHi (m + 1)

/-- Rational upper bound for `log(N₁/m) = log N₁ − log m`. -/
def lbUpQ (m : ℕ) : ℚ := 65.001 - logNatLo m

theorem lbLoQ_le (m : ℕ) (h1 : 1 ≤ m) (h2 : m ≤ 155) :
    (lbLoQ m : ℝ) ≤ Real.log ((highN : ℝ) / (m : ℝ)) := by
  have hN0 : (highN : ℝ) ≠ 0 := by norm_num [highN]
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  rw [Real.log_div hN0 hm0]
  have hlogN := high_log_N1_lower
  have hlogm := logNat_upper m h1 h2
  have hc : (lbLoQ m : ℝ) = 64.999 - (logNatHi m : ℝ) := by
    simp only [lbLoQ]; push_cast; ring
  rw [hc]; linarith

theorem laLoQ_le (m : ℕ) (h2 : m + 1 ≤ 155) :
    (laLoQ m : ℝ) ≤ Real.log ((highN : ℝ) / ((m : ℝ) + 1)) := by
  have hN0 : (highN : ℝ) ≠ 0 := by norm_num [highN]
  have hm0 : ((m : ℝ) + 1) ≠ 0 := by positivity
  have hcast : ((m : ℝ) + 1) = ((m + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [Real.log_div hN0 hm0]
  have hlogN := high_log_N1_lower
  have hlogm1 : Real.log ((m : ℝ) + 1) ≤ (logNatHi (m + 1) : ℝ) := by
    rw [hcast]; exact logNat_upper (m + 1) (by omega) h2
  have hc : (laLoQ m : ℝ) = 64.999 - (logNatHi (m + 1) : ℝ) := by
    simp only [laLoQ]; push_cast; ring
  rw [hc]; linarith

theorem lbUpQ_ge (m : ℕ) (h1 : 1 ≤ m) (h2 : m ≤ 155) :
    Real.log ((highN : ℝ) / (m : ℝ)) ≤ (lbUpQ m : ℝ) := by
  have hN0 : (highN : ℝ) ≠ 0 := by norm_num [highN]
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  rw [Real.log_div hN0 hm0]
  have hlogN := high_log_N1_upper
  have hlogm := logNat_lower m h1 h2
  have hc : (lbUpQ m : ℝ) = 65.001 - (logNatLo m : ℝ) := by
    simp only [lbUpQ]; push_cast; ring
  rw [hc]; linarith

/-! ## `exp`-comparison lower bound on `log` of a large natural

Mirrors the (private) `le_log_of` of `LogNatBounds.lean`, but for an arbitrary
positive natural `s` rather than a table entry `≤ 155`. -/

theorem log_ge_of (s : ℕ) (hs : 0 < s) (k : ℕ) (f TU : ℝ)
    (hTU : Real.exp f ≤ TU)
    (hle : (2.7182818286 : ℝ) ^ k * TU ≤ (s : ℝ)) :
    ((k : ℝ) + f) ≤ Real.log (s : ℝ) := by
  rw [Real.le_log_iff_exp_le (by exact_mod_cast hs)]
  have hk : Real.exp (k : ℝ) = Real.exp 1 ^ k := by
    rw [show (k : ℝ) = (k : ℝ) * 1 by ring, Real.exp_nat_mul]
  have h1 : Real.exp ((k : ℝ) + f) = Real.exp 1 ^ k * Real.exp f := by
    rw [Real.exp_add, hk]
  have he : Real.exp 1 ^ k ≤ (2.7182818286 : ℝ) ^ k :=
    pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le k
  rw [h1]
  calc Real.exp 1 ^ k * Real.exp f
      ≤ (2.7182818286 : ℝ) ^ k * TU := mul_le_mul he hTU (Real.exp_pos f).le (by positivity)
    _ ≤ (s : ℝ) := hle

/-! ## Penalty upper bounds

Two ways to bound the collision penalty `log(1 + t)` from above:
* `log_add_one_le` — the elementary `log(1 + t) ≤ t`, tight when `t` is tiny
  (the `b = 1` regime, where `t ≈ 4·10⁻¹⁰`);
* `log_le_logNatHi_of_le` — bound the argument by a small integer `K ≤ 155` and
  use the log table, tight when `t` is moderate (the `b = 2` regime, `t ≈ 8`). -/

theorem log_add_one_le {t : ℝ} (ht : 0 ≤ t) : Real.log (1 + t) ≤ t := by
  have h : (0 : ℝ) < 1 + t := by linarith
  have := Real.log_le_sub_one_of_pos h
  linarith

theorem log_le_logNatHi_of_le {arg : ℝ} {K : ℕ} (h1 : 1 ≤ K) (h2 : K ≤ 155)
    (hpos : 0 < arg) (hle : arg ≤ (K : ℝ)) : Real.log arg ≤ (logNatHi K : ℝ) :=
  le_trans (Real.log_le_log hpos hle) (logNat_upper K h1 h2)

/-! ## The reusable per-shell contribution lower bound

`shell_contribution_ge` composes the four ingredients into a single statement
whose every hypothesis is discharged, at a literal `m`, by `norm_num`/
`native_decide`.  The Dusart count enters through `hPmDus`, a purely rational
lower bound `Pm ≤ (Dusart formula)`; the `S`-lower bound through `hsLdef`; the
collision multiplicity through `hWlt`; and the penalty/`log S` bounds through
`hpen`/`hℓ`. -/

theorem shell_contribution_ge (m b : ℕ) (Pm : ℚ) (ℓ pen : ℝ) (sL : ℕ)
    (hm1 : 1 ≤ m) (hmU : m ≤ 154)
    (hb : (89967803 : ℝ) ≤ (highN : ℝ) / (m : ℝ))
    (ha : (89967803 : ℝ) ≤ (highN : ℝ) / ((m : ℝ) + 1))
    (hbig : (1 : ℝ) < (highN : ℝ) / ((m : ℝ) + 1))
    (hbN : m * (m + 1) ≤ highN)
    (hWlt : (((Finset.Icc 1 m).lcm id : ℕ) : ℚ) * harmonicSum m
              < ((highN : ℚ) / ((m : ℚ) + 1)) ^ (b + 1))
    (hlbpos : 0 < lbLoQ m) (hlapos : 0 < laLoQ m) (hLbpos : 0 < lbUpQ m)
    (hPmpos : 0 < Pm) (hbP : (b : ℚ) ≤ Pm)
    (hPmDus : (Pm : ℝ) ≤
      (((highN : ℝ) / (m : ℝ) - 0.006788 * ((highN : ℝ) / (m : ℝ)) / (lbLoQ m : ℝ))
        - ((highN : ℝ) / ((m : ℝ) + 1)
            + 0.006788 * ((highN : ℝ) / ((m : ℝ) + 1)) / (laLoQ m : ℝ))) / (lbUpQ m : ℝ))
    (hsLdef : sLowerBGMS m = sL) (hsL1 : 1 ≤ sL)
    (hℓ : ℓ ≤ Real.log (sL : ℝ))
    (hpen : Real.log (1 + (b : ℝ) * ((sL : ℝ) - 1) / (Pm : ℝ)) ≤ pen) :
    (Pm : ℝ) * (ℓ - pen) ≤ ∑ p ∈ shellPrimes highN m, Real.log (sigma p m) := by
  have hm155 : m ≤ 155 := by omega
  have hmU155 : m + 1 ≤ 155 := by omega
  have hcard : (Pm : ℝ) ≤ ((shellPrimes highN m).card : ℝ) :=
    le_trans hPmDus
      (shellPrimes_card_lower_dusart hm1 hb ha (lbLoQ m : ℝ) (laLoQ m : ℝ) (lbUpQ m : ℝ)
        (by exact_mod_cast hlbpos) (lbLoQ_le m hm1 hm155)
        (by exact_mod_cast hlapos) (laLoQ_le m hmU155)
        (lbUpQ_ge m hm1 hm155) (by exact_mod_cast hLbpos))
  have hsLS : sL ≤ S m := hsLdef ▸ S_ge_sLowerBGMS m hmU
  have hWltR := hWlt_of_ratLt hWlt
  have hPmposR : (0 : ℝ) < (Pm : ℝ) := by exact_mod_cast hPmpos
  have hbPR : (b : ℝ) ≤ (Pm : ℝ) := by exact_mod_cast hbP
  exact shell_contribution_pos b (Pm : ℝ) ℓ pen sL hbN hbig hWltR hPmposR hcard hbPR
    hsL1 hsLS hℓ hpen

/-! ## Three representative shells (one per collision regime)

The concrete inputs reproduce the certificate's `high_bridge_lower` per-shell
data, except that the log endpoints use the
coarser `64.999/65.001 ± logNat` enclosures rather than full-precision `log`, and
the `b = 2` penalty is bounded through `log 10` rather than the tight
`log(1 + t)`.  Both loosenings are modest and each shell's contribution stays
close to the certificate value (recorded in each shell's docstring). -/

set_option maxHeartbeats 2000000 in
/-- **Shell `m = 2`, regime `b = 0`.**  `Pm₀ = 4.3903…·10²⁵`, `S 2 = 4`, no
penalty.  Contribution `Pm₀·log 4 ≈ 6.086·10²⁵` (certificate: `6.086·10²⁵`). -/
theorem shell_2 :
    ((43903202890552501568688984 : ℚ) : ℝ) * ((logNatLo 4 : ℝ) - 0)
      ≤ ∑ p ∈ shellPrimes highN 2, Real.log (sigma p 2) := by
  apply shell_contribution_ge 2 0 43903202890552501568688984 (logNatLo 4 : ℝ) 0 4
  · norm_num
  · norm_num
  · norm_num [highN]
  · norm_num [highN]
  · norm_num [highN]
  · norm_num [highN]
  · native_decide
  · norm_num [lbLoQ, logNatHi]
  · norm_num [laLoQ, logNatHi]
  · norm_num [lbUpQ, logNatLo]
  · norm_num
  · norm_num
  · norm_num [lbLoQ, laLoQ, lbUpQ, logNatHi, logNatLo, highN]
  · native_decide
  · norm_num
  · exact logNat_lower 4 (by norm_num) (by norm_num)
  · simp

set_option maxHeartbeats 2000000 in
/-- **Shell `m = 61`, regime `b = 1`.**  `Pm₀ = 7.2589…·10²²`,
`S 61 ≥ 28491517001728`, penalty `t ≈ 3.9·10⁻¹⁰ ≤ 10⁻⁷`, `ℓ = 30.9`.
Contribution `Pm₀·(30.9 − 10⁻⁷) ≈ 2.243·10²⁴` (certificate: `2.249·10²⁴`). -/
theorem shell_61 :
    ((72589814428792216456729 : ℚ) : ℝ) * (((30 : ℝ) + 0.9) - (0.0000001 : ℝ))
      ≤ ∑ p ∈ shellPrimes highN 61, Real.log (sigma p 61) := by
  apply shell_contribution_ge 61 1 72589814428792216456729 ((30 : ℝ) + 0.9)
    (0.0000001 : ℝ) 28491517001728
  · norm_num
  · norm_num
  · norm_num [highN]
  · norm_num [highN]
  · norm_num [highN]
  · norm_num [highN]
  · native_decide
  · norm_num [lbLoQ, logNatHi]
  · norm_num [laLoQ, logNatHi]
  · norm_num [lbUpQ, logNatLo]
  · norm_num
  · norm_num
  · norm_num [lbLoQ, laLoQ, lbUpQ, logNatHi, logNatLo, highN]
  · native_decide
  · norm_num
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.9 : ℝ) by norm_num)
      (show (0.9 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 28491517001728 (by norm_num) 30 0.9 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · refine (log_add_one_le (by norm_num)).trans (by norm_num)

set_option maxHeartbeats 2000000 in
/-- **Shell `m = 121`, regime `b = 2`.**  `Pm₀ = 1.8547…·10²²`,
`S 121 ≥ 74448583843323114946560`, penalty argument `≈ 9.03 ≤ 10` so
`log(1 + t) ≤ log 10`, `ℓ = 52.6`.  Contribution
`Pm₀·(52.6 − log 10) ≈ 9.335·10²³` (certificate: `9.360·10²³`). -/
theorem shell_121 :
    ((18547958045095788140896 : ℚ) : ℝ) * (((52 : ℝ) + 0.6) - (logNatHi 10 : ℝ))
      ≤ ∑ p ∈ shellPrimes highN 121, Real.log (sigma p 121) := by
  apply shell_contribution_ge 121 2 18547958045095788140896 ((52 : ℝ) + 0.6)
    (logNatHi 10 : ℝ) 74448583843323114946560
  · norm_num
  · norm_num
  · norm_num [highN]
  · norm_num [highN]
  · norm_num [highN]
  · norm_num [highN]
  · native_decide
  · norm_num [lbLoQ, logNatHi]
  · norm_num [laLoQ, logNatHi]
  · norm_num [lbUpQ, logNatLo]
  · norm_num
  · norm_num
  · norm_num [lbLoQ, laLoQ, lbUpQ, logNatHi, logNatLo, highN]
  · native_decide
  · norm_num
  · have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.6 : ℝ) by norm_num)
      (show (0.6 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact log_ge_of 74448583843323114946560 (by norm_num) 52 0.6 _ hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  · exact log_le_logNatHi_of_le (K := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end Erdos320
