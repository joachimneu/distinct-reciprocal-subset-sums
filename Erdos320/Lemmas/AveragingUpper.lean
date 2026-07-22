import Erdos320.Lemmas.AveragingSetup
import Erdos320.Defs.Averaging
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Upper half of the averaging relation (`prop:averaging-relation`)

The manuscript's `prop:averaging-relation` asserts that
`𝓡(X) := F(e^X) − 𝓑(X)` satisfies `|𝓡(X)| ≪ (log X)²/X`.  This file proves the
**upper** half in fully explicit-constant form at the standing threshold
`X ≥ 10⁷` of `AveragingSetup`:
```
averaging_upper : F(e^X) − 𝓑(X) ≤ 7·(log X)²/X       (X ≥ 10⁷)
```
(and the alias `averagingError_le` for `𝓡(X) = averagingError X`).

Route, following the paper (with the paper's `O`-steps replaced by the
explicit inputs of `AveragingSetup`):

1. **Bridge** (`avg_bridge_le`): `F(e^X) ≤ (X/N)·g(N) + 1/X²` for
   `N = ⌊e^X⌋` — the paper's temporary normalization by `X/N` rather than
   `X/e^X` ("their difference is exponentially smaller than the stated
   error"), with the change certified `≤ X·log 2/e^X ≤ 1/X²`.
2. **Shell decomposition** (`g_shell_decomposition` + `core_normalized_le`):
   `(X/N)·g(N) ≤ (X/N)·Σ_{m≤M} Σ_{p ∈ shell m} log σ_p(m) + 3/X²`.
3. **Per-prime cap** (`avg_log_sigma_le_min`): on the `m`-th shell,
   `log σ_p(m) ≤ min(g(m), X)` — the paper's `log σ_p(m) ≤ min(g(m), log p)`
   with `log p ≤ X − log m ≤ X`.  (On the upper side the shell-dependent cap
   `X − log m` is simply enlarged to the common cap `X`, so no cap-transport
   estimate is needed.)
4. **Shell count** (`avg_normalized_shell_count_le`): the FKS input
   (`primeInterval_upper`) gives
   `(X/N)·P_m ≤ (1 + 2(log(m+1)+1)/X)/(m(m+1)) + (X/N)(𝓔(N/m)+𝓔(N/(m+1)))`,
   the explicit form of eq. `prime-shell-sum`, using `log y_m ≥ X − log(m+1) − 1`
   and `X − log(m+1) − 1 ≥ X/2`.
5. **Summation**: the main terms reindex into a partial sum of `𝓑(X)`
   (`avg_min_capped_sum_le_B` — every `BTerm` is nonnegative, so the partial
   sum is at most the full `tsum`; the paper's tail simply helps the upper
   side), the cap-error sum is `≤ 6.8·(log X)²/X` (`avg_cap_error_sum_le`,
   via `sum_log_succ_div_succ_le`), and the total FKS error is `≤ 1/X`
   (`fks_shell_total_le` times the cap `X`).

**Constant bookkeeping** (all at `X ≥ 10⁷`, i.e. `L := log X ≥ 16`): the
paper's `O((log X)²/X)` becomes
`1/X² (bridge) + 3/X² (core) + 6.8·L²/X (cap error) + 1/X (FKS) ≤ 7·L²/X`.
The binding term is the cap error: `2·log 2·((log 2 + 3L)²/2 + 2 + log 2 + 3L)
≤ 2·log 2·4.85·L² ≤ 6.74·L²` (worst at `L = 16`, margin ≈ 1.5%); everything
else is dwarfed (`1/X ≤ L²/(256X)`).
-/

namespace Erdos320

/-! ## Elementary numeric estimates on `log X` at the standing threshold -/

/-- `log X ≥ 16` for `X ≥ 10⁷` (indeed `log 10⁷ = 16.118…`); the explicit
lower bound on `L = log X` used to absorb the lower-order terms of the
averaging error into the `(log X)²` main term. -/
theorem avg_sixteen_le_log {X : ℝ} (hX : (10 : ℝ) ^ 7 ≤ X) : (16 : ℝ) ≤ Real.log X :=
  sixteen_le_log hX

/-- `log X ≤ X/1581` for `X ≥ 10⁷` — the crude sublinearity of `log`
(via `log X = 2·log √X ≤ 2√X` and `√X ≥ 3162`) that keeps the shell-count
denominator `X − log(m+1) − 1` above `X/2` uniformly over the shells. -/
theorem avg_log_le_div_const {X : ℝ} (hX : (10 : ℝ) ^ 7 ≤ X) :
    Real.log X ≤ X / 1581 := by
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le (by norm_num) hX
  have hs0 : (0 : ℝ) < Real.sqrt X := Real.sqrt_pos.mpr hX0
  have hs : (3162 : ℝ) ≤ Real.sqrt X := by
    have h1 : Real.sqrt ((3162 : ℝ) ^ 2) ≤ Real.sqrt X :=
      Real.sqrt_le_sqrt (le_trans (by norm_num) hX)
    rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3162)] at h1
  have hmul : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hX0.le
  have hlog : Real.log X ≤ 2 * Real.sqrt X := by
    have h1 : Real.log (Real.sqrt X) ≤ Real.sqrt X - 1 :=
      Real.log_le_sub_one_of_pos hs0
    have h2 : Real.log (Real.sqrt X) = Real.log X / 2 := Real.log_sqrt hX0.le
    linarith
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 1581)]
  have h3 : (3162 : ℝ) * Real.sqrt X ≤ Real.sqrt X * Real.sqrt X :=
    mul_le_mul_of_nonneg_right hs hs0.le
  nlinarith

/-- Uniform logarithmic bound over the shell indices: `log(m+1) ≤ log 2 + 3·log X`
for `m ≤ M = ⌊X³⌋` (from `m + 1 ≤ X³ + 1 ≤ 2X³`). -/
theorem avg_shell_log_le {X : ℝ} (hX : (10 : ℝ) ^ 7 ≤ X) {m : ℕ}
    (hm : m ≤ shellCutoff X) :
    Real.log ((m : ℝ) + 1) ≤ Real.log 2 + 3 * Real.log X :=
  shell_log_add_one_le (le_trans (by norm_num) hX) hm

/-- The shell-count denominator stays above `X/2`:
`X/2 ≤ X − log(m+1) − 1` for every shell index `m ≤ M`, `X ≥ 10⁷`.  This is
the explicit form of the paper's shell-endpoint lower bound
`log y_m ≥ X − 3·log X − O(1)` (proof of `prop:averaging-relation`, before
eq. `prime-shell-sum`). -/
theorem avg_cap_denom_ge_half {X : ℝ} (hX : (10 : ℝ) ^ 7 ≤ X) {m : ℕ}
    (hm : m ≤ shellCutoff X) :
    X / 2 ≤ X - Real.log ((m : ℝ) + 1) - 1 := by
  have h1 := avg_shell_log_le hX hm
  have h2 := avg_log_le_div_const hX
  linarith [log_two_le_one]

/-! ## Step 1: the bridge `F(e^X) ≤ (X/N)·g(N) + 1/X²` -/

/-- **Bridge to the floor normalization**: `F(e^X) ≤ (X/N)·g(N) + 1/X²` for
`N = ⌊e^X⌋`, `X ≥ 10⁷`.  The paper's temporary normalization by `X/N` rather
than `X/e^X` (`prop:averaging-relation` statement: "their difference is
exponentially smaller than the stated error"), with the change
bounded through `abs_FReal_exp_sub_div_floor` by `X·log 2/e^X ≤ X³/e^X ≤ 1/X²`
(the last step from `e^X > 64X⁶`, `exp_gt_poly`). -/
theorem avg_bridge_le {X : ℝ} (hX : (10 : ℝ) ^ 7 ≤ X) :
    FReal (Real.exp X)
      ≤ X / (⌊Real.exp X⌋₊ : ℝ) * g ⌊Real.exp X⌋₊ + 1 / X ^ 2 := by
  have hX1 : (1 : ℝ) ≤ X := le_trans (by norm_num) hX
  have hX0 : (0 : ℝ) < X := by linarith
  have h1 := (abs_le.mp (abs_FReal_exp_sub_div_floor hX1)).2
  have h2 : X * Real.log 2 / Real.exp X ≤ 1 / X ^ 2 := by
    rw [div_le_div_iff₀ (Real.exp_pos X) (pow_pos hX0 2)]
    have hpoly := exp_gt_poly hX
    have hlog2 : Real.log 2 ≤ 1 := log_two_le_one
    have h36 : X ^ 3 ≤ X ^ 6 := by
      have hX3 : (1 : ℝ) ≤ X ^ 3 := one_le_pow₀ hX1
      nlinarith [mul_nonneg (pow_nonneg hX0.le 3) (sub_nonneg.mpr hX3)]
    have hl2X3 : Real.log 2 * X ^ 3 ≤ 1 * X ^ 3 :=
      mul_le_mul_of_nonneg_right hlog2 (by positivity)
    nlinarith [pow_nonneg hX0.le 6]
  linarith

/-! ## Step 3: the per-prime cap `log σ_p(m) ≤ min(g(m), X)` -/

/-- On the shells of `prop:averaging-relation` the shell index is far below
the shell primes: `m < p` for `p` in the `m`-th shell of `N = ⌊e^X⌋`, `m ≤ M`,
`X ≥ 10⁷` (since `m ≤ X³ < 30X⁴ ≤ e^{X/2} ≤ N/(m+1) < p`).  This is the
size condition `m < p` under which `σ_p(m) ≤ S(m)` (`sigma_le_S`) applies. -/
theorem avg_shell_index_lt_prime {X : ℝ} (hX : (10 : ℝ) ^ 7 ≤ X) {m p : ℕ}
    (hm : m ≤ shellCutoff X) (hp : p ∈ shellPrimes ⌊Real.exp X⌋₊ m) :
    m < p := by
  have hX1 : (1 : ℝ) ≤ X := le_trans (by norm_num) hX
  have hX0 : (0 : ℝ) < X := by linarith
  have h1 : (m : ℝ) ≤ X ^ 3 :=
    le_trans (Nat.cast_le.mpr hm) (shellCutoff_cast_le hX0.le)
  have h2 := half_exp_le_shell_ratio hX hm
  have h3 := shell_ratio_lt_shell_prime hp
  have h4 := poly_le_exp_half hX
  have h5 : X ^ 3 ≤ X ^ 4 := by
    have hX3 : (0 : ℝ) ≤ X ^ 3 := by positivity
    nlinarith [mul_nonneg hX3 (sub_nonneg.mpr hX1)]
  have h6 : (m : ℝ) < (p : ℝ) := by
    have h7 : (0 : ℝ) < X ^ 4 := pow_pos hX0 4
    linarith
  exact_mod_cast h6

/-- **Per-prime cap** (`prop:averaging-relation` proof:
`log σ_p(m) ≤ min(g(m), log p) ≤ τ_m`): on the `m`-th shell (`1 ≤ m ≤ M`,
`X ≥ 10⁷`), `log σ_p(m) ≤ min(g(m), X)`.  The `g(m)` branch is
`σ_p(m) ≤ S(m)` (`sigma_le_S`, using `m < p`); the `X` branch is
`σ_p(m) ≤ p` and `log p ≤ X − log m ≤ X` (`shell_prime_le_log`) — enlarging
the shell-dependent bound `X − log m` to the paper's common cap `X` is
harmless on the upper side. -/
theorem avg_log_sigma_le_min {X : ℝ} (hX : (10 : ℝ) ^ 7 ≤ X) {m p : ℕ}
    (hm1 : 1 ≤ m) (hmM : m ≤ shellCutoff X)
    (hp : p ∈ shellPrimes ⌊Real.exp X⌋₊ m) :
    Real.log (sigma p m) ≤ min (g m) X := by
  obtain ⟨-, -, hprime⟩ := mem_shellPrimes.mp hp
  have hmp : m < p := avg_shell_index_lt_prime hX hmM hp
  have hσ1 : (1 : ℝ) ≤ ((sigma p m : ℕ) : ℝ) := by
    exact_mod_cast one_le_sigma p m
  refine le_min ?_ ?_
  · -- branch `≤ g m` via `σ_p(m) ≤ S(m)`
    have hσS : ((sigma p m : ℕ) : ℝ) ≤ ((S m : ℕ) : ℝ) :=
      Nat.cast_le.mpr (sigma_le_S hprime hmp)
    have hg : g m = Real.log (S m) := rfl
    rw [hg]
    exact Real.log_le_log (by linarith) hσS
  · -- branch `≤ X` via `σ_p(m) ≤ p` and `log p ≤ X − log m`
    have hσp : ((sigma p m : ℕ) : ℝ) ≤ (p : ℝ) :=
      Nat.cast_le.mpr (sigma_le_self hprime.pos m)
    have h1 : Real.log (sigma p m) ≤ Real.log p :=
      Real.log_le_log (by linarith) hσp
    have h2 : Real.log p ≤ X - Real.log m := shell_prime_le_log hm1 hp
    have h3 : (0 : ℝ) ≤ Real.log (m : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hm1)
    linarith

/-- **Per-shell sum bound**: the `m`-th shell contributes at most
`P_m · min(g(m), X)` — every one of the `P_m = |shellPrimes N m|` prime
factors is capped by `avg_log_sigma_le_min`. -/
theorem avg_shell_sum_le_card_mul {X : ℝ} (hX : (10 : ℝ) ^ 7 ≤ X) {m : ℕ}
    (hm1 : 1 ≤ m) (hmM : m ≤ shellCutoff X) :
    ∑ p ∈ shellPrimes ⌊Real.exp X⌋₊ m, Real.log (sigma p m)
      ≤ ((shellPrimes ⌊Real.exp X⌋₊ m).card : ℝ) * min (g m) X := by
  have h := Finset.sum_le_card_nsmul (shellPrimes ⌊Real.exp X⌋₊ m)
    (fun p => Real.log (sigma p m)) (min (g m) X)
    (fun p hp => avg_log_sigma_le_min hX hm1 hmM hp)
  simpa [nsmul_eq_mul] using h

/-! ## Step 4: the normalized shell count -/

/-- **Explicit normalized shell count, upper side** — the explicit form of
eq. `prime-shell-sum` in `prop:averaging-relation`:
```
(X/N)·P_m ≤ (1 + 2(log(m+1)+1)/X) / (m(m+1)) + (X/N)(𝓔(N/m) + 𝓔(N/(m+1)))
```
for `1 ≤ m ≤ M`, `X ≥ 10⁷`.  Route: `P_m = π(N/m) − π(N/(m+1))`
(`shellPrimes_card_cast_eq`), the FKS interval count `primeInterval_upper`
with exact endpoint gap `N/m − N/(m+1) = N/(m(m+1))`, the endpoint-log lower
bound `log(N/(m+1)) ≥ X − log(m+1) − 1`, and
`X/(X − log(m+1) − 1) ≤ 1 + 2(log(m+1)+1)/X` (valid since the denominator is
`≥ X/2`, `avg_cap_denom_ge_half`). -/
theorem avg_normalized_shell_count_le {X : ℝ} (hX : (10 : ℝ) ^ 7 ≤ X) {m : ℕ}
    (hm1 : 1 ≤ m) (hmM : m ≤ shellCutoff X) :
    X / (⌊Real.exp X⌋₊ : ℝ) * ((shellPrimes ⌊Real.exp X⌋₊ m).card : ℝ)
      ≤ (1 + 2 * (Real.log ((m : ℝ) + 1) + 1) / X) / ((m : ℝ) * ((m : ℝ) + 1))
        + X / (⌊Real.exp X⌋₊ : ℝ)
            * (fksError ((⌊Real.exp X⌋₊ : ℝ) / (m : ℝ))
              + fksError ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1))) := by
  have hX1 : (1 : ℝ) ≤ X := le_trans (by norm_num) hX
  have hX0 : (0 : ℝ) < X := by linarith
  have hN1 : 1 ≤ ⌊Real.exp X⌋₊ := one_le_expFloor hX1
  have hNR : (0 : ℝ) < (⌊Real.exp X⌋₊ : ℝ) := by exact_mod_cast hN1
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
  have hm10 : (0 : ℝ) < (m : ℝ) + 1 := by linarith
  have hXN0 : (0 : ℝ) ≤ X / (⌊Real.exp X⌋₊ : ℝ) := by positivity
  -- endpoint size facts
  have h2a : (2 : ℝ) ≤ (⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1) := two_le_shell_ratio hX hmM
  have hab : (⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1) ≤ (⌊Real.exp X⌋₊ : ℝ) / (m : ℝ) :=
    div_add_one_le_div (Nat.cast_nonneg _) hm0
  -- lower bound on the log of the left endpoint
  have hloga : X - Real.log ((m : ℝ) + 1) - 1
      ≤ Real.log ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1)) := by
    have hN2 : Real.exp X / 2 ≤ (⌊Real.exp X⌋₊ : ℝ) := exp_div_two_le_expFloor hX1
    have hlow : Real.exp X / 2 / ((m : ℝ) + 1) ≤ (⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1) :=
      div_le_div_of_nonneg_right hN2 (by positivity)
    have hlogle : Real.log (Real.exp X / 2 / ((m : ℝ) + 1))
        ≤ Real.log ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1)) :=
      Real.log_le_log (by positivity) hlow
    have hsplit : Real.log (Real.exp X / 2 / ((m : ℝ) + 1))
        = X - Real.log 2 - Real.log ((m : ℝ) + 1) :=
      log_exp_div_two_div (by positivity) X
    linarith [log_two_le_one]
  have hDhalf : X / 2 ≤ X - Real.log ((m : ℝ) + 1) - 1 := avg_cap_denom_ge_half hX hmM
  have hD0 : (0 : ℝ) < X - Real.log ((m : ℝ) + 1) - 1 := by linarith
  have hla0 : (0 : ℝ) < Real.log ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1)) :=
    lt_of_lt_of_le hD0 hloga
  have hd0 : (0 : ℝ) ≤ Real.log ((m : ℝ) + 1) + 1 := by
    have h := Real.log_nonneg (by linarith : (1 : ℝ) ≤ (m : ℝ) + 1)
    linarith
  -- the endpoint gap is exactly `N/(m(m+1))`
  have hba : (⌊Real.exp X⌋₊ : ℝ) / (m : ℝ) - (⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1)
      = (⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) * ((m : ℝ) + 1)) :=
    shell_endpoint_gap hm0
  -- `X / log(N/(m+1)) ≤ 1 + 2(log(m+1)+1)/X`
  have hXoverD : X / Real.log ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1))
      ≤ 1 + 2 * (Real.log ((m : ℝ) + 1) + 1) / X := by
    have hstep1 : X / Real.log ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1))
        ≤ X / (X - Real.log ((m : ℝ) + 1) - 1) := by
      rw [div_le_div_iff₀ hla0 hD0]
      exact mul_le_mul_of_nonneg_left hloga hX0.le
    have hstep2 : X / (X - Real.log ((m : ℝ) + 1) - 1)
        ≤ 1 + 2 * (Real.log ((m : ℝ) + 1) + 1) / X := by
      have heq : 1 + 2 * (Real.log ((m : ℝ) + 1) + 1) / X
          = (X + 2 * (Real.log ((m : ℝ) + 1) + 1)) / X := by
        field_simp
      rw [heq, div_le_div_iff₀ hD0 hX0]
      nlinarith [mul_nonneg hd0
        (by linarith : (0 : ℝ) ≤ X - 2 * (Real.log ((m : ℝ) + 1) + 1))]
    linarith
  -- assemble
  have hcard := shellPrimes_card_cast_eq ⌊Real.exp X⌋₊ hm1
  have hup := primeInterval_upper h2a hab
  calc X / (⌊Real.exp X⌋₊ : ℝ) * ((shellPrimes ⌊Real.exp X⌋₊ m).card : ℝ)
      = X / (⌊Real.exp X⌋₊ : ℝ)
          * ((primePi ((⌊Real.exp X⌋₊ : ℝ) / (m : ℝ)) : ℝ)
            - (primePi ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1)) : ℝ)) := by
        rw [hcard]
    _ ≤ X / (⌊Real.exp X⌋₊ : ℝ)
          * (((⌊Real.exp X⌋₊ : ℝ) / (m : ℝ) - (⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1))
              / Real.log ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1))
            + fksError ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1))
            + fksError ((⌊Real.exp X⌋₊ : ℝ) / (m : ℝ))) :=
        mul_le_mul_of_nonneg_left hup hXN0
    _ = X / (⌊Real.exp X⌋₊ : ℝ)
          * ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) * ((m : ℝ) + 1))
              / Real.log ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1)))
        + X / (⌊Real.exp X⌋₊ : ℝ)
            * (fksError ((⌊Real.exp X⌋₊ : ℝ) / (m : ℝ))
              + fksError ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1))) := by
        rw [hba]
        ring
    _ ≤ (1 + 2 * (Real.log ((m : ℝ) + 1) + 1) / X) / ((m : ℝ) * ((m : ℝ) + 1))
        + X / (⌊Real.exp X⌋₊ : ℝ)
            * (fksError ((⌊Real.exp X⌋₊ : ℝ) / (m : ℝ))
              + fksError ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1))) := by
        have hmain_eq : X / (⌊Real.exp X⌋₊ : ℝ)
            * ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) * ((m : ℝ) + 1))
                / Real.log ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1)))
            = (X / Real.log ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1)))
                / ((m : ℝ) * ((m : ℝ) + 1)) := by
          field_simp
        have hmono : (X / Real.log ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1)))
              / ((m : ℝ) * ((m : ℝ) + 1))
            ≤ (1 + 2 * (Real.log ((m : ℝ) + 1) + 1) / X) / ((m : ℝ) * ((m : ℝ) + 1)) :=
          div_le_div_of_nonneg_right hXoverD (by positivity)
        linarith [hmain_eq ▸ hmono]

/-! ## Step 4': the capped, normalized per-shell term -/

/-- **Capped normalized shell term** — one shell's full contribution to the
upper bound of eq. `shell-upper`:
```
(X/N)·P_m·min(g(m),X) ≤ min(g(m),X)/(m(m+1))              (main term → 𝓑)
    + 2·log 2·(log(m+1)+1)/(X(m+1))                       (cap error)
    + X·(X/N)(𝓔(N/m)+𝓔(N/(m+1)))                          (FKS error)
```
using `min(g(m),X) ≤ m·log 2` (`g_le_mul_log_two`) on the error term and
`min(g(m),X) ≤ X` on the FKS term. -/
theorem avg_capped_shell_term_le {X : ℝ} (hX : (10 : ℝ) ^ 7 ≤ X) {m : ℕ}
    (hm1 : 1 ≤ m) (hmM : m ≤ shellCutoff X) :
    X / (⌊Real.exp X⌋₊ : ℝ)
        * (((shellPrimes ⌊Real.exp X⌋₊ m).card : ℝ) * min (g m) X)
      ≤ min (g m) X / ((m : ℝ) * ((m : ℝ) + 1))
        + 2 * Real.log 2 * (Real.log ((m : ℝ) + 1) + 1) / (X * ((m : ℝ) + 1))
        + X * (X / (⌊Real.exp X⌋₊ : ℝ)
            * (fksError ((⌊Real.exp X⌋₊ : ℝ) / (m : ℝ))
              + fksError ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1)))) := by
  have hX1 : (1 : ℝ) ≤ X := le_trans (by norm_num) hX
  have hX0 : (0 : ℝ) < X := by linarith
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
  have hm10 : (0 : ℝ) < (m : ℝ) + 1 := by linarith
  have hc0 : (0 : ℝ) ≤ min (g m) X := le_min (g_nonneg m) hX0.le
  have hcX : min (g m) X ≤ X := min_le_right _ _
  have hcg : min (g m) X ≤ (m : ℝ) * Real.log 2 :=
    le_trans (min_le_left _ _) (g_le_mul_log_two m)
  have hd0 : (0 : ℝ) ≤ Real.log ((m : ℝ) + 1) + 1 := by
    have h := Real.log_nonneg (by linarith : (1 : ℝ) ≤ (m : ℝ) + 1)
    linarith
  have hF0 : (0 : ℝ) ≤ X / (⌊Real.exp X⌋₊ : ℝ)
      * (fksError ((⌊Real.exp X⌋₊ : ℝ) / (m : ℝ))
        + fksError ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1))) := by
    have h1 : (0 : ℝ) ≤ fksError ((⌊Real.exp X⌋₊ : ℝ) / (m : ℝ)) :=
      fksError_nonneg (by positivity)
    have h2 : (0 : ℝ) ≤ fksError ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1)) :=
      fksError_nonneg (by positivity)
    exact mul_nonneg (by positivity) (by linarith)
  have hcount := avg_normalized_shell_count_le hX hm1 hmM
  -- multiply the count bound by the (nonnegative) cap
  have h1 : min (g m) X
        * (X / (⌊Real.exp X⌋₊ : ℝ) * ((shellPrimes ⌊Real.exp X⌋₊ m).card : ℝ))
      ≤ min (g m) X
        * ((1 + 2 * (Real.log ((m : ℝ) + 1) + 1) / X) / ((m : ℝ) * ((m : ℝ) + 1))
          + X / (⌊Real.exp X⌋₊ : ℝ)
              * (fksError ((⌊Real.exp X⌋₊ : ℝ) / (m : ℝ))
                + fksError ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1)))) :=
    mul_le_mul_of_nonneg_left hcount hc0
  -- expand `cap · main` (a pure ring identity: no cancellation needed)
  have hexp : min (g m) X
        * ((1 + 2 * (Real.log ((m : ℝ) + 1) + 1) / X) / ((m : ℝ) * ((m : ℝ) + 1)))
      = min (g m) X / ((m : ℝ) * ((m : ℝ) + 1))
        + 2 * (min (g m) X * (Real.log ((m : ℝ) + 1) + 1))
            / (X * ((m : ℝ) * ((m : ℝ) + 1))) := by
    field_simp
  -- dominate the cap error using `min(g(m),X) ≤ m·log 2` (the `m` cancels)
  have hmid : 2 * (min (g m) X * (Real.log ((m : ℝ) + 1) + 1))
          / (X * ((m : ℝ) * ((m : ℝ) + 1)))
      ≤ 2 * Real.log 2 * (Real.log ((m : ℝ) + 1) + 1) / (X * ((m : ℝ) + 1)) := by
    have hnum : 2 * (min (g m) X * (Real.log ((m : ℝ) + 1) + 1))
        ≤ 2 * ((m : ℝ) * Real.log 2 * (Real.log ((m : ℝ) + 1) + 1)) := by
      have h := mul_le_mul_of_nonneg_right hcg hd0
      linarith
    have hstep : 2 * (min (g m) X * (Real.log ((m : ℝ) + 1) + 1))
            / (X * ((m : ℝ) * ((m : ℝ) + 1)))
        ≤ 2 * ((m : ℝ) * Real.log 2 * (Real.log ((m : ℝ) + 1) + 1))
            / (X * ((m : ℝ) * ((m : ℝ) + 1))) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    have heq : 2 * ((m : ℝ) * Real.log 2 * (Real.log ((m : ℝ) + 1) + 1))
            / (X * ((m : ℝ) * ((m : ℝ) + 1)))
        = 2 * Real.log 2 * (Real.log ((m : ℝ) + 1) + 1) / (X * ((m : ℝ) + 1)) := by
      field_simp
    linarith [heq ▸ hstep]
  -- dominate the FKS error using `min(g(m),X) ≤ X`
  have hfks : min (g m) X
        * (X / (⌊Real.exp X⌋₊ : ℝ)
          * (fksError ((⌊Real.exp X⌋₊ : ℝ) / (m : ℝ))
            + fksError ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1))))
      ≤ X * (X / (⌊Real.exp X⌋₊ : ℝ)
          * (fksError ((⌊Real.exp X⌋₊ : ℝ) / (m : ℝ))
            + fksError ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1)))) :=
    mul_le_mul_of_nonneg_right hcX hF0
  -- combine
  have hcomm : X / (⌊Real.exp X⌋₊ : ℝ)
        * (((shellPrimes ⌊Real.exp X⌋₊ m).card : ℝ) * min (g m) X)
      = min (g m) X
        * (X / (⌊Real.exp X⌋₊ : ℝ) * ((shellPrimes ⌊Real.exp X⌋₊ m).card : ℝ)) := by
    ring
  have hdistrib : min (g m) X
        * ((1 + 2 * (Real.log ((m : ℝ) + 1) + 1) / X) / ((m : ℝ) * ((m : ℝ) + 1))
          + X / (⌊Real.exp X⌋₊ : ℝ)
              * (fksError ((⌊Real.exp X⌋₊ : ℝ) / (m : ℝ))
                + fksError ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1))))
      = min (g m) X
          * ((1 + 2 * (Real.log ((m : ℝ) + 1) + 1) / X) / ((m : ℝ) * ((m : ℝ) + 1)))
        + min (g m) X
            * (X / (⌊Real.exp X⌋₊ : ℝ)
              * (fksError ((⌊Real.exp X⌋₊ : ℝ) / (m : ℝ))
                + fksError ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1)))) := by
    ring
  linarith [hcomm ▸ h1, hdistrib, hexp, hmid, hfks]

/-! ## Step 5: summation -/

/-- **Partial `𝓑`-sum bound**: `Σ_{m=1}^{M} min(g(m),X)/(m(m+1)) ≤ 𝓑(X)` for
any cutoff `M` and any `X ≥ 0` — the main terms of the shells form a partial
sum of the series `𝓑(X)` (eq. `B-def`), whose terms are all nonnegative, so
the omitted tail only helps the upper bound. -/
theorem avg_min_capped_sum_le_B {X : ℝ} (hX0 : 0 ≤ X) (M : ℕ) :
    ∑ m ∈ Finset.Icc 1 M, min (g m) X / ((m : ℝ) * ((m : ℝ) + 1)) ≤ B X := by
  have hre : ∑ m ∈ Finset.Icc 1 M, min (g m) X / ((m : ℝ) * ((m : ℝ) + 1))
      = ∑ k ∈ Finset.range M, BTerm X k := by
    have hIcc : Finset.Icc 1 M = Finset.Ico 1 (M + 1) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega
    rw [hIcc, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [BTerm]
    rw [Nat.add_comm 1 k]
    push_cast
    ring_nf
  rw [hre]
  refine Summable.sum_le_tsum (Finset.range M) (fun k _ => ?_) (summable_BTerm X)
  simp only [BTerm]
  exact div_nonneg (le_min (g_nonneg _) hX0) (by positivity)

/-- **Cap-error sum**: the total error from replacing each shell's exact
count weight by `1/(m(m+1))` is
`Σ_{m=1}^{M} 2·log 2·(log(m+1)+1)/(X(m+1)) ≤ 6.8·(log X)²/X` for `X ≥ 10⁷`
(paper: the two `O((log X)²/X)` displays around eq. `shell-upper`).  Uses
`sum_log_succ_div_succ_le` (`Σ log(m+1)/(m+1) ≤ log²(M+1)/2 + 1`),
`sum_one_div_le_log`, and `log(M+1) ≤ log 2 + 3·log X`; the constant `6.8`
comes from `2·log 2·((log 2 + 3L)²/2 + 2 + log 2 + 3L) ≤ 2·log 2·4.85·L²
≤ 6.74·L²` at `L = log X ≥ 16` (worst case `L = 16`, margin ≈ 1.5%). -/
theorem avg_cap_error_sum_le {X : ℝ} (hX : (10 : ℝ) ^ 7 ≤ X) :
    ∑ m ∈ Finset.Icc 1 (shellCutoff X),
        2 * Real.log 2 * (Real.log ((m : ℝ) + 1) + 1) / (X * ((m : ℝ) + 1))
      ≤ 6.8 * Real.log X ^ 2 / X := by
  have hX1 : (1 : ℝ) ≤ X := le_trans (by norm_num) hX
  have hX0 : (0 : ℝ) < X := by linarith
  have hl2u : Real.log 2 ≤ 0.694 := by linarith [Real.log_two_lt_d9]
  have hl20 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hL := avg_sixteen_le_log hX
  have hM1 : 1 ≤ shellCutoff X := one_le_shellCutoff hX1
  have hMR : (0 : ℝ) < ((shellCutoff X : ℕ) : ℝ) := by exact_mod_cast hM1
  have hXinv0 : (0 : ℝ) ≤ 2 * Real.log 2 / X := by positivity
  -- split each term into the `log/(m+1)` and `1/(m+1)` pieces
  have hchain : ∑ m ∈ Finset.Icc 1 (shellCutoff X),
        2 * Real.log 2 * (Real.log ((m : ℝ) + 1) + 1) / (X * ((m : ℝ) + 1))
      = 2 * Real.log 2 / X
          * ∑ m ∈ Finset.Icc 1 (shellCutoff X), Real.log ((m : ℝ) + 1) / ((m : ℝ) + 1)
        + 2 * Real.log 2 / X
            * ∑ m ∈ Finset.Icc 1 (shellCutoff X), 1 / ((m : ℝ) + 1) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    have hm10 : ((m : ℝ) + 1) ≠ 0 := by positivity
    field_simp
  -- the two series bounds
  have hS1 : ∑ m ∈ Finset.Icc 1 (shellCutoff X), Real.log ((m : ℝ) + 1) / ((m : ℝ) + 1)
      ≤ Real.log (((shellCutoff X : ℕ) : ℝ) + 1) ^ 2 / 2 + 1 :=
    sum_log_succ_div_succ_le (shellCutoff X)
  have hS2 : ∑ m ∈ Finset.Icc 1 (shellCutoff X), (1 : ℝ) / ((m : ℝ) + 1)
      ≤ 1 + Real.log ((shellCutoff X : ℕ) : ℝ) := by
    have h1 : ∑ m ∈ Finset.Icc 1 (shellCutoff X), (1 : ℝ) / ((m : ℝ) + 1)
        ≤ ∑ m ∈ Finset.Icc 1 (shellCutoff X), (1 : ℝ) / (m : ℝ) := by
      refine Finset.sum_le_sum fun m hm => ?_
      have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
      have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
      exact one_div_le_one_div_of_le hm0 (by linarith)
    exact le_trans h1 (sum_one_div_le_log (shellCutoff X))
  -- logarithmic size of the cutoff
  have hlogM1 : Real.log (((shellCutoff X : ℕ) : ℝ) + 1) ≤ Real.log 2 + 3 * Real.log X :=
    avg_shell_log_le hX le_rfl
  have hlogM10 : (0 : ℝ) ≤ Real.log (((shellCutoff X : ℕ) : ℝ) + 1) :=
    Real.log_nonneg (by linarith)
  have hlogM : Real.log ((shellCutoff X : ℕ) : ℝ) ≤ Real.log 2 + 3 * Real.log X := by
    have h1 : Real.log ((shellCutoff X : ℕ) : ℝ)
        ≤ Real.log (((shellCutoff X : ℕ) : ℝ) + 1) :=
      Real.log_le_log hMR (by linarith)
    linarith
  -- the combined inner bound `≤ 4.85·L²`
  have hinner : Real.log (((shellCutoff X : ℕ) : ℝ) + 1) ^ 2 / 2 + 1
        + (1 + Real.log ((shellCutoff X : ℕ) : ℝ))
      ≤ 4.85 * Real.log X ^ 2 := by
    have hsq : Real.log (((shellCutoff X : ℕ) : ℝ) + 1) ^ 2
        ≤ (Real.log 2 + 3 * Real.log X) ^ 2 := by
      nlinarith [hlogM10, hlogM1]
    have hl2L : Real.log 2 * Real.log X ≤ 0.694 * Real.log X :=
      mul_le_mul_of_nonneg_right hl2u (by linarith)
    have h16L : 16 * Real.log X ≤ Real.log X * Real.log X :=
      mul_le_mul_of_nonneg_right hL (by linarith)
    have hl2sq : Real.log 2 * Real.log 2 ≤ 0.694 * 0.694 :=
      mul_le_mul hl2u hl2u hl20 (by norm_num)
    nlinarith [hsq, hlogM, hl2u, hl20, hl2L, h16L, hl2sq]
  -- assemble
  rw [hchain]
  have hstep1 : 2 * Real.log 2 / X
        * ∑ m ∈ Finset.Icc 1 (shellCutoff X), Real.log ((m : ℝ) + 1) / ((m : ℝ) + 1)
      ≤ 2 * Real.log 2 / X * (Real.log (((shellCutoff X : ℕ) : ℝ) + 1) ^ 2 / 2 + 1) :=
    mul_le_mul_of_nonneg_left hS1 hXinv0
  have hstep2 : 2 * Real.log 2 / X
        * ∑ m ∈ Finset.Icc 1 (shellCutoff X), (1 : ℝ) / ((m : ℝ) + 1)
      ≤ 2 * Real.log 2 / X * (1 + Real.log ((shellCutoff X : ℕ) : ℝ)) :=
    mul_le_mul_of_nonneg_left hS2 hXinv0
  have hstep3 : 2 * Real.log 2 / X
          * (Real.log (((shellCutoff X : ℕ) : ℝ) + 1) ^ 2 / 2 + 1)
        + 2 * Real.log 2 / X * (1 + Real.log ((shellCutoff X : ℕ) : ℝ))
      = 2 * Real.log 2 / X
          * (Real.log (((shellCutoff X : ℕ) : ℝ) + 1) ^ 2 / 2 + 1
            + (1 + Real.log ((shellCutoff X : ℕ) : ℝ))) := by
    ring
  have hstep4 : 2 * Real.log 2 / X
        * (Real.log (((shellCutoff X : ℕ) : ℝ) + 1) ^ 2 / 2 + 1
          + (1 + Real.log ((shellCutoff X : ℕ) : ℝ)))
      ≤ 2 * Real.log 2 / X * (4.85 * Real.log X ^ 2) :=
    mul_le_mul_of_nonneg_left hinner hXinv0
  have hstep5 : 2 * Real.log 2 / X * (4.85 * Real.log X ^ 2)
      ≤ 6.8 * Real.log X ^ 2 / X := by
    have heq : 2 * Real.log 2 / X * (4.85 * Real.log X ^ 2)
        = 9.7 * Real.log 2 * Real.log X ^ 2 / X := by
      ring
    have hnum : 9.7 * Real.log 2 * Real.log X ^ 2 ≤ 6.8 * Real.log X ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_right hl2u (sq_nonneg (Real.log X))]
    rw [heq]
    exact div_le_div_of_nonneg_right hnum hX0.le
  linarith

/-! ## The upper half of the averaging relation -/

/-- **Upper half of `prop:averaging-relation`, explicit form**: for
`X ≥ 10⁷`,
```
F(e^X) − 𝓑(X) ≤ 7·(log X)²/X.
```
This certifies the upper half of the paper's `𝓡(X) ≪ (log X)²/X`
(eq. `averaging-relation`) with the explicit constant `7` and the explicit
threshold `X₀ = 10⁷` (the standing threshold of `AveragingSetup`; the paper's
claim is asymptotic).  The error decomposes as
`1/X² (floor bridge) + 3/X² (smooth core) + 6.8·(log X)²/X (cap error)
+ 1/X (FKS endpoints)`. -/
theorem averaging_upper {X : ℝ} (hX : (10 : ℝ) ^ 7 ≤ X) :
    FReal (Real.exp X) - B X ≤ 7 * Real.log X ^ 2 / X := by
  have hX1 : (1 : ℝ) ≤ X := le_trans (by norm_num) hX
  have hX0 : (0 : ℝ) < X := by linarith
  have hN1 : 1 ≤ ⌊Real.exp X⌋₊ := one_le_expFloor hX1
  have hNR : (0 : ℝ) < (⌊Real.exp X⌋₊ : ℝ) := by exact_mod_cast hN1
  have hXN0 : (0 : ℝ) ≤ X / (⌊Real.exp X⌋₊ : ℝ) := by positivity
  -- step 1: bridge to the floor normalization
  have hbridge := avg_bridge_le hX
  -- step 2: shell decomposition plus smooth-core absorption
  have hdec := (g_shell_decomposition (averaging_hQN hX) (averaging_hQ2 hX)).2
  have hdec2 := mul_le_mul_of_nonneg_left hdec hXN0
  have hcore := core_normalized_le hX
  have hdec_split : X / (⌊Real.exp X⌋₊ : ℝ)
        * ((∑ m ∈ Finset.Icc 1 (shellCutoff X),
              ∑ p ∈ shellPrimes ⌊Real.exp X⌋₊ m, Real.log (sigma p m))
          + Real.log ((harmonicSum ⌊Real.exp X⌋₊ : ℝ) + 1)
          + Real.log (smoothPart (⌊Real.exp X⌋₊ / (shellCutoff X + 1)) ⌊Real.exp X⌋₊))
      = X / (⌊Real.exp X⌋₊ : ℝ)
          * ∑ m ∈ Finset.Icc 1 (shellCutoff X),
              ∑ p ∈ shellPrimes ⌊Real.exp X⌋₊ m, Real.log (sigma p m)
        + X / (⌊Real.exp X⌋₊ : ℝ)
            * (Real.log ((harmonicSum ⌊Real.exp X⌋₊ : ℝ) + 1)
              + Real.log (smoothPart (⌊Real.exp X⌋₊ / (shellCutoff X + 1))
                  ⌊Real.exp X⌋₊)) := by
    ring
  -- step 3/4: cap each shell and bound its normalized count
  have hcap : ∑ m ∈ Finset.Icc 1 (shellCutoff X),
        ∑ p ∈ shellPrimes ⌊Real.exp X⌋₊ m, Real.log (sigma p m)
      ≤ ∑ m ∈ Finset.Icc 1 (shellCutoff X),
          ((shellPrimes ⌊Real.exp X⌋₊ m).card : ℝ) * min (g m) X := by
    refine Finset.sum_le_sum fun m hm => ?_
    obtain ⟨hm1, hmM⟩ := Finset.mem_Icc.mp hm
    exact avg_shell_sum_le_card_mul hX hm1 hmM
  have hcap2 := mul_le_mul_of_nonneg_left hcap hXN0
  have hpull : X / (⌊Real.exp X⌋₊ : ℝ)
        * ∑ m ∈ Finset.Icc 1 (shellCutoff X),
            ((shellPrimes ⌊Real.exp X⌋₊ m).card : ℝ) * min (g m) X
      = ∑ m ∈ Finset.Icc 1 (shellCutoff X),
          X / (⌊Real.exp X⌋₊ : ℝ)
            * (((shellPrimes ⌊Real.exp X⌋₊ m).card : ℝ) * min (g m) X) :=
    Finset.mul_sum _ _ _
  have hterms : ∑ m ∈ Finset.Icc 1 (shellCutoff X),
        X / (⌊Real.exp X⌋₊ : ℝ)
          * (((shellPrimes ⌊Real.exp X⌋₊ m).card : ℝ) * min (g m) X)
      ≤ ∑ m ∈ Finset.Icc 1 (shellCutoff X),
          (min (g m) X / ((m : ℝ) * ((m : ℝ) + 1))
            + 2 * Real.log 2 * (Real.log ((m : ℝ) + 1) + 1) / (X * ((m : ℝ) + 1))
            + X * (X / (⌊Real.exp X⌋₊ : ℝ)
                * (fksError ((⌊Real.exp X⌋₊ : ℝ) / (m : ℝ))
                  + fksError ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1))))) := by
    refine Finset.sum_le_sum fun m hm => ?_
    obtain ⟨hm1, hmM⟩ := Finset.mem_Icc.mp hm
    exact avg_capped_shell_term_le hX hm1 hmM
  -- step 5: split the bound into its three sums
  have hsplit : ∑ m ∈ Finset.Icc 1 (shellCutoff X),
        (min (g m) X / ((m : ℝ) * ((m : ℝ) + 1))
          + 2 * Real.log 2 * (Real.log ((m : ℝ) + 1) + 1) / (X * ((m : ℝ) + 1))
          + X * (X / (⌊Real.exp X⌋₊ : ℝ)
              * (fksError ((⌊Real.exp X⌋₊ : ℝ) / (m : ℝ))
                + fksError ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1)))))
      = (∑ m ∈ Finset.Icc 1 (shellCutoff X),
            min (g m) X / ((m : ℝ) * ((m : ℝ) + 1)))
        + (∑ m ∈ Finset.Icc 1 (shellCutoff X),
            2 * Real.log 2 * (Real.log ((m : ℝ) + 1) + 1) / (X * ((m : ℝ) + 1)))
        + (∑ m ∈ Finset.Icc 1 (shellCutoff X),
            X * (X / (⌊Real.exp X⌋₊ : ℝ)
              * (fksError ((⌊Real.exp X⌋₊ : ℝ) / (m : ℝ))
                + fksError ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1))))) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  -- the three sums: `𝓑`-partial sum, cap error, FKS error
  have hsumB := avg_min_capped_sum_le_B hX0.le (shellCutoff X)
  have hsumErr := avg_cap_error_sum_le hX
  have hsumFks : ∑ m ∈ Finset.Icc 1 (shellCutoff X),
        X * (X / (⌊Real.exp X⌋₊ : ℝ)
          * (fksError ((⌊Real.exp X⌋₊ : ℝ) / (m : ℝ))
            + fksError ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1))))
      ≤ 1 / X := by
    have heq : ∑ m ∈ Finset.Icc 1 (shellCutoff X),
          X * (X / (⌊Real.exp X⌋₊ : ℝ)
            * (fksError ((⌊Real.exp X⌋₊ : ℝ) / (m : ℝ))
              + fksError ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1))))
        = X * (X / (⌊Real.exp X⌋₊ : ℝ)
            * ∑ m ∈ Finset.Icc 1 (shellCutoff X),
                (fksError ((⌊Real.exp X⌋₊ : ℝ) / (m : ℝ))
                  + fksError ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1)))) := by
      rw [Finset.mul_sum, Finset.mul_sum]
    have h1 := fks_shell_total_le hX
    have h2 : X * (X / (⌊Real.exp X⌋₊ : ℝ)
          * ∑ m ∈ Finset.Icc 1 (shellCutoff X),
              (fksError ((⌊Real.exp X⌋₊ : ℝ) / (m : ℝ))
                + fksError ((⌊Real.exp X⌋₊ : ℝ) / ((m : ℝ) + 1))))
        ≤ X * (1 / X ^ 2) := mul_le_mul_of_nonneg_left h1 hX0.le
    have h3 : X * (1 / X ^ 2) = 1 / X := by
      field_simp
    linarith [heq ▸ h2]
  -- final numeric absorption: `6.8·L²/X + 1/X + 4/X² ≤ 7·L²/X` at `L ≥ 16`
  have hL := avg_sixteen_le_log hX
  have hnum : 6.8 * Real.log X ^ 2 / X + 1 / X + 4 / X ^ 2
      ≤ 7 * Real.log X ^ 2 / X := by
    have h256 : (256 : ℝ) ≤ Real.log X ^ 2 := by
      nlinarith [sq_nonneg (Real.log X - 16)]
    have hkey : 7 * Real.log X ^ 2 / X
          - (6.8 * Real.log X ^ 2 / X + 1 / X + 4 / X ^ 2)
        = (0.2 * Real.log X ^ 2 * X - X - 4) / X ^ 2 := by
      field_simp
      ring
    have hpos : (0 : ℝ) ≤ (0.2 * Real.log X ^ 2 * X - X - 4) / X ^ 2 := by
      apply div_nonneg _ (by positivity)
      nlinarith [mul_le_mul_of_nonneg_right h256 hX0.le]
    linarith
  -- chain the pieces in two stages to keep the linear arithmetic small
  have hchain1 : FReal (Real.exp X)
      ≤ X / (⌊Real.exp X⌋₊ : ℝ)
          * ∑ m ∈ Finset.Icc 1 (shellCutoff X),
              ∑ p ∈ shellPrimes ⌊Real.exp X⌋₊ m, Real.log (sigma p m)
        + 4 / X ^ 2 := by
    -- `1/X²`, `3/X²`, `4/X²` are distinct atoms for `linarith`; link them
    have hsc3 : (3 : ℝ) / X ^ 2 = 3 * (1 / X ^ 2) := by ring
    have hsc4 : (4 : ℝ) / X ^ 2 = 4 * (1 / X ^ 2) := by ring
    linarith [hbridge, hdec2, hdec_split, hcore, hsc3, hsc4]
  have hchain2 : X / (⌊Real.exp X⌋₊ : ℝ)
        * ∑ m ∈ Finset.Icc 1 (shellCutoff X),
            ∑ p ∈ shellPrimes ⌊Real.exp X⌋₊ m, Real.log (sigma p m)
      ≤ B X + 6.8 * Real.log X ^ 2 / X + 1 / X := by
    linarith [hcap2, hpull, hterms, hsplit, hsumB, hsumErr, hsumFks]
  linarith [hchain1, hchain2, hnum]

/-- Alias of `averaging_upper` in terms of the manuscript's averaging error
`𝓡(X) = averagingError X` (eq. `averaging-relation`):
`𝓡(X) ≤ 7·(log X)²/X` for `X ≥ 10⁷`. -/
theorem averagingError_le {X : ℝ} (hX : (10 : ℝ) ^ 7 ≤ X) :
    averagingError X ≤ 7 * Real.log X ^ 2 / X := by
  unfold averagingError
  exact averaging_upper hX

end Erdos320
