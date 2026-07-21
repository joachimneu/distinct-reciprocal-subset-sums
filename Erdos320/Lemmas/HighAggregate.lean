import Erdos320.Lemmas.HighShellTight

/-!
# The aggregate tail (shells `m ∈ [155, 10⁶]`) of the high finite input

This file proves the aggregate block contribution to
`highFiniteInput : 3.2411 < F ⌊e⁶⁵⌋`, treating the shells `m ∈ [155, 10⁶]` as a
single prime block (the certificate's `high_bridge_lower` aggregate step in
`directed_interval_certificate.py`).  The block uses the collision multiplicity
`b = 2` with the value-at-`m=154` numerator span `lcm(1..154)·H₁₅₄` (valid for
all `m ≥ 154` because `{1,…,154} ⊆ {1,…,m}`, so `sigma p m ≥ sigma p 154`
uniformly — `sigma_mono_in_m`), and the floor `S(154) ≥ sLowerBGMS 154`.

* `block_collision_lower_tight` — `shell_collision_lower_tight`
  (`HighFiniteProof.lean`) with the collision carrier `m₀` and the shell
  threshold denominator `D` decoupled (they coincide in the single-shell form);
  uses the *tight* integer-power hypothesis `W < r^(b+1)` (with the real-valued
  `log W / log r ≤ b` the aggregate would force `b = 3`, dropping the total below
  `3.2411`).
* `block_contribution_pos` — the monotone per-block bound over an abstract prime
  set `P`, mirroring `shell_contribution_pos`.
* `sigma_mono_in_m` — `σ_p(m)` is monotone in `m` (`Σ_p(m) ⊆ Σ_p(m')`).
* `blockPrimes` and the Dusart count `block_card_lower_dusart` over the wide
  interval `(⌊N/(10⁶+1)⌋, ⌊N/155⌋]`.
* `aggregate_lower` — the final block contribution
  `Cagg·(64.447897 − 9.279) ≤ ∑_{155 ≤ m ≤ 10⁶} ∑_{p} log σ_p(m)`.
-/

namespace Erdos320

open Finset

/-! ## Step 1: block collision lower bound (carrier `m₀`, threshold denominator `D`
decoupled). This is `shell_collision_lower_tight` with the two roles separated. -/

theorem block_collision_lower_tight {N m₀ D : ℕ}
    (P : Finset ℕ) (hP : P.Nonempty)
    (hprime : ∀ p ∈ P, Nat.Prime p) (hlarge : ∀ p ∈ P, m₀ < p)
    (hshell : ∀ p ∈ P, (N : ℝ) / ((D : ℝ) + 1) < (p : ℝ))
    (hbig : (1 : ℝ) < (N : ℝ) / ((D : ℝ) + 1)) (b : ℕ)
    (hWlt : (((Finset.Icc 1 m₀).lcm id : ℕ) : ℝ) * ((harmonicSum m₀ : ℚ) : ℝ)
            < ((N : ℝ) / ((D : ℝ) + 1)) ^ (b + 1)) :
    (P.card : ℝ)
        * (g m₀ - Real.log (1 + (b : ℝ) * ((S m₀ : ℝ) - 1) / (P.card : ℝ)))
      ≤ ∑ p ∈ P, Real.log ((sigma p m₀ : ℝ)) := by
  set L : ℕ := (Finset.Icc 1 m₀).lcm id with hLdef
  set T : Finset ℤ :=
    (reciprocalSubsetSumSet m₀).image (fun x : ℚ => (((L : ℕ) : ℚ) * x).num)
    with hTdef
  have hL0 : ((L : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (lcm_Icc_pos m₀).ne'
  have hden1 : ∀ x ∈ reciprocalSubsetSumSet m₀, (((L : ℕ) : ℚ) * x).den = 1 :=
    fun _x hx => mul_lcm_Icc_den_eq_one hx
  have hinj : Set.InjOn (fun x : ℚ => (((L : ℕ) : ℚ) * x).num)
      (reciprocalSubsetSumSet m₀) := by
    intro x hx y hy hxy
    have hxy' : (((L : ℕ) : ℚ) * x).num = (((L : ℕ) : ℚ) * y).num := hxy
    have hx1 : (((((L : ℕ) : ℚ) * x).num : ℤ) : ℚ) = ((L : ℕ) : ℚ) * x :=
      (Rat.den_eq_one_iff _).mp (hden1 x (Finset.mem_coe.mp hx))
    have hy1 : (((((L : ℕ) : ℚ) * y).num : ℤ) : ℚ) = ((L : ℕ) : ℚ) * y :=
      (Rat.den_eq_one_iff _).mp (hden1 y (Finset.mem_coe.mp hy))
    have hq : ((L : ℕ) : ℚ) * x = ((L : ℕ) : ℚ) * y := by
      rw [← hx1, ← hy1, hxy']
    exact mul_left_cancel₀ hL0 hq
  have hTcard : T.card = S m₀ := Finset.card_image_of_injOn hinj
  have hTne : T.Nonempty := (reciprocalSubsetSumSet_nonempty m₀).image _
  have hlogr_pos : 0 < Real.log ((N : ℝ) / ((D : ℝ) + 1)) := Real.log_pos hbig
  have hbcount : ∀ x ∈ T, ∀ y ∈ T, x ≠ y →
      (P.filter fun p : ℕ => (p : ℤ) ∣ (x - y)).card ≤ b := by
    intro x hx y hy hxy
    rw [hTdef] at hx hy
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
    have hz : (((L : ℕ) : ℚ) * u).num - (((L : ℕ) : ℚ) * v).num ≠ 0 :=
      sub_ne_zero.mpr hxy
    have hu0 : (0 : ℝ) ≤ ((((L : ℕ) : ℚ) * u).num : ℝ) := by
      exact_mod_cast lcm_Icc_scaled_num_nonneg hu
    have hv0 : (0 : ℝ) ≤ ((((L : ℕ) : ℚ) * v).num : ℝ) := by
      exact_mod_cast lcm_Icc_scaled_num_nonneg hv
    have huW : ((((L : ℕ) : ℚ) * u).num : ℝ)
        ≤ ((L : ℕ) : ℝ) * ((harmonicSum m₀ : ℚ) : ℝ) := by
      have h := (Rat.cast_le (K := ℝ)).mpr (lcm_Icc_scaled_num_le hu)
      push_cast at h
      exact h
    have hvW : ((((L : ℕ) : ℚ) * v).num : ℝ)
        ≤ ((L : ℕ) : ℝ) * ((harmonicSum m₀ : ℚ) : ℝ) := by
      have h := (Rat.cast_le (K := ℝ)).mpr (lcm_Icc_scaled_num_le hv)
      push_cast at h
      exact h
    have habs : |(((((L : ℕ) : ℚ) * u).num - (((L : ℕ) : ℚ) * v).num : ℤ) : ℝ)|
        ≤ ((L : ℕ) : ℝ) * ((harmonicSum m₀ : ℚ) : ℝ) := by
      rw [abs_le]
      push_cast
      constructor <;> linarith
    have hone : (1 : ℝ) ≤ |(((((L : ℕ) : ℚ) * u).num
        - (((L : ℕ) : ℚ) * v).num : ℤ) : ℝ)| := by
      have := Int.one_le_abs hz
      calc (1 : ℝ) = ((1 : ℤ) : ℝ) := by norm_num
        _ ≤ ((|(((L : ℕ) : ℚ) * u).num - (((L : ℕ) : ℚ) * v).num| : ℤ) : ℝ) := by
            exact_mod_cast this
        _ = |(((((L : ℕ) : ℚ) * u).num - (((L : ℕ) : ℚ) * v).num : ℤ) : ℝ)| := by
            rw [Int.cast_abs]
    have hWpos : 0 < ((L : ℕ) : ℝ) * ((harmonicSum m₀ : ℚ) : ℝ) := by
      linarith [hone.trans habs]
    have hcnt := card_filter_dvd_le_of_abs_le _ hz _ habs
      ((N : ℝ) / ((D : ℝ) + 1)) hbig P hprime hshell
    have hloglt : Real.log (((L : ℕ) : ℝ) * ((harmonicSum m₀ : ℚ) : ℝ))
        < ((b : ℝ) + 1) * Real.log ((N : ℝ) / ((D : ℝ) + 1)) := by
      have h := Real.log_lt_log hWpos hWlt
      rwa [Real.log_pow, Nat.cast_add, Nat.cast_one] at h
    have hlt : Real.log (((L : ℕ) : ℝ) * ((harmonicSum m₀ : ℚ) : ℝ))
        / Real.log ((N : ℝ) / ((D : ℝ) + 1)) < (b : ℝ) + 1 := by
      rw [div_lt_iff₀ hlogr_pos]; linarith
    have hcardlt : (((P.filter fun p : ℕ =>
        (p : ℤ) ∣ ((((L : ℕ) : ℚ) * u).num - (((L : ℕ) : ℚ) * v).num)).card : ℕ) : ℝ)
        < (b : ℝ) + 1 := lt_of_le_of_lt hcnt hlt
    have : (P.filter fun p : ℕ =>
        (p : ℤ) ∣ ((((L : ℕ) : ℚ) * u).num - (((L : ℕ) : ℚ) * v).num)).card < b + 1 := by
      exact_mod_cast hcardlt
    omega
  have hmain := average_collision_bound T hTne P hP b hbcount
  rw [hTcard] at hmain
  have himg : ∀ p ∈ P, (T.image fun x : ℤ => (x : ZMod p)).card = sigma p m₀ := by
    intro p hp
    have hpp := hprime p hp
    have hLp : ¬ p ∣ L := not_dvd_lcm_Icc_of_lt hpp (hlarge p hp)
    have h1 := card_image_intCast_scaled_eq_card_image_ratToZMod hpp hLp
      (reciprocalSubsetSumSet m₀) hden1
    rw [ratToZMod_image_reciprocalSubsetSumSet hpp (hlarge p hp)] at h1
    rw [hTdef]
    exact h1
  show (P.card : ℝ)
      * (Real.log ((S m₀ : ℕ) : ℝ)
        - Real.log (1 + (b : ℝ) * (((S m₀ : ℕ) : ℝ) - 1) / (P.card : ℝ)))
    ≤ ∑ p ∈ P, Real.log ((sigma p m₀ : ℝ))
  refine hmain.trans (le_of_eq (Finset.sum_congr rfl fun p hp => ?_))
  rw [himg p hp]

/-! ## Step 1b: block contribution lower bound over an abstract prime set `P`. -/

theorem block_contribution_pos {N m₀ D : ℕ} (b : ℕ) (Pm ℓ pen : ℝ) (sL : ℕ)
    (P : Finset ℕ) (hP : P.Nonempty)
    (hprime : ∀ p ∈ P, Nat.Prime p) (hlarge : ∀ p ∈ P, m₀ < p)
    (hshell : ∀ p ∈ P, (N : ℝ) / ((D : ℝ) + 1) < (p : ℝ))
    (hbig : (1 : ℝ) < (N : ℝ) / ((D : ℝ) + 1))
    (hWlt : (((Finset.Icc 1 m₀).lcm id : ℕ) : ℝ) * ((harmonicSum m₀ : ℚ) : ℝ)
            < ((N : ℝ) / ((D : ℝ) + 1)) ^ (b + 1))
    (hPmpos : 0 < Pm) (hPmle : Pm ≤ (P.card : ℝ))
    (hbP : (b : ℝ) ≤ Pm) (hsL1 : 1 ≤ sL) (hsLS : sL ≤ S m₀)
    (hℓ : ℓ ≤ Real.log (sL : ℝ))
    (hpen : Real.log (1 + (b : ℝ) * ((sL : ℝ) - 1) / Pm) ≤ pen) :
    Pm * (ℓ - pen) ≤ ∑ p ∈ P, Real.log (sigma p m₀) := by
  have hcoll := block_collision_lower_tight P hP hprime hlarge hshell hbig b hWlt
  refine le_trans ?_ hcoll
  set Pc : ℝ := (P.card : ℝ) with hPcdef
  set Sm : ℝ := ((S m₀ : ℕ) : ℝ) with hSmdef
  have hgeq : g m₀ = Real.log Sm := rfl
  rw [hgeq]
  have hPcpos : 0 < Pc := lt_of_lt_of_le hPmpos hPmle
  have hbnn : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b
  have hSmge1 : (1 : ℝ) ≤ Sm := by rw [hSmdef]; exact_mod_cast one_le_S m₀
  have hsLR1 : (1 : ℝ) ≤ (sL : ℝ) := by exact_mod_cast hsL1
  have hsLSm : (sL : ℝ) ≤ Sm := by rw [hSmdef]; exact_mod_cast hsLS
  have hbPc : (b : ℝ) ≤ Pc := le_trans hbP hPmle
  have hSm1 : (0 : ℝ) ≤ Sm - 1 := by linarith
  have hsL1' : (0 : ℝ) ≤ (sL : ℝ) - 1 := by linarith
  set A : ℝ := 1 + (b : ℝ) * (Sm - 1) / Pc with hAdef
  set Ap : ℝ := 1 + (b : ℝ) * (Sm - 1) / Pm with hApdef
  set App : ℝ := 1 + (b : ℝ) * ((sL : ℝ) - 1) / Pm with hAppdef
  have hApos : 0 < A := by
    rw [hAdef]; have := div_nonneg (mul_nonneg hbnn hSm1) hPcpos.le; linarith
  have hAppos : 0 < Ap := by
    rw [hApdef]; have := div_nonneg (mul_nonneg hbnn hSm1) hPmpos.le; linarith
  have hApppos : 0 < App := by
    rw [hAppdef]; have := div_nonneg (mul_nonneg hbnn hsL1') hPmpos.le; linarith
  have hAleSm : A ≤ Sm := by
    rw [hAdef]
    have h : (b : ℝ) * (Sm - 1) / Pc ≤ Sm - 1 := by
      rw [div_le_iff₀ hPcpos]; nlinarith [hbPc, hSm1]
    linarith
  have hbrk : 0 ≤ Real.log Sm - Real.log A := by
    have := Real.log_le_log hApos hAleSm; linarith
  have hAleAp : A ≤ Ap := by
    rw [hAdef, hApdef]
    have := div_le_div_of_nonneg_left (mul_nonneg hbnn hSm1) hPmpos hPmle
    linarith
  have hlogAAp : Real.log A ≤ Real.log Ap := Real.log_le_log hApos hAleAp
  have hPmne : Pm ≠ 0 := hPmpos.ne'
  have hSmono : (sL : ℝ) * Ap ≤ Sm * App := by
    rw [hApdef, hAppdef]
    refine le_of_mul_le_mul_right ?_ hPmpos
    have expand : ((sL : ℝ) * (1 + (b : ℝ) * (Sm - 1) / Pm)) * Pm
        = (sL : ℝ) * Pm + (sL : ℝ) * (b : ℝ) * (Sm - 1) := by field_simp
    have expand2 : (Sm * (1 + (b : ℝ) * ((sL : ℝ) - 1) / Pm)) * Pm
        = Sm * Pm + Sm * (b : ℝ) * ((sL : ℝ) - 1) := by field_simp
    rw [expand, expand2]
    nlinarith [mul_nonneg (by linarith [hbP] : (0 : ℝ) ≤ Pm - b)
      (by linarith : (0 : ℝ) ≤ Sm - (sL : ℝ))]
  have hlogSmono : Real.log (sL : ℝ) - Real.log App ≤ Real.log Sm - Real.log Ap := by
    have h1 : Real.log ((sL : ℝ) * Ap) ≤ Real.log (Sm * App) :=
      Real.log_le_log (by positivity) hSmono
    rw [Real.log_mul (by positivity) hAppos.ne', Real.log_mul (by positivity) hApppos.ne'] at h1
    linarith
  have hmid : ℓ - pen ≤ Real.log Sm - Real.log A := by
    have hpen' : Real.log App ≤ pen := hpen
    linarith [hℓ, hpen', hlogSmono, hlogAAp]
  calc Pm * (ℓ - pen)
      ≤ Pm * (Real.log Sm - Real.log A) :=
        mul_le_mul_of_nonneg_left hmid hPmpos.le
    _ ≤ Pc * (Real.log Sm - Real.log A) :=
        mul_le_mul_of_nonneg_right hPmle hbrk
    _ = Pc * (Real.log Sm - Real.log (1 + (b : ℝ) * (Sm - 1) / Pc)) := by rw [hAdef]

/-! ## Step 2: `sigma p m` is monotone in `m`. -/

theorem modularImage_subset_of_le (p : ℕ) {m m' : ℕ} (h : m ≤ m') :
    modularImage p m ⊆ modularImage p m' := by
  unfold modularImage
  exact Finset.image_subset_image (Finset.powerset_mono.mpr (Finset.Icc_subset_Icc_right h))

theorem sigma_mono_in_m (p : ℕ) {m m' : ℕ} (h : m ≤ m') : sigma p m ≤ sigma p m' :=
  Finset.card_le_card (modularImage_subset_of_le p h)

theorem log_sigma_mono_in_m (p : ℕ) {m m' : ℕ} (h : m ≤ m') :
    Real.log (sigma p m : ℝ) ≤ Real.log (sigma p m' : ℝ) :=
  Real.log_le_log (by exact_mod_cast one_le_sigma p m) (by exact_mod_cast sigma_mono_in_m p h)

/-! ## Step 3: the aggregate block prime set `(⌊N/(10⁶+1)⌋, ⌊N/155⌋]` and its count. -/

/-- `P_agg`: the primes of the aggregate block, `⌊N₁/(10⁶+1)⌋ < p ≤ ⌊N₁/155⌋`. -/
def blockPrimes : Finset ℕ :=
  (Finset.Ioc (highN / 1000001) (highN / 155)).filter Nat.Prime

theorem floorB : ⌊(highN : ℝ) / 155⌋₊ = highN / 155 := by
  rw [show ((highN : ℝ) / 155) = ((highN : ℝ) / ((155 : ℕ) : ℝ)) by norm_num,
    Nat.floor_div_eq_div]

theorem floorA : ⌊(highN : ℝ) / 1000001⌋₊ = highN / 1000001 := by
  rw [show ((highN : ℝ) / 1000001) = ((highN : ℝ) / ((1000001 : ℕ) : ℝ)) by norm_num,
    Nat.floor_div_eq_div]

theorem highN_div155_le : highN / 1000001 ≤ highN / 155 :=
  Nat.div_le_div_left (by omega) (by omega)

/-- `ϑ(N/155) − ϑ(N/(10⁶+1))` is the block log-sum (block analogue of
`chebyshevTheta_sub_eq_sum_shellPrimes`). -/
theorem block_theta_bridge :
    chebyshevTheta ((highN : ℝ) / 155) - chebyshevTheta ((highN : ℝ) / 1000001)
      = ∑ p ∈ blockPrimes, Real.log (p : ℝ) := by
  have hb : chebyshevTheta ((highN : ℝ) / 155)
      = ∑ p ∈ (Finset.Iic (highN / 155)).filter Nat.Prime, Real.log (p : ℝ) := by
    rw [chebyshevTheta, floorB]
  have ha : chebyshevTheta ((highN : ℝ) / 1000001)
      = ∑ p ∈ (Finset.Iic (highN / 1000001)).filter Nat.Prime, Real.log (p : ℝ) := by
    rw [chebyshevTheta, floorA]
  have hunion : (Finset.Iic (highN / 155)).filter Nat.Prime
      = (Finset.Iic (highN / 1000001)).filter Nat.Prime ∪ blockPrimes := by
    rw [blockPrimes, ← Finset.filter_union, Finset.Iic_union_Ioc_eq_Iic highN_div155_le]
  have hdisj : Disjoint ((Finset.Iic (highN / 1000001)).filter Nat.Prime) blockPrimes := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    rw [Finset.mem_filter, Finset.mem_Iic] at hp1
    rw [blockPrimes, Finset.mem_filter, Finset.mem_Ioc] at hp2
    omega
  rw [hb, ha, hunion, Finset.sum_union hdisj]
  ring

theorem block_sum_log_le :
    ∑ p ∈ blockPrimes, Real.log (p : ℝ)
      ≤ (blockPrimes.card : ℝ) * Real.log ((highN : ℝ) / 155) := by
  have hterm : ∀ p ∈ blockPrimes, Real.log (p : ℝ) ≤ Real.log ((highN : ℝ) / 155) := by
    intro p hp
    rw [blockPrimes, Finset.mem_filter, Finset.mem_Ioc] at hp
    obtain ⟨⟨_, hpb⟩, hprime⟩ := hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    refine Real.log_le_log hp0 ?_
    calc (p : ℝ) ≤ ((highN / 155 : ℕ) : ℝ) := by exact_mod_cast hpb
      _ ≤ (highN : ℝ) / ((155 : ℕ) : ℝ) := Nat.cast_div_le
      _ = (highN : ℝ) / 155 := by norm_num
  calc ∑ p ∈ blockPrimes, Real.log (p : ℝ)
      ≤ blockPrimes.card • Real.log ((highN : ℝ) / 155) :=
        Finset.sum_le_card_nsmul _ _ _ hterm
    _ = (blockPrimes.card : ℝ) * Real.log ((highN : ℝ) / 155) := by rw [nsmul_eq_mul]

theorem block_card_lower_of_theta (θlo θhi Lb : ℝ)
    (hθlo : θlo ≤ chebyshevTheta ((highN : ℝ) / 155))
    (hθhi : chebyshevTheta ((highN : ℝ) / 1000001) ≤ θhi)
    (hLb : Real.log ((highN : ℝ) / 155) ≤ Lb) (hLbpos : 0 < Lb) :
    (θlo - θhi) / Lb ≤ (blockPrimes.card : ℝ) := by
  rw [div_le_iff₀ hLbpos]
  have hcard0 : (0 : ℝ) ≤ (blockPrimes.card : ℝ) := by positivity
  have h1 : chebyshevTheta ((highN : ℝ) / 155) - chebyshevTheta ((highN : ℝ) / 1000001)
      ≤ (blockPrimes.card : ℝ) * Lb := by
    rw [block_theta_bridge]
    calc ∑ p ∈ blockPrimes, Real.log (p : ℝ)
        ≤ (blockPrimes.card : ℝ) * Real.log ((highN : ℝ) / 155) := block_sum_log_le
      _ ≤ (blockPrimes.card : ℝ) * Lb := mul_le_mul_of_nonneg_left hLb hcard0
  linarith [hθlo, hθhi, h1]

theorem block_card_lower_dusart (logbLo logaLo Lb : ℝ)
    (hbpos : 0 < logbLo) (hble : logbLo ≤ Real.log ((highN : ℝ) / 155))
    (hapos : 0 < logaLo) (hale : logaLo ≤ Real.log ((highN : ℝ) / 1000001))
    (hLb : Real.log ((highN : ℝ) / 155) ≤ Lb) (hLbpos : 0 < Lb) :
    (((highN : ℝ) / 155 - 0.006788 * ((highN : ℝ) / 155) / logbLo)
        - ((highN : ℝ) / 1000001 + 0.006788 * ((highN : ℝ) / 1000001) / logaLo)) / Lb
      ≤ (blockPrimes.card : ℝ) := by
  have hb10 : (89967803 : ℝ) ≤ (highN : ℝ) / 155 := by norm_num [highN]
  have ha10 : (89967803 : ℝ) ≤ (highN : ℝ) / 1000001 := by norm_num [highN]
  obtain ⟨hbLo, -⟩ := dusart_theta_lower_upper hb10
  obtain ⟨-, haUp⟩ := dusart_theta_lower_upper ha10
  refine block_card_lower_of_theta _ _ Lb ?_ ?_ hLb hLbpos
  · refine le_trans ?_ hbLo
    have hmono : 0.006788 * ((highN : ℝ) / 155) / Real.log ((highN : ℝ) / 155)
        ≤ 0.006788 * ((highN : ℝ) / 155) / logbLo :=
      div_le_div_of_nonneg_left (by positivity) hbpos hble
    linarith [hmono]
  · refine le_trans haUp ?_
    have hmono : 0.006788 * ((highN : ℝ) / 1000001) / Real.log ((highN : ℝ) / 1000001)
        ≤ 0.006788 * ((highN : ℝ) / 1000001) / logaLo :=
      div_le_div_of_nonneg_left (by positivity) hapos hale
    linarith [hmono]

/-- The biUnion of the shells `m ∈ [155, 10⁶]` equals `blockPrimes`. -/
theorem biUnion_shell_eq_blockPrimes :
    (Finset.Icc 155 1000000).biUnion (shellPrimes highN) = blockPrimes := by
  ext p
  simp only [Finset.mem_biUnion, Finset.mem_Icc, mem_shellPrimes, blockPrimes,
    Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨m, ⟨hm1, hmM⟩, hlo, hhi, hprime⟩
    refine ⟨⟨?_, ?_⟩, hprime⟩
    · calc highN / 1000001 ≤ highN / (m + 1) := Nat.div_le_div_left (by omega) (by omega)
        _ < p := hlo
    · calc p ≤ highN / m := hhi
        _ ≤ highN / 155 := Nat.div_le_div_left hm1 (by omega)
  · rintro ⟨⟨hAlo, hBhi⟩, hprime⟩
    have hp0 : 0 < p := hprime.pos
    have hm1 : 155 ≤ highN / p := (Nat.le_div_iff_mul_le hp0).mpr (by
      have := (Nat.le_div_iff_mul_le (by norm_num : 0 < 155)).mp hBhi
      omega)
    have hmM : highN / p ≤ 1000000 := by
      have hlt : highN < p * 1000001 := (Nat.div_lt_iff_lt_mul (by norm_num)).mp hAlo
      have : highN / p < 1000001 :=
        (Nat.div_lt_iff_lt_mul hp0).mpr (by rw [Nat.mul_comm]; exact hlt)
      omega
    have hupper : p ≤ highN / (highN / p) :=
      (Nat.le_div_iff_mul_le (by omega)).mpr (Nat.mul_div_le highN p)
    have hlower : highN / (highN / p + 1) < p := by
      apply (Nat.div_lt_iff_lt_mul (Nat.succ_pos _)).mpr
      calc highN = p * (highN / p) + highN % p := (Nat.div_add_mod highN p).symm
        _ < p * (highN / p) + p := Nat.add_lt_add_left (Nat.mod_lt highN hp0) _
        _ = p * (highN / p + 1) := by ring
    exact ⟨highN / p, ⟨hm1, hmM⟩, hlower, hupper, hprime⟩

theorem blockPrimes_prime {p : ℕ} (hp : p ∈ blockPrimes) : Nat.Prime p := by
  rw [blockPrimes, Finset.mem_filter] at hp; exact hp.2

theorem blockPrimes_gt_lo {p : ℕ} (hp : p ∈ blockPrimes) : highN / 1000001 < p := by
  rw [blockPrimes, Finset.mem_filter, Finset.mem_Ioc] at hp; exact hp.1.1

theorem highN_div_1000001 : highN / 1000001 = 16948875495227841913575 := by
  norm_num [highN]

/-! ## Step 4: the aggregate contribution lower bound. -/

set_option maxRecDepth 8000 in
/-- `log(sLowerBGMS 154) ≥ 64.447897` (the aggregate `S`-floor). -/
theorem aggregate_ell_lower :
    ((64 : ℝ) + 0.447897) ≤ Real.log ((9758124781512047322275512320 : ℕ) : ℝ) := by
  have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.447897 : ℝ) by norm_num)
    (show (0.447897 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
  exact log_ge_of 9758124781512047322275512320 (by norm_num) 64 0.447897 _ hTU
    (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])

set_option maxRecDepth 8000 in
/-- The aggregate collision penalty upper bound `log(1 + 2(sL−1)/Cagg) ≤ 9.279`. -/
theorem aggregate_pen_upper :
    Real.log (1 + ((2 : ℕ) : ℝ) * (((9758124781512047322275512320 : ℕ) : ℝ) - 1)
      / (1823261901489827785636347 : ℝ)) ≤ ((9 : ℝ) + 0.279) := by
  apply log_le_of_real _ _ 9 0.279 _ _
    (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.279 : ℝ) by norm_num) 12)
  all_goals
    first
    | positivity
    | norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
theorem aggregate_lower :
    (1823261901489827785636347 : ℝ) * (((64 : ℝ) + 0.447897) - ((9 : ℝ) + 0.279))
      ≤ ∑ m ∈ Finset.Icc 155 1000000, ∑ p ∈ shellPrimes highN m,
          Real.log (sigma p m) := by
  have hN0 : (highN : ℝ) ≠ 0 := by norm_num [highN]
  -- rational log endpoint bounds
  have hlogbLo : (59.9555747 : ℝ) ≤ Real.log ((highN : ℝ) / 155) := by
    rw [Real.log_div hN0 (by norm_num)]
    have h1 := high_log_N1_lower
    have h2 : Real.log (155 : ℝ) ≤ 5.0434253 := by
      have h := logNat_upper 155 (by norm_num) (by norm_num)
      rw [show ((155 : ℕ) : ℝ) = (155 : ℝ) by norm_num] at h
      rw [show ((logNatHi 155 : ℚ) : ℝ) = (5.0434253 : ℝ) by norm_num [logNatHi]] at h
      exact h
    linarith
  have hlogaLo : (50.999 : ℝ) ≤ Real.log ((highN : ℝ) / 1000001) := by
    rw [Real.log_div hN0 (by norm_num)]
    have h1 := high_log_N1_lower
    have hlog1e6 : Real.log (1000001 : ℝ) ≤ 14 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      have heq : Real.exp (14 : ℝ) = Real.exp 1 ^ 14 := by rw [← Real.exp_nat_mul]; norm_num
      have hp1 : (2.7182818283 : ℝ) ^ 14 ≤ Real.exp 1 ^ 14 :=
        pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 14
      have hp2 : (1000001 : ℝ) ≤ (2.7182818283 : ℝ) ^ 14 := by norm_num
      rw [heq]; linarith
    linarith
  have hLbup : Real.log ((highN : ℝ) / 155) ≤ (59.9575749 : ℝ) := by
    rw [Real.log_div hN0 (by norm_num)]
    have h1 := high_log_N1_upper
    have h2 : (5.0434251 : ℝ) ≤ Real.log (155 : ℝ) := by
      have h := logNat_lower 155 (by norm_num) (by norm_num)
      rw [show ((155 : ℕ) : ℝ) = (155 : ℝ) by norm_num] at h
      rw [show ((logNatLo 155 : ℚ) : ℝ) = (5.0434251 : ℝ) by norm_num [logNatLo]] at h
      exact h
    linarith
  -- count lower bound
  have hcardf := block_card_lower_dusart 59.9555747 50.999 59.9575749
    (by norm_num) hlogbLo (by norm_num) hlogaLo hLbup (by norm_num)
  have hPmle : (1823261901489827785636347 : ℝ) ≤ (blockPrimes.card : ℝ) := by
    refine le_trans ?_ hcardf
    norm_num [highN]
  have hcardpos : (0 : ℝ) < (blockPrimes.card : ℝ) := by
    have : (0 : ℝ) < (1823261901489827785636347 : ℝ) := by norm_num
    linarith
  have hP : blockPrimes.Nonempty := by
    rw [← Finset.card_pos]; exact_mod_cast hcardpos
  -- hypotheses for block_contribution_pos
  have hprime : ∀ p ∈ blockPrimes, Nat.Prime p := fun p hp => blockPrimes_prime hp
  have hlarge : ∀ p ∈ blockPrimes, 154 < p := by
    intro p hp
    have h := blockPrimes_gt_lo hp
    rw [highN_div_1000001] at h; omega
  have hshell : ∀ p ∈ blockPrimes, (highN : ℝ) / ((1000000 : ℝ) + 1) < (p : ℝ) := by
    intro p hp
    have hlo := blockPrimes_gt_lo hp
    have key : highN < p * 1000001 := (Nat.div_lt_iff_lt_mul (by norm_num)).mp hlo
    rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < (1000000 : ℝ) + 1)]
    have hc : (highN : ℝ) < (p : ℝ) * 1000001 := by exact_mod_cast key
    linarith
  have hbig : (1 : ℝ) < (highN : ℝ) / ((1000000 : ℝ) + 1) := by norm_num [highN]
  have hWlt : (((Finset.Icc 1 154).lcm id : ℕ) : ℝ) * ((harmonicSum 154 : ℚ) : ℝ)
      < ((highN : ℝ) / ((1000000 : ℝ) + 1)) ^ (2 + 1) := by
    have hq : (((Finset.Icc 1 154).lcm id : ℕ) : ℚ) * harmonicSum 154
        < ((highN : ℚ) / ((1000000 : ℚ) + 1)) ^ (2 + 1) := by native_decide
    have h := (Rat.cast_lt (K := ℝ)).mpr hq
    push_cast at h
    exact h
  have hsLS : (9758124781512047322275512320 : ℕ) ≤ S 154 := by
    have hdef : sLowerBGMS 154 = 9758124781512047322275512320 := by native_decide
    have := S_ge_sLowerBGMS 154 (by norm_num)
    rwa [hdef] at this
  -- assemble
  have hcontrib := block_contribution_pos (N := highN) (m₀ := 154) (D := 1000000)
    2 (1823261901489827785636347 : ℝ) ((64 : ℝ) + 0.447897) ((9 : ℝ) + 0.279)
    9758124781512047322275512320 blockPrimes hP hprime hlarge hshell hbig hWlt
    (by norm_num) hPmle (by norm_num) (by norm_num) hsLS aggregate_ell_lower
    aggregate_pen_upper
  have hbiU : ∑ p ∈ blockPrimes, Real.log (sigma p 154)
      = ∑ m ∈ Finset.Icc 155 1000000, ∑ p ∈ shellPrimes highN m, Real.log (sigma p 154) := by
    rw [← biUnion_shell_eq_blockPrimes]
    refine Finset.sum_biUnion ?_
    exact (shellPrimes_pairwiseDisjoint highN 1000000).subset
      (Finset.coe_subset.mpr (by intro x hx; rw [Finset.mem_Icc] at hx ⊢; omega))
  have hsigma : ∑ m ∈ Finset.Icc 155 1000000, ∑ p ∈ shellPrimes highN m, Real.log (sigma p 154)
      ≤ ∑ m ∈ Finset.Icc 155 1000000, ∑ p ∈ shellPrimes highN m, Real.log (sigma p m) := by
    apply Finset.sum_le_sum
    intro m hm
    apply Finset.sum_le_sum
    intro p _
    exact log_sigma_mono_in_m p (by rw [Finset.mem_Icc] at hm; omega)
  calc (1823261901489827785636347 : ℝ) * (((64 : ℝ) + 0.447897) - ((9 : ℝ) + 0.279))
      ≤ ∑ p ∈ blockPrimes, Real.log (sigma p 154) := hcontrib
    _ = ∑ m ∈ Finset.Icc 155 1000000, ∑ p ∈ shellPrimes highN m,
          Real.log (sigma p 154) := hbiU
    _ ≤ ∑ m ∈ Finset.Icc 155 1000000, ∑ p ∈ shellPrimes highN m,
          Real.log (sigma p m) := hsigma

end Erdos320
