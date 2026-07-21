import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.IntervalCases

/-!
# Tight rational two-sided bounds on `Real.log m` for `1 ≤ m ≤ 155`

For every natural `m` with `1 ≤ m ≤ 155` this file provides explicit rational
lower/upper bounds `logNatLo m ≤ Real.log m ≤ logNatHi m` with
`logNatHi m - logNatLo m ≤ 7·10⁻⁷`.  These feed the high-finite-input shell
ledger, where each shell needs `log (N₁/m) = log N₁ - log m` to a few decimals.

## Method (prime factorization)

`log m = ∑ over the prime factorization`, so it suffices to bound `log p` for the
36 primes `p ≤ 155`.  The seeds `p = 2, 3, 5` come directly from Mathlib's
digit constants (`Real.log_two_gt_d9`/`_lt_d9` and the `three`/`five`
analogues).  Every other prime bound is proved by an `exp`-comparison
(`Real.le_log_iff_exp_le` / `Real.log_le_iff_le_exp`), discharging the resulting
`exp`-of-rational bound through the digit-of-`e` constants
(`Real.exp_one_lt_d9`, `Real.exp_one_gt_d9`) and a degree-12 Taylor enclosure
(`Real.exp_bound'`, `Real.sum_le_exp_of_nonneg`), mirroring `PhaseEnclosure.lean`
and `ShellCountDusart.lean`.  The composite bounds are assembled from
`Real.log (a*b) = log a + log b` (`logMul`) along the smallest-prime-factor tree,
so each `m` reuses the bounds of two strictly smaller factors.
-/

namespace Erdos320

open Real

/-! ## Lookup tables of rational bounds -/

/-- Rational lower bound for `Real.log m`, `1 ≤ m ≤ 155` (else `0`). -/
def logNatLo : ℕ → ℚ
  | 1 => 0.0000000
  | 2 => 0.6931471
  | 3 => 1.0986122
  | 4 => 1.3862942
  | 5 => 1.6094379
  | 6 => 1.7917593
  | 7 => 1.9459101
  | 8 => 2.0794413
  | 9 => 2.1972244
  | 10 => 2.3025850
  | 11 => 2.3978952
  | 12 => 2.4849064
  | 13 => 2.5649493
  | 14 => 2.6390572
  | 15 => 2.7080501
  | 16 => 2.7725884
  | 17 => 2.8332133
  | 18 => 2.8903715
  | 19 => 2.9444389
  | 20 => 2.9957321
  | 21 => 3.0445223
  | 22 => 3.0910423
  | 23 => 3.1354942
  | 24 => 3.1780535
  | 25 => 3.2188758
  | 26 => 3.2580964
  | 27 => 3.2958366
  | 28 => 3.3322043
  | 29 => 3.3672958
  | 30 => 3.4011972
  | 31 => 3.4339872
  | 32 => 3.4657355
  | 33 => 3.4965074
  | 34 => 3.5263604
  | 35 => 3.5553480
  | 36 => 3.5835186
  | 37 => 3.6109179
  | 38 => 3.6375860
  | 39 => 3.6635615
  | 40 => 3.6888792
  | 41 => 3.7135720
  | 42 => 3.7376694
  | 43 => 3.7612001
  | 44 => 3.7841894
  | 45 => 3.8066623
  | 46 => 3.8286413
  | 47 => 3.8501476
  | 48 => 3.8712006
  | 49 => 3.8918202
  | 50 => 3.9120229
  | 51 => 3.9318255
  | 52 => 3.9512435
  | 53 => 3.9702919
  | 54 => 3.9889837
  | 55 => 4.0073331
  | 56 => 4.0253514
  | 57 => 4.0430511
  | 58 => 4.0604429
  | 59 => 4.0775374
  | 60 => 4.0943443
  | 61 => 4.1108738
  | 62 => 4.1271343
  | 63 => 4.1431345
  | 64 => 4.1588826
  | 65 => 4.1743872
  | 66 => 4.1896545
  | 67 => 4.2046926
  | 68 => 4.2195075
  | 69 => 4.2341064
  | 70 => 4.2484951
  | 71 => 4.2626798
  | 72 => 4.2766657
  | 73 => 4.2904594
  | 74 => 4.3040650
  | 75 => 4.3174880
  | 76 => 4.3307331
  | 77 => 4.3438053
  | 78 => 4.3567086
  | 79 => 4.3694478
  | 80 => 4.3820263
  | 81 => 4.3944488
  | 82 => 4.4067191
  | 83 => 4.4188406
  | 84 => 4.4308165
  | 85 => 4.4426512
  | 86 => 4.4543472
  | 87 => 4.4659080
  | 88 => 4.4773365
  | 89 => 4.4886363
  | 90 => 4.4998094
  | 91 => 4.5108594
  | 92 => 4.5217884
  | 93 => 4.5325994
  | 94 => 4.5432947
  | 95 => 4.5538768
  | 96 => 4.5643477
  | 97 => 4.5747109
  | 98 => 4.5849673
  | 99 => 4.5951196
  | 100 => 4.6051700
  | 101 => 4.6151205
  | 102 => 4.6249726
  | 103 => 4.6347289
  | 104 => 4.6443906
  | 105 => 4.6539602
  | 106 => 4.6634390
  | 107 => 4.6728288
  | 108 => 4.6821308
  | 109 => 4.6913478
  | 110 => 4.7004802
  | 111 => 4.7095301
  | 112 => 4.7184985
  | 113 => 4.7273878
  | 114 => 4.7361982
  | 115 => 4.7449321
  | 116 => 4.7535900
  | 117 => 4.7621737
  | 118 => 4.7706845
  | 119 => 4.7791234
  | 120 => 4.7874914
  | 121 => 4.7957904
  | 122 => 4.8040209
  | 123 => 4.8121842
  | 124 => 4.8202814
  | 125 => 4.8283137
  | 126 => 4.8362816
  | 127 => 4.8441870
  | 128 => 4.8520297
  | 129 => 4.8598123
  | 130 => 4.8675343
  | 131 => 4.8751973
  | 132 => 4.8828016
  | 133 => 4.8903490
  | 134 => 4.8978397
  | 135 => 4.9052745
  | 136 => 4.9126546
  | 137 => 4.9199809
  | 138 => 4.9272535
  | 139 => 4.9344739
  | 140 => 4.9416422
  | 141 => 4.9487598
  | 142 => 4.9558269
  | 143 => 4.9628445
  | 144 => 4.9698128
  | 145 => 4.9767337
  | 146 => 4.9836065
  | 147 => 4.9904324
  | 148 => 4.9972121
  | 149 => 5.0039463
  | 150 => 5.0106351
  | 151 => 5.0172798
  | 152 => 5.0238802
  | 153 => 5.0304377
  | 154 => 5.0369524
  | 155 => 5.0434251
  | _ => 0

/-- Rational upper bound for `Real.log m`, `1 ≤ m ≤ 155` (else `0`). -/
def logNatHi : ℕ → ℚ
  | 1 => 0.0000000
  | 2 => 0.6931472
  | 3 => 1.0986123
  | 4 => 1.3862944
  | 5 => 1.6094380
  | 6 => 1.7917595
  | 7 => 1.9459102
  | 8 => 2.0794416
  | 9 => 2.1972246
  | 10 => 2.3025852
  | 11 => 2.3978953
  | 12 => 2.4849067
  | 13 => 2.5649494
  | 14 => 2.6390574
  | 15 => 2.7080503
  | 16 => 2.7725888
  | 17 => 2.8332134
  | 18 => 2.8903718
  | 19 => 2.9444390
  | 20 => 2.9957324
  | 21 => 3.0445225
  | 22 => 3.0910425
  | 23 => 3.1354943
  | 24 => 3.1780539
  | 25 => 3.2188760
  | 26 => 3.2580966
  | 27 => 3.2958369
  | 28 => 3.3322046
  | 29 => 3.3672959
  | 30 => 3.4011975
  | 31 => 3.4339873
  | 32 => 3.4657360
  | 33 => 3.4965076
  | 34 => 3.5263606
  | 35 => 3.5553482
  | 36 => 3.5835190
  | 37 => 3.6109180
  | 38 => 3.6375862
  | 39 => 3.6635617
  | 40 => 3.6888796
  | 41 => 3.7135721
  | 42 => 3.7376697
  | 43 => 3.7612002
  | 44 => 3.7841897
  | 45 => 3.8066626
  | 46 => 3.8286415
  | 47 => 3.8501477
  | 48 => 3.8712011
  | 49 => 3.8918204
  | 50 => 3.9120232
  | 51 => 3.9318257
  | 52 => 3.9512438
  | 53 => 3.9702920
  | 54 => 3.9889841
  | 55 => 4.0073333
  | 56 => 4.0253518
  | 57 => 4.0430513
  | 58 => 4.0604431
  | 59 => 4.0775375
  | 60 => 4.0943447
  | 61 => 4.1108739
  | 62 => 4.1271345
  | 63 => 4.1431348
  | 64 => 4.1588832
  | 65 => 4.1743874
  | 66 => 4.1896548
  | 67 => 4.2046927
  | 68 => 4.2195078
  | 69 => 4.2341066
  | 70 => 4.2484954
  | 71 => 4.2626799
  | 72 => 4.2766662
  | 73 => 4.2904595
  | 74 => 4.3040652
  | 75 => 4.3174883
  | 76 => 4.3307334
  | 77 => 4.3438055
  | 78 => 4.3567089
  | 79 => 4.3694479
  | 80 => 4.3820268
  | 81 => 4.3944492
  | 82 => 4.4067193
  | 83 => 4.4188407
  | 84 => 4.4308169
  | 85 => 4.4426514
  | 86 => 4.4543474
  | 87 => 4.4659082
  | 88 => 4.4773369
  | 89 => 4.4886364
  | 90 => 4.4998098
  | 91 => 4.5108596
  | 92 => 4.5217887
  | 93 => 4.5325996
  | 94 => 4.5432949
  | 95 => 4.5538770
  | 96 => 4.5643483
  | 97 => 4.5747110
  | 98 => 4.5849676
  | 99 => 4.5951199
  | 100 => 4.6051704
  | 101 => 4.6151206
  | 102 => 4.6249729
  | 103 => 4.6347290
  | 104 => 4.6443910
  | 105 => 4.6539605
  | 106 => 4.6634392
  | 107 => 4.6728289
  | 108 => 4.6821313
  | 109 => 4.6913479
  | 110 => 4.7004805
  | 111 => 4.7095303
  | 112 => 4.7184990
  | 113 => 4.7273879
  | 114 => 4.7361985
  | 115 => 4.7449323
  | 116 => 4.7535903
  | 117 => 4.7621740
  | 118 => 4.7706847
  | 119 => 4.7791236
  | 120 => 4.7874919
  | 121 => 4.7957906
  | 122 => 4.8040211
  | 123 => 4.8121844
  | 124 => 4.8202817
  | 125 => 4.8283140
  | 126 => 4.8362820
  | 127 => 4.8441871
  | 128 => 4.8520304
  | 129 => 4.8598125
  | 130 => 4.8675346
  | 131 => 4.8751974
  | 132 => 4.8828020
  | 133 => 4.8903492
  | 134 => 4.8978399
  | 135 => 4.9052749
  | 136 => 4.9126550
  | 137 => 4.9199810
  | 138 => 4.9272538
  | 139 => 4.9344740
  | 140 => 4.9416426
  | 141 => 4.9487600
  | 142 => 4.9558271
  | 143 => 4.9628447
  | 144 => 4.9698134
  | 145 => 4.9767339
  | 146 => 4.9836067
  | 147 => 4.9904327
  | 148 => 4.9972124
  | 149 => 5.0039464
  | 150 => 5.0106355
  | 151 => 5.0172799
  | 152 => 5.0238806
  | 153 => 5.0304380
  | 154 => 5.0369527
  | 155 => 5.0434253
  | _ => 0

/-! ## `exp`-comparison toolkit -/

private lemma expNatSplit (k : ℕ) : Real.exp (k : ℝ) = Real.exp 1 ^ k := by
  rw [show (k : ℝ) = (k : ℝ) * 1 by ring, Real.exp_nat_mul]

private lemma expq_lower (k : ℕ) (f TL q : ℝ) (hq : q = (k : ℝ) + f)
    (hTL0 : 0 ≤ TL) (hTL : TL ≤ Real.exp f) :
    (2.7182818283 : ℝ) ^ k * TL ≤ Real.exp q := by
  have h1 : Real.exp q = Real.exp 1 ^ k * Real.exp f := by
    rw [hq, Real.exp_add, expNatSplit]
  have he : (2.7182818283 : ℝ) ^ k ≤ Real.exp 1 ^ k :=
    pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le k
  rw [h1]; exact mul_le_mul he hTL hTL0 (by positivity)

private lemma expq_upper (k : ℕ) (f TU q : ℝ) (hq : q = (k : ℝ) + f)
    (hTU : Real.exp f ≤ TU) :
    Real.exp q ≤ (2.7182818286 : ℝ) ^ k * TU := by
  have h1 : Real.exp q = Real.exp 1 ^ k * Real.exp f := by
    rw [hq, Real.exp_add, expNatSplit]
  have he : Real.exp 1 ^ k ≤ (2.7182818286 : ℝ) ^ k :=
    pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le k
  rw [h1]; exact mul_le_mul he hTU (Real.exp_pos f).le (by positivity)

private lemma le_log_of (p : ℕ) (hp : 0 < p) (q : ℝ) (k : ℕ) (f TU : ℝ)
    (hq : q = (k : ℝ) + f) (hTU : Real.exp f ≤ TU)
    (hle : (2.7182818286 : ℝ) ^ k * TU ≤ (p : ℝ)) : q ≤ Real.log (p : ℝ) := by
  rw [Real.le_log_iff_exp_le (by exact_mod_cast hp)]
  exact (expq_upper k f TU q hq hTU).trans hle

private lemma log_le_of (p : ℕ) (hp : 0 < p) (q : ℝ) (k : ℕ) (f TL : ℝ)
    (hq : q = (k : ℝ) + f) (hTL0 : 0 ≤ TL) (hTL : TL ≤ Real.exp f)
    (hle : (p : ℝ) ≤ (2.7182818283 : ℝ) ^ k * TL) : Real.log (p : ℝ) ≤ q := by
  rw [Real.log_le_iff_le_exp (by exact_mod_cast hp)]
  exact hle.trans (expq_lower k f TL q hq hTL0 hTL)

private lemma logMul {a b : ℕ} (ha : (0 : ℝ) < (a : ℝ)) (hb : (0 : ℝ) < (b : ℝ))
    {la ua lb ub : ℝ}
    (Ha : la ≤ Real.log ↑a ∧ Real.log ↑a ≤ ua)
    (Hb : lb ≤ Real.log ↑b ∧ Real.log ↑b ≤ ub) :
    la + lb ≤ Real.log ↑(a * b) ∧ Real.log ↑(a * b) ≤ ua + ub := by
  have hcast : (↑(a * b) : ℝ) = (↑a : ℝ) * ↑b := by push_cast; ring
  rw [hcast, Real.log_mul ha.ne' hb.ne']
  exact ⟨by linarith [Ha.1, Hb.1], by linarith [Ha.2, Hb.2]⟩

/-! ## Per-value bounds `M_n : logNatLo n ≤ Real.log n ≤ logNatHi n` -/

theorem M_1 : (↑(logNatLo 1) : ℝ) ≤ Real.log ↑(1 : ℕ) ∧ Real.log ↑(1 : ℕ) ≤ ↑(logNatHi 1) := by
  rw [show (↑(logNatLo 1) : ℝ) = 0 from by norm_num [logNatLo],
      show (↑(logNatHi 1) : ℝ) = 0 from by norm_num [logNatHi]]
  simp

theorem M_2 : (↑(logNatLo 2) : ℝ) ≤ Real.log ↑(2 : ℕ) ∧ Real.log ↑(2 : ℕ) ≤ ↑(logNatHi 2) := by
  rw [show ((2 : ℕ) : ℝ) = 2 from by norm_num,
      show (↑(logNatLo 2) : ℝ) = (0.6931471 : ℝ) from by norm_num [logNatLo],
      show (↑(logNatHi 2) : ℝ) = (0.6931472 : ℝ) from by norm_num [logNatHi]]
  constructor
  · linarith [Real.log_two_gt_d9]
  · linarith [Real.log_two_lt_d9]

theorem M_3 : (↑(logNatLo 3) : ℝ) ≤ Real.log ↑(3 : ℕ) ∧ Real.log ↑(3 : ℕ) ≤ ↑(logNatHi 3) := by
  rw [show ((3 : ℕ) : ℝ) = 3 from by norm_num,
      show (↑(logNatLo 3) : ℝ) = (1.0986122 : ℝ) from by norm_num [logNatLo],
      show (↑(logNatHi 3) : ℝ) = (1.0986123 : ℝ) from by norm_num [logNatHi]]
  constructor
  · linarith [Real.log_three_gt_d9]
  · linarith [Real.log_three_lt_d9]

theorem M_4 : (↑(logNatLo 4) : ℝ) ≤ Real.log ↑(4 : ℕ) ∧ Real.log ↑(4 : ℕ) ≤ ↑(logNatHi 4) := by
  have h := logMul (a := 2) (b := 2) (by norm_num) (by norm_num) M_2 M_2
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 4) : ℝ) = ↑(logNatLo 2) + ↑(logNatLo 2) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 4) : ℝ) = ↑(logNatHi 2) + ↑(logNatHi 2) from by norm_num [logNatHi]]
    exact h.2

theorem M_5 : (↑(logNatLo 5) : ℝ) ≤ Real.log ↑(5 : ℕ) ∧ Real.log ↑(5 : ℕ) ≤ ↑(logNatHi 5) := by
  rw [show ((5 : ℕ) : ℝ) = 5 from by norm_num,
      show (↑(logNatLo 5) : ℝ) = (1.6094379 : ℝ) from by norm_num [logNatLo],
      show (↑(logNatHi 5) : ℝ) = (1.6094380 : ℝ) from by norm_num [logNatHi]]
  constructor
  · linarith [Real.log_five_gt_d9]
  · linarith [Real.log_five_lt_d9]

theorem M_6 : (↑(logNatLo 6) : ℝ) ≤ Real.log ↑(6 : ℕ) ∧ Real.log ↑(6 : ℕ) ≤ ↑(logNatHi 6) := by
  have h := logMul (a := 2) (b := 3) (by norm_num) (by norm_num) M_2 M_3
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 6) : ℝ) = ↑(logNatLo 2) + ↑(logNatLo 3) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 6) : ℝ) = ↑(logNatHi 2) + ↑(logNatHi 3) from by norm_num [logNatHi]]
    exact h.2

set_option maxHeartbeats 1000000 in
theorem M_7 : (↑(logNatLo 7) : ℝ) ≤ Real.log ↑(7 : ℕ) ∧ Real.log ↑(7 : ℕ) ≤ ↑(logNatHi 7) := by
  have hlo : (1.9459101 : ℝ) ≤ Real.log ↑(7 : ℕ) := by
    have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.9459101 : ℝ) by norm_num)
      (show (0.9459101 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact le_log_of 7 (by norm_num) (1.9459101) 1 (0.9459101) _ (by norm_num) hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  have hhi : Real.log ↑(7 : ℕ) ≤ (1.9459102 : ℝ) := by
    have hTL := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.9459102 : ℝ) by norm_num) 12
    exact log_le_of 7 (by norm_num) (1.9459102) 1 (0.9459102) _ (by norm_num) (by positivity) hTL
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 7) : ℝ) = (1.9459101 : ℝ) from by norm_num [logNatLo]]; exact hlo
  · rw [show (↑(logNatHi 7) : ℝ) = (1.9459102 : ℝ) from by norm_num [logNatHi]]; exact hhi

theorem M_8 : (↑(logNatLo 8) : ℝ) ≤ Real.log ↑(8 : ℕ) ∧ Real.log ↑(8 : ℕ) ≤ ↑(logNatHi 8) := by
  have h := logMul (a := 2) (b := 4) (by norm_num) (by norm_num) M_2 M_4
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 8) : ℝ) = ↑(logNatLo 2) + ↑(logNatLo 4) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 8) : ℝ) = ↑(logNatHi 2) + ↑(logNatHi 4) from by norm_num [logNatHi]]
    exact h.2

theorem M_9 : (↑(logNatLo 9) : ℝ) ≤ Real.log ↑(9 : ℕ) ∧ Real.log ↑(9 : ℕ) ≤ ↑(logNatHi 9) := by
  have h := logMul (a := 3) (b := 3) (by norm_num) (by norm_num) M_3 M_3
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 9) : ℝ) = ↑(logNatLo 3) + ↑(logNatLo 3) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 9) : ℝ) = ↑(logNatHi 3) + ↑(logNatHi 3) from by norm_num [logNatHi]]
    exact h.2

theorem M_10 : (↑(logNatLo 10) : ℝ) ≤ Real.log ↑(10 : ℕ) ∧ Real.log ↑(10 : ℕ) ≤ ↑(logNatHi 10) := by
  have h := logMul (a := 2) (b := 5) (by norm_num) (by norm_num) M_2 M_5
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 10) : ℝ) = ↑(logNatLo 2) + ↑(logNatLo 5) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 10) : ℝ) = ↑(logNatHi 2) + ↑(logNatHi 5) from by norm_num [logNatHi]]
    exact h.2

set_option maxHeartbeats 1000000 in
theorem M_11 : (↑(logNatLo 11) : ℝ) ≤ Real.log ↑(11 : ℕ) ∧ Real.log ↑(11 : ℕ) ≤ ↑(logNatHi 11) := by
  have hlo : (2.3978952 : ℝ) ≤ Real.log ↑(11 : ℕ) := by
    have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.3978952 : ℝ) by norm_num)
      (show (0.3978952 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact le_log_of 11 (by norm_num) (2.3978952) 2 (0.3978952) _ (by norm_num) hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  have hhi : Real.log ↑(11 : ℕ) ≤ (2.3978953 : ℝ) := by
    have hTL := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.3978953 : ℝ) by norm_num) 12
    exact log_le_of 11 (by norm_num) (2.3978953) 2 (0.3978953) _ (by norm_num) (by positivity) hTL
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 11) : ℝ) = (2.3978952 : ℝ) from by norm_num [logNatLo]]; exact hlo
  · rw [show (↑(logNatHi 11) : ℝ) = (2.3978953 : ℝ) from by norm_num [logNatHi]]; exact hhi

theorem M_12 : (↑(logNatLo 12) : ℝ) ≤ Real.log ↑(12 : ℕ) ∧ Real.log ↑(12 : ℕ) ≤ ↑(logNatHi 12) := by
  have h := logMul (a := 2) (b := 6) (by norm_num) (by norm_num) M_2 M_6
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 12) : ℝ) = ↑(logNatLo 2) + ↑(logNatLo 6) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 12) : ℝ) = ↑(logNatHi 2) + ↑(logNatHi 6) from by norm_num [logNatHi]]
    exact h.2

set_option maxHeartbeats 1000000 in
theorem M_13 : (↑(logNatLo 13) : ℝ) ≤ Real.log ↑(13 : ℕ) ∧ Real.log ↑(13 : ℕ) ≤ ↑(logNatHi 13) := by
  have hlo : (2.5649493 : ℝ) ≤ Real.log ↑(13 : ℕ) := by
    have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.5649493 : ℝ) by norm_num)
      (show (0.5649493 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact le_log_of 13 (by norm_num) (2.5649493) 2 (0.5649493) _ (by norm_num) hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  have hhi : Real.log ↑(13 : ℕ) ≤ (2.5649494 : ℝ) := by
    have hTL := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.5649494 : ℝ) by norm_num) 12
    exact log_le_of 13 (by norm_num) (2.5649494) 2 (0.5649494) _ (by norm_num) (by positivity) hTL
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 13) : ℝ) = (2.5649493 : ℝ) from by norm_num [logNatLo]]; exact hlo
  · rw [show (↑(logNatHi 13) : ℝ) = (2.5649494 : ℝ) from by norm_num [logNatHi]]; exact hhi

theorem M_14 : (↑(logNatLo 14) : ℝ) ≤ Real.log ↑(14 : ℕ) ∧ Real.log ↑(14 : ℕ) ≤ ↑(logNatHi 14) := by
  have h := logMul (a := 2) (b := 7) (by norm_num) (by norm_num) M_2 M_7
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 14) : ℝ) = ↑(logNatLo 2) + ↑(logNatLo 7) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 14) : ℝ) = ↑(logNatHi 2) + ↑(logNatHi 7) from by norm_num [logNatHi]]
    exact h.2

theorem M_15 : (↑(logNatLo 15) : ℝ) ≤ Real.log ↑(15 : ℕ) ∧ Real.log ↑(15 : ℕ) ≤ ↑(logNatHi 15) := by
  have h := logMul (a := 3) (b := 5) (by norm_num) (by norm_num) M_3 M_5
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 15) : ℝ) = ↑(logNatLo 3) + ↑(logNatLo 5) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 15) : ℝ) = ↑(logNatHi 3) + ↑(logNatHi 5) from by norm_num [logNatHi]]
    exact h.2

theorem M_16 : (↑(logNatLo 16) : ℝ) ≤ Real.log ↑(16 : ℕ) ∧ Real.log ↑(16 : ℕ) ≤ ↑(logNatHi 16) := by
  have h := logMul (a := 2) (b := 8) (by norm_num) (by norm_num) M_2 M_8
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 16) : ℝ) = ↑(logNatLo 2) + ↑(logNatLo 8) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 16) : ℝ) = ↑(logNatHi 2) + ↑(logNatHi 8) from by norm_num [logNatHi]]
    exact h.2

set_option maxHeartbeats 1000000 in
theorem M_17 : (↑(logNatLo 17) : ℝ) ≤ Real.log ↑(17 : ℕ) ∧ Real.log ↑(17 : ℕ) ≤ ↑(logNatHi 17) := by
  have hlo : (2.8332133 : ℝ) ≤ Real.log ↑(17 : ℕ) := by
    have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.8332133 : ℝ) by norm_num)
      (show (0.8332133 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact le_log_of 17 (by norm_num) (2.8332133) 2 (0.8332133) _ (by norm_num) hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  have hhi : Real.log ↑(17 : ℕ) ≤ (2.8332134 : ℝ) := by
    have hTL := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.8332134 : ℝ) by norm_num) 12
    exact log_le_of 17 (by norm_num) (2.8332134) 2 (0.8332134) _ (by norm_num) (by positivity) hTL
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 17) : ℝ) = (2.8332133 : ℝ) from by norm_num [logNatLo]]; exact hlo
  · rw [show (↑(logNatHi 17) : ℝ) = (2.8332134 : ℝ) from by norm_num [logNatHi]]; exact hhi

theorem M_18 : (↑(logNatLo 18) : ℝ) ≤ Real.log ↑(18 : ℕ) ∧ Real.log ↑(18 : ℕ) ≤ ↑(logNatHi 18) := by
  have h := logMul (a := 2) (b := 9) (by norm_num) (by norm_num) M_2 M_9
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 18) : ℝ) = ↑(logNatLo 2) + ↑(logNatLo 9) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 18) : ℝ) = ↑(logNatHi 2) + ↑(logNatHi 9) from by norm_num [logNatHi]]
    exact h.2

set_option maxHeartbeats 1000000 in
theorem M_19 : (↑(logNatLo 19) : ℝ) ≤ Real.log ↑(19 : ℕ) ∧ Real.log ↑(19 : ℕ) ≤ ↑(logNatHi 19) := by
  have hlo : (2.9444389 : ℝ) ≤ Real.log ↑(19 : ℕ) := by
    have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.9444389 : ℝ) by norm_num)
      (show (0.9444389 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact le_log_of 19 (by norm_num) (2.9444389) 2 (0.9444389) _ (by norm_num) hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  have hhi : Real.log ↑(19 : ℕ) ≤ (2.9444390 : ℝ) := by
    have hTL := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.9444390 : ℝ) by norm_num) 12
    exact log_le_of 19 (by norm_num) (2.9444390) 2 (0.9444390) _ (by norm_num) (by positivity) hTL
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 19) : ℝ) = (2.9444389 : ℝ) from by norm_num [logNatLo]]; exact hlo
  · rw [show (↑(logNatHi 19) : ℝ) = (2.9444390 : ℝ) from by norm_num [logNatHi]]; exact hhi

theorem M_20 : (↑(logNatLo 20) : ℝ) ≤ Real.log ↑(20 : ℕ) ∧ Real.log ↑(20 : ℕ) ≤ ↑(logNatHi 20) := by
  have h := logMul (a := 2) (b := 10) (by norm_num) (by norm_num) M_2 M_10
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 20) : ℝ) = ↑(logNatLo 2) + ↑(logNatLo 10) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 20) : ℝ) = ↑(logNatHi 2) + ↑(logNatHi 10) from by norm_num [logNatHi]]
    exact h.2

theorem M_21 : (↑(logNatLo 21) : ℝ) ≤ Real.log ↑(21 : ℕ) ∧ Real.log ↑(21 : ℕ) ≤ ↑(logNatHi 21) := by
  have h := logMul (a := 3) (b := 7) (by norm_num) (by norm_num) M_3 M_7
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 21) : ℝ) = ↑(logNatLo 3) + ↑(logNatLo 7) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 21) : ℝ) = ↑(logNatHi 3) + ↑(logNatHi 7) from by norm_num [logNatHi]]
    exact h.2

theorem M_22 : (↑(logNatLo 22) : ℝ) ≤ Real.log ↑(22 : ℕ) ∧ Real.log ↑(22 : ℕ) ≤ ↑(logNatHi 22) := by
  have h := logMul (a := 2) (b := 11) (by norm_num) (by norm_num) M_2 M_11
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 22) : ℝ) = ↑(logNatLo 2) + ↑(logNatLo 11) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 22) : ℝ) = ↑(logNatHi 2) + ↑(logNatHi 11) from by norm_num [logNatHi]]
    exact h.2

set_option maxHeartbeats 1000000 in
theorem M_23 : (↑(logNatLo 23) : ℝ) ≤ Real.log ↑(23 : ℕ) ∧ Real.log ↑(23 : ℕ) ≤ ↑(logNatHi 23) := by
  have hlo : (3.1354942 : ℝ) ≤ Real.log ↑(23 : ℕ) := by
    have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.1354942 : ℝ) by norm_num)
      (show (0.1354942 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact le_log_of 23 (by norm_num) (3.1354942) 3 (0.1354942) _ (by norm_num) hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  have hhi : Real.log ↑(23 : ℕ) ≤ (3.1354943 : ℝ) := by
    have hTL := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.1354943 : ℝ) by norm_num) 12
    exact log_le_of 23 (by norm_num) (3.1354943) 3 (0.1354943) _ (by norm_num) (by positivity) hTL
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 23) : ℝ) = (3.1354942 : ℝ) from by norm_num [logNatLo]]; exact hlo
  · rw [show (↑(logNatHi 23) : ℝ) = (3.1354943 : ℝ) from by norm_num [logNatHi]]; exact hhi

theorem M_24 : (↑(logNatLo 24) : ℝ) ≤ Real.log ↑(24 : ℕ) ∧ Real.log ↑(24 : ℕ) ≤ ↑(logNatHi 24) := by
  have h := logMul (a := 2) (b := 12) (by norm_num) (by norm_num) M_2 M_12
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 24) : ℝ) = ↑(logNatLo 2) + ↑(logNatLo 12) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 24) : ℝ) = ↑(logNatHi 2) + ↑(logNatHi 12) from by norm_num [logNatHi]]
    exact h.2

theorem M_25 : (↑(logNatLo 25) : ℝ) ≤ Real.log ↑(25 : ℕ) ∧ Real.log ↑(25 : ℕ) ≤ ↑(logNatHi 25) := by
  have h := logMul (a := 5) (b := 5) (by norm_num) (by norm_num) M_5 M_5
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 25) : ℝ) = ↑(logNatLo 5) + ↑(logNatLo 5) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 25) : ℝ) = ↑(logNatHi 5) + ↑(logNatHi 5) from by norm_num [logNatHi]]
    exact h.2

theorem M_26 : (↑(logNatLo 26) : ℝ) ≤ Real.log ↑(26 : ℕ) ∧ Real.log ↑(26 : ℕ) ≤ ↑(logNatHi 26) := by
  have h := logMul (a := 2) (b := 13) (by norm_num) (by norm_num) M_2 M_13
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 26) : ℝ) = ↑(logNatLo 2) + ↑(logNatLo 13) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 26) : ℝ) = ↑(logNatHi 2) + ↑(logNatHi 13) from by norm_num [logNatHi]]
    exact h.2

theorem M_27 : (↑(logNatLo 27) : ℝ) ≤ Real.log ↑(27 : ℕ) ∧ Real.log ↑(27 : ℕ) ≤ ↑(logNatHi 27) := by
  have h := logMul (a := 3) (b := 9) (by norm_num) (by norm_num) M_3 M_9
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 27) : ℝ) = ↑(logNatLo 3) + ↑(logNatLo 9) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 27) : ℝ) = ↑(logNatHi 3) + ↑(logNatHi 9) from by norm_num [logNatHi]]
    exact h.2

theorem M_28 : (↑(logNatLo 28) : ℝ) ≤ Real.log ↑(28 : ℕ) ∧ Real.log ↑(28 : ℕ) ≤ ↑(logNatHi 28) := by
  have h := logMul (a := 2) (b := 14) (by norm_num) (by norm_num) M_2 M_14
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 28) : ℝ) = ↑(logNatLo 2) + ↑(logNatLo 14) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 28) : ℝ) = ↑(logNatHi 2) + ↑(logNatHi 14) from by norm_num [logNatHi]]
    exact h.2

set_option maxHeartbeats 1000000 in
theorem M_29 : (↑(logNatLo 29) : ℝ) ≤ Real.log ↑(29 : ℕ) ∧ Real.log ↑(29 : ℕ) ≤ ↑(logNatHi 29) := by
  have hlo : (3.3672958 : ℝ) ≤ Real.log ↑(29 : ℕ) := by
    have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.3672958 : ℝ) by norm_num)
      (show (0.3672958 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact le_log_of 29 (by norm_num) (3.3672958) 3 (0.3672958) _ (by norm_num) hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  have hhi : Real.log ↑(29 : ℕ) ≤ (3.3672959 : ℝ) := by
    have hTL := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.3672959 : ℝ) by norm_num) 12
    exact log_le_of 29 (by norm_num) (3.3672959) 3 (0.3672959) _ (by norm_num) (by positivity) hTL
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 29) : ℝ) = (3.3672958 : ℝ) from by norm_num [logNatLo]]; exact hlo
  · rw [show (↑(logNatHi 29) : ℝ) = (3.3672959 : ℝ) from by norm_num [logNatHi]]; exact hhi

theorem M_30 : (↑(logNatLo 30) : ℝ) ≤ Real.log ↑(30 : ℕ) ∧ Real.log ↑(30 : ℕ) ≤ ↑(logNatHi 30) := by
  have h := logMul (a := 2) (b := 15) (by norm_num) (by norm_num) M_2 M_15
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 30) : ℝ) = ↑(logNatLo 2) + ↑(logNatLo 15) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 30) : ℝ) = ↑(logNatHi 2) + ↑(logNatHi 15) from by norm_num [logNatHi]]
    exact h.2

set_option maxHeartbeats 1000000 in
theorem M_31 : (↑(logNatLo 31) : ℝ) ≤ Real.log ↑(31 : ℕ) ∧ Real.log ↑(31 : ℕ) ≤ ↑(logNatHi 31) := by
  have hlo : (3.4339872 : ℝ) ≤ Real.log ↑(31 : ℕ) := by
    have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.4339872 : ℝ) by norm_num)
      (show (0.4339872 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact le_log_of 31 (by norm_num) (3.4339872) 3 (0.4339872) _ (by norm_num) hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  have hhi : Real.log ↑(31 : ℕ) ≤ (3.4339873 : ℝ) := by
    have hTL := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.4339873 : ℝ) by norm_num) 12
    exact log_le_of 31 (by norm_num) (3.4339873) 3 (0.4339873) _ (by norm_num) (by positivity) hTL
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 31) : ℝ) = (3.4339872 : ℝ) from by norm_num [logNatLo]]; exact hlo
  · rw [show (↑(logNatHi 31) : ℝ) = (3.4339873 : ℝ) from by norm_num [logNatHi]]; exact hhi

theorem M_32 : (↑(logNatLo 32) : ℝ) ≤ Real.log ↑(32 : ℕ) ∧ Real.log ↑(32 : ℕ) ≤ ↑(logNatHi 32) := by
  have h := logMul (a := 2) (b := 16) (by norm_num) (by norm_num) M_2 M_16
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 32) : ℝ) = ↑(logNatLo 2) + ↑(logNatLo 16) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 32) : ℝ) = ↑(logNatHi 2) + ↑(logNatHi 16) from by norm_num [logNatHi]]
    exact h.2

theorem M_33 : (↑(logNatLo 33) : ℝ) ≤ Real.log ↑(33 : ℕ) ∧ Real.log ↑(33 : ℕ) ≤ ↑(logNatHi 33) := by
  have h := logMul (a := 3) (b := 11) (by norm_num) (by norm_num) M_3 M_11
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 33) : ℝ) = ↑(logNatLo 3) + ↑(logNatLo 11) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 33) : ℝ) = ↑(logNatHi 3) + ↑(logNatHi 11) from by norm_num [logNatHi]]
    exact h.2

theorem M_34 : (↑(logNatLo 34) : ℝ) ≤ Real.log ↑(34 : ℕ) ∧ Real.log ↑(34 : ℕ) ≤ ↑(logNatHi 34) := by
  have h := logMul (a := 2) (b := 17) (by norm_num) (by norm_num) M_2 M_17
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 34) : ℝ) = ↑(logNatLo 2) + ↑(logNatLo 17) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 34) : ℝ) = ↑(logNatHi 2) + ↑(logNatHi 17) from by norm_num [logNatHi]]
    exact h.2

theorem M_35 : (↑(logNatLo 35) : ℝ) ≤ Real.log ↑(35 : ℕ) ∧ Real.log ↑(35 : ℕ) ≤ ↑(logNatHi 35) := by
  have h := logMul (a := 5) (b := 7) (by norm_num) (by norm_num) M_5 M_7
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 35) : ℝ) = ↑(logNatLo 5) + ↑(logNatLo 7) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 35) : ℝ) = ↑(logNatHi 5) + ↑(logNatHi 7) from by norm_num [logNatHi]]
    exact h.2

theorem M_36 : (↑(logNatLo 36) : ℝ) ≤ Real.log ↑(36 : ℕ) ∧ Real.log ↑(36 : ℕ) ≤ ↑(logNatHi 36) := by
  have h := logMul (a := 2) (b := 18) (by norm_num) (by norm_num) M_2 M_18
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 36) : ℝ) = ↑(logNatLo 2) + ↑(logNatLo 18) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 36) : ℝ) = ↑(logNatHi 2) + ↑(logNatHi 18) from by norm_num [logNatHi]]
    exact h.2

set_option maxHeartbeats 1000000 in
theorem M_37 : (↑(logNatLo 37) : ℝ) ≤ Real.log ↑(37 : ℕ) ∧ Real.log ↑(37 : ℕ) ≤ ↑(logNatHi 37) := by
  have hlo : (3.6109179 : ℝ) ≤ Real.log ↑(37 : ℕ) := by
    have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.6109179 : ℝ) by norm_num)
      (show (0.6109179 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact le_log_of 37 (by norm_num) (3.6109179) 3 (0.6109179) _ (by norm_num) hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  have hhi : Real.log ↑(37 : ℕ) ≤ (3.6109180 : ℝ) := by
    have hTL := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.6109180 : ℝ) by norm_num) 12
    exact log_le_of 37 (by norm_num) (3.6109180) 3 (0.6109180) _ (by norm_num) (by positivity) hTL
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 37) : ℝ) = (3.6109179 : ℝ) from by norm_num [logNatLo]]; exact hlo
  · rw [show (↑(logNatHi 37) : ℝ) = (3.6109180 : ℝ) from by norm_num [logNatHi]]; exact hhi

theorem M_38 : (↑(logNatLo 38) : ℝ) ≤ Real.log ↑(38 : ℕ) ∧ Real.log ↑(38 : ℕ) ≤ ↑(logNatHi 38) := by
  have h := logMul (a := 2) (b := 19) (by norm_num) (by norm_num) M_2 M_19
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 38) : ℝ) = ↑(logNatLo 2) + ↑(logNatLo 19) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 38) : ℝ) = ↑(logNatHi 2) + ↑(logNatHi 19) from by norm_num [logNatHi]]
    exact h.2

theorem M_39 : (↑(logNatLo 39) : ℝ) ≤ Real.log ↑(39 : ℕ) ∧ Real.log ↑(39 : ℕ) ≤ ↑(logNatHi 39) := by
  have h := logMul (a := 3) (b := 13) (by norm_num) (by norm_num) M_3 M_13
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 39) : ℝ) = ↑(logNatLo 3) + ↑(logNatLo 13) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 39) : ℝ) = ↑(logNatHi 3) + ↑(logNatHi 13) from by norm_num [logNatHi]]
    exact h.2

theorem M_40 : (↑(logNatLo 40) : ℝ) ≤ Real.log ↑(40 : ℕ) ∧ Real.log ↑(40 : ℕ) ≤ ↑(logNatHi 40) := by
  have h := logMul (a := 2) (b := 20) (by norm_num) (by norm_num) M_2 M_20
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 40) : ℝ) = ↑(logNatLo 2) + ↑(logNatLo 20) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 40) : ℝ) = ↑(logNatHi 2) + ↑(logNatHi 20) from by norm_num [logNatHi]]
    exact h.2

set_option maxHeartbeats 1000000 in
theorem M_41 : (↑(logNatLo 41) : ℝ) ≤ Real.log ↑(41 : ℕ) ∧ Real.log ↑(41 : ℕ) ≤ ↑(logNatHi 41) := by
  have hlo : (3.7135720 : ℝ) ≤ Real.log ↑(41 : ℕ) := by
    have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.7135720 : ℝ) by norm_num)
      (show (0.7135720 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact le_log_of 41 (by norm_num) (3.7135720) 3 (0.7135720) _ (by norm_num) hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  have hhi : Real.log ↑(41 : ℕ) ≤ (3.7135721 : ℝ) := by
    have hTL := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.7135721 : ℝ) by norm_num) 12
    exact log_le_of 41 (by norm_num) (3.7135721) 3 (0.7135721) _ (by norm_num) (by positivity) hTL
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 41) : ℝ) = (3.7135720 : ℝ) from by norm_num [logNatLo]]; exact hlo
  · rw [show (↑(logNatHi 41) : ℝ) = (3.7135721 : ℝ) from by norm_num [logNatHi]]; exact hhi

theorem M_42 : (↑(logNatLo 42) : ℝ) ≤ Real.log ↑(42 : ℕ) ∧ Real.log ↑(42 : ℕ) ≤ ↑(logNatHi 42) := by
  have h := logMul (a := 2) (b := 21) (by norm_num) (by norm_num) M_2 M_21
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 42) : ℝ) = ↑(logNatLo 2) + ↑(logNatLo 21) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 42) : ℝ) = ↑(logNatHi 2) + ↑(logNatHi 21) from by norm_num [logNatHi]]
    exact h.2

set_option maxHeartbeats 1000000 in
theorem M_43 : (↑(logNatLo 43) : ℝ) ≤ Real.log ↑(43 : ℕ) ∧ Real.log ↑(43 : ℕ) ≤ ↑(logNatHi 43) := by
  have hlo : (3.7612001 : ℝ) ≤ Real.log ↑(43 : ℕ) := by
    have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.7612001 : ℝ) by norm_num)
      (show (0.7612001 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact le_log_of 43 (by norm_num) (3.7612001) 3 (0.7612001) _ (by norm_num) hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  have hhi : Real.log ↑(43 : ℕ) ≤ (3.7612002 : ℝ) := by
    have hTL := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.7612002 : ℝ) by norm_num) 12
    exact log_le_of 43 (by norm_num) (3.7612002) 3 (0.7612002) _ (by norm_num) (by positivity) hTL
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 43) : ℝ) = (3.7612001 : ℝ) from by norm_num [logNatLo]]; exact hlo
  · rw [show (↑(logNatHi 43) : ℝ) = (3.7612002 : ℝ) from by norm_num [logNatHi]]; exact hhi

theorem M_44 : (↑(logNatLo 44) : ℝ) ≤ Real.log ↑(44 : ℕ) ∧ Real.log ↑(44 : ℕ) ≤ ↑(logNatHi 44) := by
  have h := logMul (a := 2) (b := 22) (by norm_num) (by norm_num) M_2 M_22
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 44) : ℝ) = ↑(logNatLo 2) + ↑(logNatLo 22) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 44) : ℝ) = ↑(logNatHi 2) + ↑(logNatHi 22) from by norm_num [logNatHi]]
    exact h.2

theorem M_45 : (↑(logNatLo 45) : ℝ) ≤ Real.log ↑(45 : ℕ) ∧ Real.log ↑(45 : ℕ) ≤ ↑(logNatHi 45) := by
  have h := logMul (a := 3) (b := 15) (by norm_num) (by norm_num) M_3 M_15
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 45) : ℝ) = ↑(logNatLo 3) + ↑(logNatLo 15) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 45) : ℝ) = ↑(logNatHi 3) + ↑(logNatHi 15) from by norm_num [logNatHi]]
    exact h.2

theorem M_46 : (↑(logNatLo 46) : ℝ) ≤ Real.log ↑(46 : ℕ) ∧ Real.log ↑(46 : ℕ) ≤ ↑(logNatHi 46) := by
  have h := logMul (a := 2) (b := 23) (by norm_num) (by norm_num) M_2 M_23
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 46) : ℝ) = ↑(logNatLo 2) + ↑(logNatLo 23) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 46) : ℝ) = ↑(logNatHi 2) + ↑(logNatHi 23) from by norm_num [logNatHi]]
    exact h.2

set_option maxHeartbeats 1000000 in
theorem M_47 : (↑(logNatLo 47) : ℝ) ≤ Real.log ↑(47 : ℕ) ∧ Real.log ↑(47 : ℕ) ≤ ↑(logNatHi 47) := by
  have hlo : (3.8501476 : ℝ) ≤ Real.log ↑(47 : ℕ) := by
    have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.8501476 : ℝ) by norm_num)
      (show (0.8501476 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact le_log_of 47 (by norm_num) (3.8501476) 3 (0.8501476) _ (by norm_num) hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  have hhi : Real.log ↑(47 : ℕ) ≤ (3.8501477 : ℝ) := by
    have hTL := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.8501477 : ℝ) by norm_num) 12
    exact log_le_of 47 (by norm_num) (3.8501477) 3 (0.8501477) _ (by norm_num) (by positivity) hTL
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 47) : ℝ) = (3.8501476 : ℝ) from by norm_num [logNatLo]]; exact hlo
  · rw [show (↑(logNatHi 47) : ℝ) = (3.8501477 : ℝ) from by norm_num [logNatHi]]; exact hhi

theorem M_48 : (↑(logNatLo 48) : ℝ) ≤ Real.log ↑(48 : ℕ) ∧ Real.log ↑(48 : ℕ) ≤ ↑(logNatHi 48) := by
  have h := logMul (a := 2) (b := 24) (by norm_num) (by norm_num) M_2 M_24
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 48) : ℝ) = ↑(logNatLo 2) + ↑(logNatLo 24) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 48) : ℝ) = ↑(logNatHi 2) + ↑(logNatHi 24) from by norm_num [logNatHi]]
    exact h.2

theorem M_49 : (↑(logNatLo 49) : ℝ) ≤ Real.log ↑(49 : ℕ) ∧ Real.log ↑(49 : ℕ) ≤ ↑(logNatHi 49) := by
  have h := logMul (a := 7) (b := 7) (by norm_num) (by norm_num) M_7 M_7
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 49) : ℝ) = ↑(logNatLo 7) + ↑(logNatLo 7) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 49) : ℝ) = ↑(logNatHi 7) + ↑(logNatHi 7) from by norm_num [logNatHi]]
    exact h.2

theorem M_50 : (↑(logNatLo 50) : ℝ) ≤ Real.log ↑(50 : ℕ) ∧ Real.log ↑(50 : ℕ) ≤ ↑(logNatHi 50) := by
  have h := logMul (a := 2) (b := 25) (by norm_num) (by norm_num) M_2 M_25
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 50) : ℝ) = ↑(logNatLo 2) + ↑(logNatLo 25) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 50) : ℝ) = ↑(logNatHi 2) + ↑(logNatHi 25) from by norm_num [logNatHi]]
    exact h.2

theorem M_51 : (↑(logNatLo 51) : ℝ) ≤ Real.log ↑(51 : ℕ) ∧ Real.log ↑(51 : ℕ) ≤ ↑(logNatHi 51) := by
  have h := logMul (a := 3) (b := 17) (by norm_num) (by norm_num) M_3 M_17
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 51) : ℝ) = ↑(logNatLo 3) + ↑(logNatLo 17) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 51) : ℝ) = ↑(logNatHi 3) + ↑(logNatHi 17) from by norm_num [logNatHi]]
    exact h.2

theorem M_52 : (↑(logNatLo 52) : ℝ) ≤ Real.log ↑(52 : ℕ) ∧ Real.log ↑(52 : ℕ) ≤ ↑(logNatHi 52) := by
  have h := logMul (a := 2) (b := 26) (by norm_num) (by norm_num) M_2 M_26
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 52) : ℝ) = ↑(logNatLo 2) + ↑(logNatLo 26) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 52) : ℝ) = ↑(logNatHi 2) + ↑(logNatHi 26) from by norm_num [logNatHi]]
    exact h.2

set_option maxHeartbeats 1000000 in
theorem M_53 : (↑(logNatLo 53) : ℝ) ≤ Real.log ↑(53 : ℕ) ∧ Real.log ↑(53 : ℕ) ≤ ↑(logNatHi 53) := by
  have hlo : (3.9702919 : ℝ) ≤ Real.log ↑(53 : ℕ) := by
    have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.9702919 : ℝ) by norm_num)
      (show (0.9702919 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact le_log_of 53 (by norm_num) (3.9702919) 3 (0.9702919) _ (by norm_num) hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  have hhi : Real.log ↑(53 : ℕ) ≤ (3.9702920 : ℝ) := by
    have hTL := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.9702920 : ℝ) by norm_num) 12
    exact log_le_of 53 (by norm_num) (3.9702920) 3 (0.9702920) _ (by norm_num) (by positivity) hTL
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 53) : ℝ) = (3.9702919 : ℝ) from by norm_num [logNatLo]]; exact hlo
  · rw [show (↑(logNatHi 53) : ℝ) = (3.9702920 : ℝ) from by norm_num [logNatHi]]; exact hhi

theorem M_54 : (↑(logNatLo 54) : ℝ) ≤ Real.log ↑(54 : ℕ) ∧ Real.log ↑(54 : ℕ) ≤ ↑(logNatHi 54) := by
  have h := logMul (a := 2) (b := 27) (by norm_num) (by norm_num) M_2 M_27
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 54) : ℝ) = ↑(logNatLo 2) + ↑(logNatLo 27) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 54) : ℝ) = ↑(logNatHi 2) + ↑(logNatHi 27) from by norm_num [logNatHi]]
    exact h.2

theorem M_55 : (↑(logNatLo 55) : ℝ) ≤ Real.log ↑(55 : ℕ) ∧ Real.log ↑(55 : ℕ) ≤ ↑(logNatHi 55) := by
  have h := logMul (a := 5) (b := 11) (by norm_num) (by norm_num) M_5 M_11
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 55) : ℝ) = ↑(logNatLo 5) + ↑(logNatLo 11) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 55) : ℝ) = ↑(logNatHi 5) + ↑(logNatHi 11) from by norm_num [logNatHi]]
    exact h.2

theorem M_56 : (↑(logNatLo 56) : ℝ) ≤ Real.log ↑(56 : ℕ) ∧ Real.log ↑(56 : ℕ) ≤ ↑(logNatHi 56) := by
  have h := logMul (a := 2) (b := 28) (by norm_num) (by norm_num) M_2 M_28
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 56) : ℝ) = ↑(logNatLo 2) + ↑(logNatLo 28) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 56) : ℝ) = ↑(logNatHi 2) + ↑(logNatHi 28) from by norm_num [logNatHi]]
    exact h.2

theorem M_57 : (↑(logNatLo 57) : ℝ) ≤ Real.log ↑(57 : ℕ) ∧ Real.log ↑(57 : ℕ) ≤ ↑(logNatHi 57) := by
  have h := logMul (a := 3) (b := 19) (by norm_num) (by norm_num) M_3 M_19
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 57) : ℝ) = ↑(logNatLo 3) + ↑(logNatLo 19) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 57) : ℝ) = ↑(logNatHi 3) + ↑(logNatHi 19) from by norm_num [logNatHi]]
    exact h.2

theorem M_58 : (↑(logNatLo 58) : ℝ) ≤ Real.log ↑(58 : ℕ) ∧ Real.log ↑(58 : ℕ) ≤ ↑(logNatHi 58) := by
  have h := logMul (a := 2) (b := 29) (by norm_num) (by norm_num) M_2 M_29
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 58) : ℝ) = ↑(logNatLo 2) + ↑(logNatLo 29) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 58) : ℝ) = ↑(logNatHi 2) + ↑(logNatHi 29) from by norm_num [logNatHi]]
    exact h.2

set_option maxHeartbeats 1000000 in
theorem M_59 : (↑(logNatLo 59) : ℝ) ≤ Real.log ↑(59 : ℕ) ∧ Real.log ↑(59 : ℕ) ≤ ↑(logNatHi 59) := by
  have hlo : (4.0775374 : ℝ) ≤ Real.log ↑(59 : ℕ) := by
    have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.0775374 : ℝ) by norm_num)
      (show (0.0775374 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact le_log_of 59 (by norm_num) (4.0775374) 4 (0.0775374) _ (by norm_num) hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  have hhi : Real.log ↑(59 : ℕ) ≤ (4.0775375 : ℝ) := by
    have hTL := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.0775375 : ℝ) by norm_num) 12
    exact log_le_of 59 (by norm_num) (4.0775375) 4 (0.0775375) _ (by norm_num) (by positivity) hTL
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 59) : ℝ) = (4.0775374 : ℝ) from by norm_num [logNatLo]]; exact hlo
  · rw [show (↑(logNatHi 59) : ℝ) = (4.0775375 : ℝ) from by norm_num [logNatHi]]; exact hhi

theorem M_60 : (↑(logNatLo 60) : ℝ) ≤ Real.log ↑(60 : ℕ) ∧ Real.log ↑(60 : ℕ) ≤ ↑(logNatHi 60) := by
  have h := logMul (a := 2) (b := 30) (by norm_num) (by norm_num) M_2 M_30
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 60) : ℝ) = ↑(logNatLo 2) + ↑(logNatLo 30) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 60) : ℝ) = ↑(logNatHi 2) + ↑(logNatHi 30) from by norm_num [logNatHi]]
    exact h.2

set_option maxHeartbeats 1000000 in
theorem M_61 : (↑(logNatLo 61) : ℝ) ≤ Real.log ↑(61 : ℕ) ∧ Real.log ↑(61 : ℕ) ≤ ↑(logNatHi 61) := by
  have hlo : (4.1108738 : ℝ) ≤ Real.log ↑(61 : ℕ) := by
    have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.1108738 : ℝ) by norm_num)
      (show (0.1108738 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact le_log_of 61 (by norm_num) (4.1108738) 4 (0.1108738) _ (by norm_num) hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  have hhi : Real.log ↑(61 : ℕ) ≤ (4.1108739 : ℝ) := by
    have hTL := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.1108739 : ℝ) by norm_num) 12
    exact log_le_of 61 (by norm_num) (4.1108739) 4 (0.1108739) _ (by norm_num) (by positivity) hTL
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 61) : ℝ) = (4.1108738 : ℝ) from by norm_num [logNatLo]]; exact hlo
  · rw [show (↑(logNatHi 61) : ℝ) = (4.1108739 : ℝ) from by norm_num [logNatHi]]; exact hhi

theorem M_62 : (↑(logNatLo 62) : ℝ) ≤ Real.log ↑(62 : ℕ) ∧ Real.log ↑(62 : ℕ) ≤ ↑(logNatHi 62) := by
  have h := logMul (a := 2) (b := 31) (by norm_num) (by norm_num) M_2 M_31
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 62) : ℝ) = ↑(logNatLo 2) + ↑(logNatLo 31) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 62) : ℝ) = ↑(logNatHi 2) + ↑(logNatHi 31) from by norm_num [logNatHi]]
    exact h.2

theorem M_63 : (↑(logNatLo 63) : ℝ) ≤ Real.log ↑(63 : ℕ) ∧ Real.log ↑(63 : ℕ) ≤ ↑(logNatHi 63) := by
  have h := logMul (a := 3) (b := 21) (by norm_num) (by norm_num) M_3 M_21
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 63) : ℝ) = ↑(logNatLo 3) + ↑(logNatLo 21) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 63) : ℝ) = ↑(logNatHi 3) + ↑(logNatHi 21) from by norm_num [logNatHi]]
    exact h.2

theorem M_64 : (↑(logNatLo 64) : ℝ) ≤ Real.log ↑(64 : ℕ) ∧ Real.log ↑(64 : ℕ) ≤ ↑(logNatHi 64) := by
  have h := logMul (a := 2) (b := 32) (by norm_num) (by norm_num) M_2 M_32
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 64) : ℝ) = ↑(logNatLo 2) + ↑(logNatLo 32) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 64) : ℝ) = ↑(logNatHi 2) + ↑(logNatHi 32) from by norm_num [logNatHi]]
    exact h.2

theorem M_65 : (↑(logNatLo 65) : ℝ) ≤ Real.log ↑(65 : ℕ) ∧ Real.log ↑(65 : ℕ) ≤ ↑(logNatHi 65) := by
  have h := logMul (a := 5) (b := 13) (by norm_num) (by norm_num) M_5 M_13
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 65) : ℝ) = ↑(logNatLo 5) + ↑(logNatLo 13) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 65) : ℝ) = ↑(logNatHi 5) + ↑(logNatHi 13) from by norm_num [logNatHi]]
    exact h.2

theorem M_66 : (↑(logNatLo 66) : ℝ) ≤ Real.log ↑(66 : ℕ) ∧ Real.log ↑(66 : ℕ) ≤ ↑(logNatHi 66) := by
  have h := logMul (a := 2) (b := 33) (by norm_num) (by norm_num) M_2 M_33
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 66) : ℝ) = ↑(logNatLo 2) + ↑(logNatLo 33) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 66) : ℝ) = ↑(logNatHi 2) + ↑(logNatHi 33) from by norm_num [logNatHi]]
    exact h.2

set_option maxHeartbeats 1000000 in
theorem M_67 : (↑(logNatLo 67) : ℝ) ≤ Real.log ↑(67 : ℕ) ∧ Real.log ↑(67 : ℕ) ≤ ↑(logNatHi 67) := by
  have hlo : (4.2046926 : ℝ) ≤ Real.log ↑(67 : ℕ) := by
    have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.2046926 : ℝ) by norm_num)
      (show (0.2046926 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact le_log_of 67 (by norm_num) (4.2046926) 4 (0.2046926) _ (by norm_num) hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  have hhi : Real.log ↑(67 : ℕ) ≤ (4.2046927 : ℝ) := by
    have hTL := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.2046927 : ℝ) by norm_num) 12
    exact log_le_of 67 (by norm_num) (4.2046927) 4 (0.2046927) _ (by norm_num) (by positivity) hTL
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 67) : ℝ) = (4.2046926 : ℝ) from by norm_num [logNatLo]]; exact hlo
  · rw [show (↑(logNatHi 67) : ℝ) = (4.2046927 : ℝ) from by norm_num [logNatHi]]; exact hhi

theorem M_68 : (↑(logNatLo 68) : ℝ) ≤ Real.log ↑(68 : ℕ) ∧ Real.log ↑(68 : ℕ) ≤ ↑(logNatHi 68) := by
  have h := logMul (a := 2) (b := 34) (by norm_num) (by norm_num) M_2 M_34
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 68) : ℝ) = ↑(logNatLo 2) + ↑(logNatLo 34) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 68) : ℝ) = ↑(logNatHi 2) + ↑(logNatHi 34) from by norm_num [logNatHi]]
    exact h.2

theorem M_69 : (↑(logNatLo 69) : ℝ) ≤ Real.log ↑(69 : ℕ) ∧ Real.log ↑(69 : ℕ) ≤ ↑(logNatHi 69) := by
  have h := logMul (a := 3) (b := 23) (by norm_num) (by norm_num) M_3 M_23
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 69) : ℝ) = ↑(logNatLo 3) + ↑(logNatLo 23) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 69) : ℝ) = ↑(logNatHi 3) + ↑(logNatHi 23) from by norm_num [logNatHi]]
    exact h.2

theorem M_70 : (↑(logNatLo 70) : ℝ) ≤ Real.log ↑(70 : ℕ) ∧ Real.log ↑(70 : ℕ) ≤ ↑(logNatHi 70) := by
  have h := logMul (a := 2) (b := 35) (by norm_num) (by norm_num) M_2 M_35
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 70) : ℝ) = ↑(logNatLo 2) + ↑(logNatLo 35) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 70) : ℝ) = ↑(logNatHi 2) + ↑(logNatHi 35) from by norm_num [logNatHi]]
    exact h.2

set_option maxHeartbeats 1000000 in
theorem M_71 : (↑(logNatLo 71) : ℝ) ≤ Real.log ↑(71 : ℕ) ∧ Real.log ↑(71 : ℕ) ≤ ↑(logNatHi 71) := by
  have hlo : (4.2626798 : ℝ) ≤ Real.log ↑(71 : ℕ) := by
    have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.2626798 : ℝ) by norm_num)
      (show (0.2626798 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact le_log_of 71 (by norm_num) (4.2626798) 4 (0.2626798) _ (by norm_num) hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  have hhi : Real.log ↑(71 : ℕ) ≤ (4.2626799 : ℝ) := by
    have hTL := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.2626799 : ℝ) by norm_num) 12
    exact log_le_of 71 (by norm_num) (4.2626799) 4 (0.2626799) _ (by norm_num) (by positivity) hTL
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 71) : ℝ) = (4.2626798 : ℝ) from by norm_num [logNatLo]]; exact hlo
  · rw [show (↑(logNatHi 71) : ℝ) = (4.2626799 : ℝ) from by norm_num [logNatHi]]; exact hhi

theorem M_72 : (↑(logNatLo 72) : ℝ) ≤ Real.log ↑(72 : ℕ) ∧ Real.log ↑(72 : ℕ) ≤ ↑(logNatHi 72) := by
  have h := logMul (a := 2) (b := 36) (by norm_num) (by norm_num) M_2 M_36
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 72) : ℝ) = ↑(logNatLo 2) + ↑(logNatLo 36) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 72) : ℝ) = ↑(logNatHi 2) + ↑(logNatHi 36) from by norm_num [logNatHi]]
    exact h.2

set_option maxHeartbeats 1000000 in
theorem M_73 : (↑(logNatLo 73) : ℝ) ≤ Real.log ↑(73 : ℕ) ∧ Real.log ↑(73 : ℕ) ≤ ↑(logNatHi 73) := by
  have hlo : (4.2904594 : ℝ) ≤ Real.log ↑(73 : ℕ) := by
    have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.2904594 : ℝ) by norm_num)
      (show (0.2904594 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact le_log_of 73 (by norm_num) (4.2904594) 4 (0.2904594) _ (by norm_num) hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  have hhi : Real.log ↑(73 : ℕ) ≤ (4.2904595 : ℝ) := by
    have hTL := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.2904595 : ℝ) by norm_num) 12
    exact log_le_of 73 (by norm_num) (4.2904595) 4 (0.2904595) _ (by norm_num) (by positivity) hTL
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 73) : ℝ) = (4.2904594 : ℝ) from by norm_num [logNatLo]]; exact hlo
  · rw [show (↑(logNatHi 73) : ℝ) = (4.2904595 : ℝ) from by norm_num [logNatHi]]; exact hhi

theorem M_74 : (↑(logNatLo 74) : ℝ) ≤ Real.log ↑(74 : ℕ) ∧ Real.log ↑(74 : ℕ) ≤ ↑(logNatHi 74) := by
  have h := logMul (a := 2) (b := 37) (by norm_num) (by norm_num) M_2 M_37
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 74) : ℝ) = ↑(logNatLo 2) + ↑(logNatLo 37) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 74) : ℝ) = ↑(logNatHi 2) + ↑(logNatHi 37) from by norm_num [logNatHi]]
    exact h.2

theorem M_75 : (↑(logNatLo 75) : ℝ) ≤ Real.log ↑(75 : ℕ) ∧ Real.log ↑(75 : ℕ) ≤ ↑(logNatHi 75) := by
  have h := logMul (a := 3) (b := 25) (by norm_num) (by norm_num) M_3 M_25
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 75) : ℝ) = ↑(logNatLo 3) + ↑(logNatLo 25) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 75) : ℝ) = ↑(logNatHi 3) + ↑(logNatHi 25) from by norm_num [logNatHi]]
    exact h.2

theorem M_76 : (↑(logNatLo 76) : ℝ) ≤ Real.log ↑(76 : ℕ) ∧ Real.log ↑(76 : ℕ) ≤ ↑(logNatHi 76) := by
  have h := logMul (a := 2) (b := 38) (by norm_num) (by norm_num) M_2 M_38
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 76) : ℝ) = ↑(logNatLo 2) + ↑(logNatLo 38) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 76) : ℝ) = ↑(logNatHi 2) + ↑(logNatHi 38) from by norm_num [logNatHi]]
    exact h.2

theorem M_77 : (↑(logNatLo 77) : ℝ) ≤ Real.log ↑(77 : ℕ) ∧ Real.log ↑(77 : ℕ) ≤ ↑(logNatHi 77) := by
  have h := logMul (a := 7) (b := 11) (by norm_num) (by norm_num) M_7 M_11
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 77) : ℝ) = ↑(logNatLo 7) + ↑(logNatLo 11) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 77) : ℝ) = ↑(logNatHi 7) + ↑(logNatHi 11) from by norm_num [logNatHi]]
    exact h.2

theorem M_78 : (↑(logNatLo 78) : ℝ) ≤ Real.log ↑(78 : ℕ) ∧ Real.log ↑(78 : ℕ) ≤ ↑(logNatHi 78) := by
  have h := logMul (a := 2) (b := 39) (by norm_num) (by norm_num) M_2 M_39
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 78) : ℝ) = ↑(logNatLo 2) + ↑(logNatLo 39) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 78) : ℝ) = ↑(logNatHi 2) + ↑(logNatHi 39) from by norm_num [logNatHi]]
    exact h.2

set_option maxHeartbeats 1000000 in
theorem M_79 : (↑(logNatLo 79) : ℝ) ≤ Real.log ↑(79 : ℕ) ∧ Real.log ↑(79 : ℕ) ≤ ↑(logNatHi 79) := by
  have hlo : (4.3694478 : ℝ) ≤ Real.log ↑(79 : ℕ) := by
    have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.3694478 : ℝ) by norm_num)
      (show (0.3694478 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact le_log_of 79 (by norm_num) (4.3694478) 4 (0.3694478) _ (by norm_num) hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  have hhi : Real.log ↑(79 : ℕ) ≤ (4.3694479 : ℝ) := by
    have hTL := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.3694479 : ℝ) by norm_num) 12
    exact log_le_of 79 (by norm_num) (4.3694479) 4 (0.3694479) _ (by norm_num) (by positivity) hTL
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 79) : ℝ) = (4.3694478 : ℝ) from by norm_num [logNatLo]]; exact hlo
  · rw [show (↑(logNatHi 79) : ℝ) = (4.3694479 : ℝ) from by norm_num [logNatHi]]; exact hhi

theorem M_80 : (↑(logNatLo 80) : ℝ) ≤ Real.log ↑(80 : ℕ) ∧ Real.log ↑(80 : ℕ) ≤ ↑(logNatHi 80) := by
  have h := logMul (a := 2) (b := 40) (by norm_num) (by norm_num) M_2 M_40
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 80) : ℝ) = ↑(logNatLo 2) + ↑(logNatLo 40) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 80) : ℝ) = ↑(logNatHi 2) + ↑(logNatHi 40) from by norm_num [logNatHi]]
    exact h.2

theorem M_81 : (↑(logNatLo 81) : ℝ) ≤ Real.log ↑(81 : ℕ) ∧ Real.log ↑(81 : ℕ) ≤ ↑(logNatHi 81) := by
  have h := logMul (a := 3) (b := 27) (by norm_num) (by norm_num) M_3 M_27
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 81) : ℝ) = ↑(logNatLo 3) + ↑(logNatLo 27) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 81) : ℝ) = ↑(logNatHi 3) + ↑(logNatHi 27) from by norm_num [logNatHi]]
    exact h.2

theorem M_82 : (↑(logNatLo 82) : ℝ) ≤ Real.log ↑(82 : ℕ) ∧ Real.log ↑(82 : ℕ) ≤ ↑(logNatHi 82) := by
  have h := logMul (a := 2) (b := 41) (by norm_num) (by norm_num) M_2 M_41
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 82) : ℝ) = ↑(logNatLo 2) + ↑(logNatLo 41) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 82) : ℝ) = ↑(logNatHi 2) + ↑(logNatHi 41) from by norm_num [logNatHi]]
    exact h.2

set_option maxHeartbeats 1000000 in
theorem M_83 : (↑(logNatLo 83) : ℝ) ≤ Real.log ↑(83 : ℕ) ∧ Real.log ↑(83 : ℕ) ≤ ↑(logNatHi 83) := by
  have hlo : (4.4188406 : ℝ) ≤ Real.log ↑(83 : ℕ) := by
    have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.4188406 : ℝ) by norm_num)
      (show (0.4188406 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact le_log_of 83 (by norm_num) (4.4188406) 4 (0.4188406) _ (by norm_num) hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  have hhi : Real.log ↑(83 : ℕ) ≤ (4.4188407 : ℝ) := by
    have hTL := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.4188407 : ℝ) by norm_num) 12
    exact log_le_of 83 (by norm_num) (4.4188407) 4 (0.4188407) _ (by norm_num) (by positivity) hTL
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 83) : ℝ) = (4.4188406 : ℝ) from by norm_num [logNatLo]]; exact hlo
  · rw [show (↑(logNatHi 83) : ℝ) = (4.4188407 : ℝ) from by norm_num [logNatHi]]; exact hhi

theorem M_84 : (↑(logNatLo 84) : ℝ) ≤ Real.log ↑(84 : ℕ) ∧ Real.log ↑(84 : ℕ) ≤ ↑(logNatHi 84) := by
  have h := logMul (a := 2) (b := 42) (by norm_num) (by norm_num) M_2 M_42
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 84) : ℝ) = ↑(logNatLo 2) + ↑(logNatLo 42) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 84) : ℝ) = ↑(logNatHi 2) + ↑(logNatHi 42) from by norm_num [logNatHi]]
    exact h.2

theorem M_85 : (↑(logNatLo 85) : ℝ) ≤ Real.log ↑(85 : ℕ) ∧ Real.log ↑(85 : ℕ) ≤ ↑(logNatHi 85) := by
  have h := logMul (a := 5) (b := 17) (by norm_num) (by norm_num) M_5 M_17
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 85) : ℝ) = ↑(logNatLo 5) + ↑(logNatLo 17) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 85) : ℝ) = ↑(logNatHi 5) + ↑(logNatHi 17) from by norm_num [logNatHi]]
    exact h.2

theorem M_86 : (↑(logNatLo 86) : ℝ) ≤ Real.log ↑(86 : ℕ) ∧ Real.log ↑(86 : ℕ) ≤ ↑(logNatHi 86) := by
  have h := logMul (a := 2) (b := 43) (by norm_num) (by norm_num) M_2 M_43
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 86) : ℝ) = ↑(logNatLo 2) + ↑(logNatLo 43) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 86) : ℝ) = ↑(logNatHi 2) + ↑(logNatHi 43) from by norm_num [logNatHi]]
    exact h.2

theorem M_87 : (↑(logNatLo 87) : ℝ) ≤ Real.log ↑(87 : ℕ) ∧ Real.log ↑(87 : ℕ) ≤ ↑(logNatHi 87) := by
  have h := logMul (a := 3) (b := 29) (by norm_num) (by norm_num) M_3 M_29
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 87) : ℝ) = ↑(logNatLo 3) + ↑(logNatLo 29) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 87) : ℝ) = ↑(logNatHi 3) + ↑(logNatHi 29) from by norm_num [logNatHi]]
    exact h.2

theorem M_88 : (↑(logNatLo 88) : ℝ) ≤ Real.log ↑(88 : ℕ) ∧ Real.log ↑(88 : ℕ) ≤ ↑(logNatHi 88) := by
  have h := logMul (a := 2) (b := 44) (by norm_num) (by norm_num) M_2 M_44
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 88) : ℝ) = ↑(logNatLo 2) + ↑(logNatLo 44) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 88) : ℝ) = ↑(logNatHi 2) + ↑(logNatHi 44) from by norm_num [logNatHi]]
    exact h.2

set_option maxHeartbeats 1000000 in
theorem M_89 : (↑(logNatLo 89) : ℝ) ≤ Real.log ↑(89 : ℕ) ∧ Real.log ↑(89 : ℕ) ≤ ↑(logNatHi 89) := by
  have hlo : (4.4886363 : ℝ) ≤ Real.log ↑(89 : ℕ) := by
    have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.4886363 : ℝ) by norm_num)
      (show (0.4886363 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact le_log_of 89 (by norm_num) (4.4886363) 4 (0.4886363) _ (by norm_num) hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  have hhi : Real.log ↑(89 : ℕ) ≤ (4.4886364 : ℝ) := by
    have hTL := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.4886364 : ℝ) by norm_num) 12
    exact log_le_of 89 (by norm_num) (4.4886364) 4 (0.4886364) _ (by norm_num) (by positivity) hTL
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 89) : ℝ) = (4.4886363 : ℝ) from by norm_num [logNatLo]]; exact hlo
  · rw [show (↑(logNatHi 89) : ℝ) = (4.4886364 : ℝ) from by norm_num [logNatHi]]; exact hhi

theorem M_90 : (↑(logNatLo 90) : ℝ) ≤ Real.log ↑(90 : ℕ) ∧ Real.log ↑(90 : ℕ) ≤ ↑(logNatHi 90) := by
  have h := logMul (a := 2) (b := 45) (by norm_num) (by norm_num) M_2 M_45
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 90) : ℝ) = ↑(logNatLo 2) + ↑(logNatLo 45) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 90) : ℝ) = ↑(logNatHi 2) + ↑(logNatHi 45) from by norm_num [logNatHi]]
    exact h.2

theorem M_91 : (↑(logNatLo 91) : ℝ) ≤ Real.log ↑(91 : ℕ) ∧ Real.log ↑(91 : ℕ) ≤ ↑(logNatHi 91) := by
  have h := logMul (a := 7) (b := 13) (by norm_num) (by norm_num) M_7 M_13
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 91) : ℝ) = ↑(logNatLo 7) + ↑(logNatLo 13) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 91) : ℝ) = ↑(logNatHi 7) + ↑(logNatHi 13) from by norm_num [logNatHi]]
    exact h.2

theorem M_92 : (↑(logNatLo 92) : ℝ) ≤ Real.log ↑(92 : ℕ) ∧ Real.log ↑(92 : ℕ) ≤ ↑(logNatHi 92) := by
  have h := logMul (a := 2) (b := 46) (by norm_num) (by norm_num) M_2 M_46
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 92) : ℝ) = ↑(logNatLo 2) + ↑(logNatLo 46) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 92) : ℝ) = ↑(logNatHi 2) + ↑(logNatHi 46) from by norm_num [logNatHi]]
    exact h.2

theorem M_93 : (↑(logNatLo 93) : ℝ) ≤ Real.log ↑(93 : ℕ) ∧ Real.log ↑(93 : ℕ) ≤ ↑(logNatHi 93) := by
  have h := logMul (a := 3) (b := 31) (by norm_num) (by norm_num) M_3 M_31
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 93) : ℝ) = ↑(logNatLo 3) + ↑(logNatLo 31) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 93) : ℝ) = ↑(logNatHi 3) + ↑(logNatHi 31) from by norm_num [logNatHi]]
    exact h.2

theorem M_94 : (↑(logNatLo 94) : ℝ) ≤ Real.log ↑(94 : ℕ) ∧ Real.log ↑(94 : ℕ) ≤ ↑(logNatHi 94) := by
  have h := logMul (a := 2) (b := 47) (by norm_num) (by norm_num) M_2 M_47
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 94) : ℝ) = ↑(logNatLo 2) + ↑(logNatLo 47) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 94) : ℝ) = ↑(logNatHi 2) + ↑(logNatHi 47) from by norm_num [logNatHi]]
    exact h.2

theorem M_95 : (↑(logNatLo 95) : ℝ) ≤ Real.log ↑(95 : ℕ) ∧ Real.log ↑(95 : ℕ) ≤ ↑(logNatHi 95) := by
  have h := logMul (a := 5) (b := 19) (by norm_num) (by norm_num) M_5 M_19
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 95) : ℝ) = ↑(logNatLo 5) + ↑(logNatLo 19) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 95) : ℝ) = ↑(logNatHi 5) + ↑(logNatHi 19) from by norm_num [logNatHi]]
    exact h.2

theorem M_96 : (↑(logNatLo 96) : ℝ) ≤ Real.log ↑(96 : ℕ) ∧ Real.log ↑(96 : ℕ) ≤ ↑(logNatHi 96) := by
  have h := logMul (a := 2) (b := 48) (by norm_num) (by norm_num) M_2 M_48
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 96) : ℝ) = ↑(logNatLo 2) + ↑(logNatLo 48) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 96) : ℝ) = ↑(logNatHi 2) + ↑(logNatHi 48) from by norm_num [logNatHi]]
    exact h.2

set_option maxHeartbeats 1000000 in
theorem M_97 : (↑(logNatLo 97) : ℝ) ≤ Real.log ↑(97 : ℕ) ∧ Real.log ↑(97 : ℕ) ≤ ↑(logNatHi 97) := by
  have hlo : (4.5747109 : ℝ) ≤ Real.log ↑(97 : ℕ) := by
    have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.5747109 : ℝ) by norm_num)
      (show (0.5747109 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact le_log_of 97 (by norm_num) (4.5747109) 4 (0.5747109) _ (by norm_num) hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  have hhi : Real.log ↑(97 : ℕ) ≤ (4.5747110 : ℝ) := by
    have hTL := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.5747110 : ℝ) by norm_num) 12
    exact log_le_of 97 (by norm_num) (4.5747110) 4 (0.5747110) _ (by norm_num) (by positivity) hTL
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 97) : ℝ) = (4.5747109 : ℝ) from by norm_num [logNatLo]]; exact hlo
  · rw [show (↑(logNatHi 97) : ℝ) = (4.5747110 : ℝ) from by norm_num [logNatHi]]; exact hhi

theorem M_98 : (↑(logNatLo 98) : ℝ) ≤ Real.log ↑(98 : ℕ) ∧ Real.log ↑(98 : ℕ) ≤ ↑(logNatHi 98) := by
  have h := logMul (a := 2) (b := 49) (by norm_num) (by norm_num) M_2 M_49
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 98) : ℝ) = ↑(logNatLo 2) + ↑(logNatLo 49) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 98) : ℝ) = ↑(logNatHi 2) + ↑(logNatHi 49) from by norm_num [logNatHi]]
    exact h.2

theorem M_99 : (↑(logNatLo 99) : ℝ) ≤ Real.log ↑(99 : ℕ) ∧ Real.log ↑(99 : ℕ) ≤ ↑(logNatHi 99) := by
  have h := logMul (a := 3) (b := 33) (by norm_num) (by norm_num) M_3 M_33
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 99) : ℝ) = ↑(logNatLo 3) + ↑(logNatLo 33) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 99) : ℝ) = ↑(logNatHi 3) + ↑(logNatHi 33) from by norm_num [logNatHi]]
    exact h.2

theorem M_100 : (↑(logNatLo 100) : ℝ) ≤ Real.log ↑(100 : ℕ) ∧ Real.log ↑(100 : ℕ) ≤ ↑(logNatHi 100) := by
  have h := logMul (a := 2) (b := 50) (by norm_num) (by norm_num) M_2 M_50
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 100) : ℝ) = ↑(logNatLo 2) + ↑(logNatLo 50) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 100) : ℝ) = ↑(logNatHi 2) + ↑(logNatHi 50) from by norm_num [logNatHi]]
    exact h.2

set_option maxHeartbeats 1000000 in
theorem M_101 : (↑(logNatLo 101) : ℝ) ≤ Real.log ↑(101 : ℕ) ∧ Real.log ↑(101 : ℕ) ≤ ↑(logNatHi 101) := by
  have hlo : (4.6151205 : ℝ) ≤ Real.log ↑(101 : ℕ) := by
    have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.6151205 : ℝ) by norm_num)
      (show (0.6151205 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact le_log_of 101 (by norm_num) (4.6151205) 4 (0.6151205) _ (by norm_num) hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  have hhi : Real.log ↑(101 : ℕ) ≤ (4.6151206 : ℝ) := by
    have hTL := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.6151206 : ℝ) by norm_num) 12
    exact log_le_of 101 (by norm_num) (4.6151206) 4 (0.6151206) _ (by norm_num) (by positivity) hTL
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 101) : ℝ) = (4.6151205 : ℝ) from by norm_num [logNatLo]]; exact hlo
  · rw [show (↑(logNatHi 101) : ℝ) = (4.6151206 : ℝ) from by norm_num [logNatHi]]; exact hhi

theorem M_102 : (↑(logNatLo 102) : ℝ) ≤ Real.log ↑(102 : ℕ) ∧ Real.log ↑(102 : ℕ) ≤ ↑(logNatHi 102) := by
  have h := logMul (a := 2) (b := 51) (by norm_num) (by norm_num) M_2 M_51
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 102) : ℝ) = ↑(logNatLo 2) + ↑(logNatLo 51) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 102) : ℝ) = ↑(logNatHi 2) + ↑(logNatHi 51) from by norm_num [logNatHi]]
    exact h.2

set_option maxHeartbeats 1000000 in
theorem M_103 : (↑(logNatLo 103) : ℝ) ≤ Real.log ↑(103 : ℕ) ∧ Real.log ↑(103 : ℕ) ≤ ↑(logNatHi 103) := by
  have hlo : (4.6347289 : ℝ) ≤ Real.log ↑(103 : ℕ) := by
    have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.6347289 : ℝ) by norm_num)
      (show (0.6347289 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact le_log_of 103 (by norm_num) (4.6347289) 4 (0.6347289) _ (by norm_num) hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  have hhi : Real.log ↑(103 : ℕ) ≤ (4.6347290 : ℝ) := by
    have hTL := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.6347290 : ℝ) by norm_num) 12
    exact log_le_of 103 (by norm_num) (4.6347290) 4 (0.6347290) _ (by norm_num) (by positivity) hTL
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 103) : ℝ) = (4.6347289 : ℝ) from by norm_num [logNatLo]]; exact hlo
  · rw [show (↑(logNatHi 103) : ℝ) = (4.6347290 : ℝ) from by norm_num [logNatHi]]; exact hhi

theorem M_104 : (↑(logNatLo 104) : ℝ) ≤ Real.log ↑(104 : ℕ) ∧ Real.log ↑(104 : ℕ) ≤ ↑(logNatHi 104) := by
  have h := logMul (a := 2) (b := 52) (by norm_num) (by norm_num) M_2 M_52
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 104) : ℝ) = ↑(logNatLo 2) + ↑(logNatLo 52) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 104) : ℝ) = ↑(logNatHi 2) + ↑(logNatHi 52) from by norm_num [logNatHi]]
    exact h.2

theorem M_105 : (↑(logNatLo 105) : ℝ) ≤ Real.log ↑(105 : ℕ) ∧ Real.log ↑(105 : ℕ) ≤ ↑(logNatHi 105) := by
  have h := logMul (a := 3) (b := 35) (by norm_num) (by norm_num) M_3 M_35
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 105) : ℝ) = ↑(logNatLo 3) + ↑(logNatLo 35) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 105) : ℝ) = ↑(logNatHi 3) + ↑(logNatHi 35) from by norm_num [logNatHi]]
    exact h.2

theorem M_106 : (↑(logNatLo 106) : ℝ) ≤ Real.log ↑(106 : ℕ) ∧ Real.log ↑(106 : ℕ) ≤ ↑(logNatHi 106) := by
  have h := logMul (a := 2) (b := 53) (by norm_num) (by norm_num) M_2 M_53
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 106) : ℝ) = ↑(logNatLo 2) + ↑(logNatLo 53) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 106) : ℝ) = ↑(logNatHi 2) + ↑(logNatHi 53) from by norm_num [logNatHi]]
    exact h.2

set_option maxHeartbeats 1000000 in
theorem M_107 : (↑(logNatLo 107) : ℝ) ≤ Real.log ↑(107 : ℕ) ∧ Real.log ↑(107 : ℕ) ≤ ↑(logNatHi 107) := by
  have hlo : (4.6728288 : ℝ) ≤ Real.log ↑(107 : ℕ) := by
    have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.6728288 : ℝ) by norm_num)
      (show (0.6728288 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact le_log_of 107 (by norm_num) (4.6728288) 4 (0.6728288) _ (by norm_num) hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  have hhi : Real.log ↑(107 : ℕ) ≤ (4.6728289 : ℝ) := by
    have hTL := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.6728289 : ℝ) by norm_num) 12
    exact log_le_of 107 (by norm_num) (4.6728289) 4 (0.6728289) _ (by norm_num) (by positivity) hTL
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 107) : ℝ) = (4.6728288 : ℝ) from by norm_num [logNatLo]]; exact hlo
  · rw [show (↑(logNatHi 107) : ℝ) = (4.6728289 : ℝ) from by norm_num [logNatHi]]; exact hhi

theorem M_108 : (↑(logNatLo 108) : ℝ) ≤ Real.log ↑(108 : ℕ) ∧ Real.log ↑(108 : ℕ) ≤ ↑(logNatHi 108) := by
  have h := logMul (a := 2) (b := 54) (by norm_num) (by norm_num) M_2 M_54
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 108) : ℝ) = ↑(logNatLo 2) + ↑(logNatLo 54) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 108) : ℝ) = ↑(logNatHi 2) + ↑(logNatHi 54) from by norm_num [logNatHi]]
    exact h.2

set_option maxHeartbeats 1000000 in
theorem M_109 : (↑(logNatLo 109) : ℝ) ≤ Real.log ↑(109 : ℕ) ∧ Real.log ↑(109 : ℕ) ≤ ↑(logNatHi 109) := by
  have hlo : (4.6913478 : ℝ) ≤ Real.log ↑(109 : ℕ) := by
    have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.6913478 : ℝ) by norm_num)
      (show (0.6913478 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact le_log_of 109 (by norm_num) (4.6913478) 4 (0.6913478) _ (by norm_num) hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  have hhi : Real.log ↑(109 : ℕ) ≤ (4.6913479 : ℝ) := by
    have hTL := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.6913479 : ℝ) by norm_num) 12
    exact log_le_of 109 (by norm_num) (4.6913479) 4 (0.6913479) _ (by norm_num) (by positivity) hTL
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 109) : ℝ) = (4.6913478 : ℝ) from by norm_num [logNatLo]]; exact hlo
  · rw [show (↑(logNatHi 109) : ℝ) = (4.6913479 : ℝ) from by norm_num [logNatHi]]; exact hhi

theorem M_110 : (↑(logNatLo 110) : ℝ) ≤ Real.log ↑(110 : ℕ) ∧ Real.log ↑(110 : ℕ) ≤ ↑(logNatHi 110) := by
  have h := logMul (a := 2) (b := 55) (by norm_num) (by norm_num) M_2 M_55
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 110) : ℝ) = ↑(logNatLo 2) + ↑(logNatLo 55) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 110) : ℝ) = ↑(logNatHi 2) + ↑(logNatHi 55) from by norm_num [logNatHi]]
    exact h.2

theorem M_111 : (↑(logNatLo 111) : ℝ) ≤ Real.log ↑(111 : ℕ) ∧ Real.log ↑(111 : ℕ) ≤ ↑(logNatHi 111) := by
  have h := logMul (a := 3) (b := 37) (by norm_num) (by norm_num) M_3 M_37
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 111) : ℝ) = ↑(logNatLo 3) + ↑(logNatLo 37) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 111) : ℝ) = ↑(logNatHi 3) + ↑(logNatHi 37) from by norm_num [logNatHi]]
    exact h.2

theorem M_112 : (↑(logNatLo 112) : ℝ) ≤ Real.log ↑(112 : ℕ) ∧ Real.log ↑(112 : ℕ) ≤ ↑(logNatHi 112) := by
  have h := logMul (a := 2) (b := 56) (by norm_num) (by norm_num) M_2 M_56
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 112) : ℝ) = ↑(logNatLo 2) + ↑(logNatLo 56) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 112) : ℝ) = ↑(logNatHi 2) + ↑(logNatHi 56) from by norm_num [logNatHi]]
    exact h.2

set_option maxHeartbeats 1000000 in
theorem M_113 : (↑(logNatLo 113) : ℝ) ≤ Real.log ↑(113 : ℕ) ∧ Real.log ↑(113 : ℕ) ≤ ↑(logNatHi 113) := by
  have hlo : (4.7273878 : ℝ) ≤ Real.log ↑(113 : ℕ) := by
    have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.7273878 : ℝ) by norm_num)
      (show (0.7273878 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact le_log_of 113 (by norm_num) (4.7273878) 4 (0.7273878) _ (by norm_num) hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  have hhi : Real.log ↑(113 : ℕ) ≤ (4.7273879 : ℝ) := by
    have hTL := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.7273879 : ℝ) by norm_num) 12
    exact log_le_of 113 (by norm_num) (4.7273879) 4 (0.7273879) _ (by norm_num) (by positivity) hTL
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 113) : ℝ) = (4.7273878 : ℝ) from by norm_num [logNatLo]]; exact hlo
  · rw [show (↑(logNatHi 113) : ℝ) = (4.7273879 : ℝ) from by norm_num [logNatHi]]; exact hhi

theorem M_114 : (↑(logNatLo 114) : ℝ) ≤ Real.log ↑(114 : ℕ) ∧ Real.log ↑(114 : ℕ) ≤ ↑(logNatHi 114) := by
  have h := logMul (a := 2) (b := 57) (by norm_num) (by norm_num) M_2 M_57
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 114) : ℝ) = ↑(logNatLo 2) + ↑(logNatLo 57) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 114) : ℝ) = ↑(logNatHi 2) + ↑(logNatHi 57) from by norm_num [logNatHi]]
    exact h.2

theorem M_115 : (↑(logNatLo 115) : ℝ) ≤ Real.log ↑(115 : ℕ) ∧ Real.log ↑(115 : ℕ) ≤ ↑(logNatHi 115) := by
  have h := logMul (a := 5) (b := 23) (by norm_num) (by norm_num) M_5 M_23
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 115) : ℝ) = ↑(logNatLo 5) + ↑(logNatLo 23) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 115) : ℝ) = ↑(logNatHi 5) + ↑(logNatHi 23) from by norm_num [logNatHi]]
    exact h.2

theorem M_116 : (↑(logNatLo 116) : ℝ) ≤ Real.log ↑(116 : ℕ) ∧ Real.log ↑(116 : ℕ) ≤ ↑(logNatHi 116) := by
  have h := logMul (a := 2) (b := 58) (by norm_num) (by norm_num) M_2 M_58
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 116) : ℝ) = ↑(logNatLo 2) + ↑(logNatLo 58) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 116) : ℝ) = ↑(logNatHi 2) + ↑(logNatHi 58) from by norm_num [logNatHi]]
    exact h.2

theorem M_117 : (↑(logNatLo 117) : ℝ) ≤ Real.log ↑(117 : ℕ) ∧ Real.log ↑(117 : ℕ) ≤ ↑(logNatHi 117) := by
  have h := logMul (a := 3) (b := 39) (by norm_num) (by norm_num) M_3 M_39
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 117) : ℝ) = ↑(logNatLo 3) + ↑(logNatLo 39) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 117) : ℝ) = ↑(logNatHi 3) + ↑(logNatHi 39) from by norm_num [logNatHi]]
    exact h.2

theorem M_118 : (↑(logNatLo 118) : ℝ) ≤ Real.log ↑(118 : ℕ) ∧ Real.log ↑(118 : ℕ) ≤ ↑(logNatHi 118) := by
  have h := logMul (a := 2) (b := 59) (by norm_num) (by norm_num) M_2 M_59
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 118) : ℝ) = ↑(logNatLo 2) + ↑(logNatLo 59) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 118) : ℝ) = ↑(logNatHi 2) + ↑(logNatHi 59) from by norm_num [logNatHi]]
    exact h.2

theorem M_119 : (↑(logNatLo 119) : ℝ) ≤ Real.log ↑(119 : ℕ) ∧ Real.log ↑(119 : ℕ) ≤ ↑(logNatHi 119) := by
  have h := logMul (a := 7) (b := 17) (by norm_num) (by norm_num) M_7 M_17
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 119) : ℝ) = ↑(logNatLo 7) + ↑(logNatLo 17) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 119) : ℝ) = ↑(logNatHi 7) + ↑(logNatHi 17) from by norm_num [logNatHi]]
    exact h.2

theorem M_120 : (↑(logNatLo 120) : ℝ) ≤ Real.log ↑(120 : ℕ) ∧ Real.log ↑(120 : ℕ) ≤ ↑(logNatHi 120) := by
  have h := logMul (a := 2) (b := 60) (by norm_num) (by norm_num) M_2 M_60
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 120) : ℝ) = ↑(logNatLo 2) + ↑(logNatLo 60) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 120) : ℝ) = ↑(logNatHi 2) + ↑(logNatHi 60) from by norm_num [logNatHi]]
    exact h.2

theorem M_121 : (↑(logNatLo 121) : ℝ) ≤ Real.log ↑(121 : ℕ) ∧ Real.log ↑(121 : ℕ) ≤ ↑(logNatHi 121) := by
  have h := logMul (a := 11) (b := 11) (by norm_num) (by norm_num) M_11 M_11
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 121) : ℝ) = ↑(logNatLo 11) + ↑(logNatLo 11) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 121) : ℝ) = ↑(logNatHi 11) + ↑(logNatHi 11) from by norm_num [logNatHi]]
    exact h.2

theorem M_122 : (↑(logNatLo 122) : ℝ) ≤ Real.log ↑(122 : ℕ) ∧ Real.log ↑(122 : ℕ) ≤ ↑(logNatHi 122) := by
  have h := logMul (a := 2) (b := 61) (by norm_num) (by norm_num) M_2 M_61
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 122) : ℝ) = ↑(logNatLo 2) + ↑(logNatLo 61) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 122) : ℝ) = ↑(logNatHi 2) + ↑(logNatHi 61) from by norm_num [logNatHi]]
    exact h.2

theorem M_123 : (↑(logNatLo 123) : ℝ) ≤ Real.log ↑(123 : ℕ) ∧ Real.log ↑(123 : ℕ) ≤ ↑(logNatHi 123) := by
  have h := logMul (a := 3) (b := 41) (by norm_num) (by norm_num) M_3 M_41
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 123) : ℝ) = ↑(logNatLo 3) + ↑(logNatLo 41) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 123) : ℝ) = ↑(logNatHi 3) + ↑(logNatHi 41) from by norm_num [logNatHi]]
    exact h.2

theorem M_124 : (↑(logNatLo 124) : ℝ) ≤ Real.log ↑(124 : ℕ) ∧ Real.log ↑(124 : ℕ) ≤ ↑(logNatHi 124) := by
  have h := logMul (a := 2) (b := 62) (by norm_num) (by norm_num) M_2 M_62
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 124) : ℝ) = ↑(logNatLo 2) + ↑(logNatLo 62) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 124) : ℝ) = ↑(logNatHi 2) + ↑(logNatHi 62) from by norm_num [logNatHi]]
    exact h.2

theorem M_125 : (↑(logNatLo 125) : ℝ) ≤ Real.log ↑(125 : ℕ) ∧ Real.log ↑(125 : ℕ) ≤ ↑(logNatHi 125) := by
  have h := logMul (a := 5) (b := 25) (by norm_num) (by norm_num) M_5 M_25
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 125) : ℝ) = ↑(logNatLo 5) + ↑(logNatLo 25) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 125) : ℝ) = ↑(logNatHi 5) + ↑(logNatHi 25) from by norm_num [logNatHi]]
    exact h.2

theorem M_126 : (↑(logNatLo 126) : ℝ) ≤ Real.log ↑(126 : ℕ) ∧ Real.log ↑(126 : ℕ) ≤ ↑(logNatHi 126) := by
  have h := logMul (a := 2) (b := 63) (by norm_num) (by norm_num) M_2 M_63
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 126) : ℝ) = ↑(logNatLo 2) + ↑(logNatLo 63) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 126) : ℝ) = ↑(logNatHi 2) + ↑(logNatHi 63) from by norm_num [logNatHi]]
    exact h.2

set_option maxHeartbeats 1000000 in
theorem M_127 : (↑(logNatLo 127) : ℝ) ≤ Real.log ↑(127 : ℕ) ∧ Real.log ↑(127 : ℕ) ≤ ↑(logNatHi 127) := by
  have hlo : (4.8441870 : ℝ) ≤ Real.log ↑(127 : ℕ) := by
    have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.8441870 : ℝ) by norm_num)
      (show (0.8441870 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact le_log_of 127 (by norm_num) (4.8441870) 4 (0.8441870) _ (by norm_num) hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  have hhi : Real.log ↑(127 : ℕ) ≤ (4.8441871 : ℝ) := by
    have hTL := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.8441871 : ℝ) by norm_num) 12
    exact log_le_of 127 (by norm_num) (4.8441871) 4 (0.8441871) _ (by norm_num) (by positivity) hTL
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 127) : ℝ) = (4.8441870 : ℝ) from by norm_num [logNatLo]]; exact hlo
  · rw [show (↑(logNatHi 127) : ℝ) = (4.8441871 : ℝ) from by norm_num [logNatHi]]; exact hhi

theorem M_128 : (↑(logNatLo 128) : ℝ) ≤ Real.log ↑(128 : ℕ) ∧ Real.log ↑(128 : ℕ) ≤ ↑(logNatHi 128) := by
  have h := logMul (a := 2) (b := 64) (by norm_num) (by norm_num) M_2 M_64
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 128) : ℝ) = ↑(logNatLo 2) + ↑(logNatLo 64) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 128) : ℝ) = ↑(logNatHi 2) + ↑(logNatHi 64) from by norm_num [logNatHi]]
    exact h.2

theorem M_129 : (↑(logNatLo 129) : ℝ) ≤ Real.log ↑(129 : ℕ) ∧ Real.log ↑(129 : ℕ) ≤ ↑(logNatHi 129) := by
  have h := logMul (a := 3) (b := 43) (by norm_num) (by norm_num) M_3 M_43
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 129) : ℝ) = ↑(logNatLo 3) + ↑(logNatLo 43) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 129) : ℝ) = ↑(logNatHi 3) + ↑(logNatHi 43) from by norm_num [logNatHi]]
    exact h.2

theorem M_130 : (↑(logNatLo 130) : ℝ) ≤ Real.log ↑(130 : ℕ) ∧ Real.log ↑(130 : ℕ) ≤ ↑(logNatHi 130) := by
  have h := logMul (a := 2) (b := 65) (by norm_num) (by norm_num) M_2 M_65
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 130) : ℝ) = ↑(logNatLo 2) + ↑(logNatLo 65) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 130) : ℝ) = ↑(logNatHi 2) + ↑(logNatHi 65) from by norm_num [logNatHi]]
    exact h.2

set_option maxHeartbeats 1000000 in
theorem M_131 : (↑(logNatLo 131) : ℝ) ≤ Real.log ↑(131 : ℕ) ∧ Real.log ↑(131 : ℕ) ≤ ↑(logNatHi 131) := by
  have hlo : (4.8751973 : ℝ) ≤ Real.log ↑(131 : ℕ) := by
    have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.8751973 : ℝ) by norm_num)
      (show (0.8751973 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact le_log_of 131 (by norm_num) (4.8751973) 4 (0.8751973) _ (by norm_num) hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  have hhi : Real.log ↑(131 : ℕ) ≤ (4.8751974 : ℝ) := by
    have hTL := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.8751974 : ℝ) by norm_num) 12
    exact log_le_of 131 (by norm_num) (4.8751974) 4 (0.8751974) _ (by norm_num) (by positivity) hTL
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 131) : ℝ) = (4.8751973 : ℝ) from by norm_num [logNatLo]]; exact hlo
  · rw [show (↑(logNatHi 131) : ℝ) = (4.8751974 : ℝ) from by norm_num [logNatHi]]; exact hhi

theorem M_132 : (↑(logNatLo 132) : ℝ) ≤ Real.log ↑(132 : ℕ) ∧ Real.log ↑(132 : ℕ) ≤ ↑(logNatHi 132) := by
  have h := logMul (a := 2) (b := 66) (by norm_num) (by norm_num) M_2 M_66
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 132) : ℝ) = ↑(logNatLo 2) + ↑(logNatLo 66) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 132) : ℝ) = ↑(logNatHi 2) + ↑(logNatHi 66) from by norm_num [logNatHi]]
    exact h.2

theorem M_133 : (↑(logNatLo 133) : ℝ) ≤ Real.log ↑(133 : ℕ) ∧ Real.log ↑(133 : ℕ) ≤ ↑(logNatHi 133) := by
  have h := logMul (a := 7) (b := 19) (by norm_num) (by norm_num) M_7 M_19
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 133) : ℝ) = ↑(logNatLo 7) + ↑(logNatLo 19) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 133) : ℝ) = ↑(logNatHi 7) + ↑(logNatHi 19) from by norm_num [logNatHi]]
    exact h.2

theorem M_134 : (↑(logNatLo 134) : ℝ) ≤ Real.log ↑(134 : ℕ) ∧ Real.log ↑(134 : ℕ) ≤ ↑(logNatHi 134) := by
  have h := logMul (a := 2) (b := 67) (by norm_num) (by norm_num) M_2 M_67
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 134) : ℝ) = ↑(logNatLo 2) + ↑(logNatLo 67) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 134) : ℝ) = ↑(logNatHi 2) + ↑(logNatHi 67) from by norm_num [logNatHi]]
    exact h.2

theorem M_135 : (↑(logNatLo 135) : ℝ) ≤ Real.log ↑(135 : ℕ) ∧ Real.log ↑(135 : ℕ) ≤ ↑(logNatHi 135) := by
  have h := logMul (a := 3) (b := 45) (by norm_num) (by norm_num) M_3 M_45
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 135) : ℝ) = ↑(logNatLo 3) + ↑(logNatLo 45) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 135) : ℝ) = ↑(logNatHi 3) + ↑(logNatHi 45) from by norm_num [logNatHi]]
    exact h.2

theorem M_136 : (↑(logNatLo 136) : ℝ) ≤ Real.log ↑(136 : ℕ) ∧ Real.log ↑(136 : ℕ) ≤ ↑(logNatHi 136) := by
  have h := logMul (a := 2) (b := 68) (by norm_num) (by norm_num) M_2 M_68
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 136) : ℝ) = ↑(logNatLo 2) + ↑(logNatLo 68) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 136) : ℝ) = ↑(logNatHi 2) + ↑(logNatHi 68) from by norm_num [logNatHi]]
    exact h.2

set_option maxHeartbeats 1000000 in
theorem M_137 : (↑(logNatLo 137) : ℝ) ≤ Real.log ↑(137 : ℕ) ∧ Real.log ↑(137 : ℕ) ≤ ↑(logNatHi 137) := by
  have hlo : (4.9199809 : ℝ) ≤ Real.log ↑(137 : ℕ) := by
    have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.9199809 : ℝ) by norm_num)
      (show (0.9199809 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact le_log_of 137 (by norm_num) (4.9199809) 4 (0.9199809) _ (by norm_num) hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  have hhi : Real.log ↑(137 : ℕ) ≤ (4.9199810 : ℝ) := by
    have hTL := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.9199810 : ℝ) by norm_num) 12
    exact log_le_of 137 (by norm_num) (4.9199810) 4 (0.9199810) _ (by norm_num) (by positivity) hTL
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 137) : ℝ) = (4.9199809 : ℝ) from by norm_num [logNatLo]]; exact hlo
  · rw [show (↑(logNatHi 137) : ℝ) = (4.9199810 : ℝ) from by norm_num [logNatHi]]; exact hhi

theorem M_138 : (↑(logNatLo 138) : ℝ) ≤ Real.log ↑(138 : ℕ) ∧ Real.log ↑(138 : ℕ) ≤ ↑(logNatHi 138) := by
  have h := logMul (a := 2) (b := 69) (by norm_num) (by norm_num) M_2 M_69
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 138) : ℝ) = ↑(logNatLo 2) + ↑(logNatLo 69) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 138) : ℝ) = ↑(logNatHi 2) + ↑(logNatHi 69) from by norm_num [logNatHi]]
    exact h.2

set_option maxHeartbeats 1000000 in
theorem M_139 : (↑(logNatLo 139) : ℝ) ≤ Real.log ↑(139 : ℕ) ∧ Real.log ↑(139 : ℕ) ≤ ↑(logNatHi 139) := by
  have hlo : (4.9344739 : ℝ) ≤ Real.log ↑(139 : ℕ) := by
    have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.9344739 : ℝ) by norm_num)
      (show (0.9344739 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact le_log_of 139 (by norm_num) (4.9344739) 4 (0.9344739) _ (by norm_num) hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  have hhi : Real.log ↑(139 : ℕ) ≤ (4.9344740 : ℝ) := by
    have hTL := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.9344740 : ℝ) by norm_num) 12
    exact log_le_of 139 (by norm_num) (4.9344740) 4 (0.9344740) _ (by norm_num) (by positivity) hTL
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 139) : ℝ) = (4.9344739 : ℝ) from by norm_num [logNatLo]]; exact hlo
  · rw [show (↑(logNatHi 139) : ℝ) = (4.9344740 : ℝ) from by norm_num [logNatHi]]; exact hhi

theorem M_140 : (↑(logNatLo 140) : ℝ) ≤ Real.log ↑(140 : ℕ) ∧ Real.log ↑(140 : ℕ) ≤ ↑(logNatHi 140) := by
  have h := logMul (a := 2) (b := 70) (by norm_num) (by norm_num) M_2 M_70
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 140) : ℝ) = ↑(logNatLo 2) + ↑(logNatLo 70) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 140) : ℝ) = ↑(logNatHi 2) + ↑(logNatHi 70) from by norm_num [logNatHi]]
    exact h.2

theorem M_141 : (↑(logNatLo 141) : ℝ) ≤ Real.log ↑(141 : ℕ) ∧ Real.log ↑(141 : ℕ) ≤ ↑(logNatHi 141) := by
  have h := logMul (a := 3) (b := 47) (by norm_num) (by norm_num) M_3 M_47
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 141) : ℝ) = ↑(logNatLo 3) + ↑(logNatLo 47) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 141) : ℝ) = ↑(logNatHi 3) + ↑(logNatHi 47) from by norm_num [logNatHi]]
    exact h.2

theorem M_142 : (↑(logNatLo 142) : ℝ) ≤ Real.log ↑(142 : ℕ) ∧ Real.log ↑(142 : ℕ) ≤ ↑(logNatHi 142) := by
  have h := logMul (a := 2) (b := 71) (by norm_num) (by norm_num) M_2 M_71
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 142) : ℝ) = ↑(logNatLo 2) + ↑(logNatLo 71) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 142) : ℝ) = ↑(logNatHi 2) + ↑(logNatHi 71) from by norm_num [logNatHi]]
    exact h.2

theorem M_143 : (↑(logNatLo 143) : ℝ) ≤ Real.log ↑(143 : ℕ) ∧ Real.log ↑(143 : ℕ) ≤ ↑(logNatHi 143) := by
  have h := logMul (a := 11) (b := 13) (by norm_num) (by norm_num) M_11 M_13
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 143) : ℝ) = ↑(logNatLo 11) + ↑(logNatLo 13) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 143) : ℝ) = ↑(logNatHi 11) + ↑(logNatHi 13) from by norm_num [logNatHi]]
    exact h.2

theorem M_144 : (↑(logNatLo 144) : ℝ) ≤ Real.log ↑(144 : ℕ) ∧ Real.log ↑(144 : ℕ) ≤ ↑(logNatHi 144) := by
  have h := logMul (a := 2) (b := 72) (by norm_num) (by norm_num) M_2 M_72
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 144) : ℝ) = ↑(logNatLo 2) + ↑(logNatLo 72) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 144) : ℝ) = ↑(logNatHi 2) + ↑(logNatHi 72) from by norm_num [logNatHi]]
    exact h.2

theorem M_145 : (↑(logNatLo 145) : ℝ) ≤ Real.log ↑(145 : ℕ) ∧ Real.log ↑(145 : ℕ) ≤ ↑(logNatHi 145) := by
  have h := logMul (a := 5) (b := 29) (by norm_num) (by norm_num) M_5 M_29
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 145) : ℝ) = ↑(logNatLo 5) + ↑(logNatLo 29) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 145) : ℝ) = ↑(logNatHi 5) + ↑(logNatHi 29) from by norm_num [logNatHi]]
    exact h.2

theorem M_146 : (↑(logNatLo 146) : ℝ) ≤ Real.log ↑(146 : ℕ) ∧ Real.log ↑(146 : ℕ) ≤ ↑(logNatHi 146) := by
  have h := logMul (a := 2) (b := 73) (by norm_num) (by norm_num) M_2 M_73
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 146) : ℝ) = ↑(logNatLo 2) + ↑(logNatLo 73) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 146) : ℝ) = ↑(logNatHi 2) + ↑(logNatHi 73) from by norm_num [logNatHi]]
    exact h.2

theorem M_147 : (↑(logNatLo 147) : ℝ) ≤ Real.log ↑(147 : ℕ) ∧ Real.log ↑(147 : ℕ) ≤ ↑(logNatHi 147) := by
  have h := logMul (a := 3) (b := 49) (by norm_num) (by norm_num) M_3 M_49
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 147) : ℝ) = ↑(logNatLo 3) + ↑(logNatLo 49) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 147) : ℝ) = ↑(logNatHi 3) + ↑(logNatHi 49) from by norm_num [logNatHi]]
    exact h.2

theorem M_148 : (↑(logNatLo 148) : ℝ) ≤ Real.log ↑(148 : ℕ) ∧ Real.log ↑(148 : ℕ) ≤ ↑(logNatHi 148) := by
  have h := logMul (a := 2) (b := 74) (by norm_num) (by norm_num) M_2 M_74
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 148) : ℝ) = ↑(logNatLo 2) + ↑(logNatLo 74) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 148) : ℝ) = ↑(logNatHi 2) + ↑(logNatHi 74) from by norm_num [logNatHi]]
    exact h.2

set_option maxHeartbeats 1000000 in
theorem M_149 : (↑(logNatLo 149) : ℝ) ≤ Real.log ↑(149 : ℕ) ∧ Real.log ↑(149 : ℕ) ≤ ↑(logNatHi 149) := by
  have hlo : (5.0039463 : ℝ) ≤ Real.log ↑(149 : ℕ) := by
    have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.0039463 : ℝ) by norm_num)
      (show (0.0039463 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact le_log_of 149 (by norm_num) (5.0039463) 5 (0.0039463) _ (by norm_num) hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  have hhi : Real.log ↑(149 : ℕ) ≤ (5.0039464 : ℝ) := by
    have hTL := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.0039464 : ℝ) by norm_num) 12
    exact log_le_of 149 (by norm_num) (5.0039464) 5 (0.0039464) _ (by norm_num) (by positivity) hTL
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 149) : ℝ) = (5.0039463 : ℝ) from by norm_num [logNatLo]]; exact hlo
  · rw [show (↑(logNatHi 149) : ℝ) = (5.0039464 : ℝ) from by norm_num [logNatHi]]; exact hhi

theorem M_150 : (↑(logNatLo 150) : ℝ) ≤ Real.log ↑(150 : ℕ) ∧ Real.log ↑(150 : ℕ) ≤ ↑(logNatHi 150) := by
  have h := logMul (a := 2) (b := 75) (by norm_num) (by norm_num) M_2 M_75
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 150) : ℝ) = ↑(logNatLo 2) + ↑(logNatLo 75) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 150) : ℝ) = ↑(logNatHi 2) + ↑(logNatHi 75) from by norm_num [logNatHi]]
    exact h.2

set_option maxHeartbeats 1000000 in
theorem M_151 : (↑(logNatLo 151) : ℝ) ≤ Real.log ↑(151 : ℕ) ∧ Real.log ↑(151 : ℕ) ≤ ↑(logNatHi 151) := by
  have hlo : (5.0172798 : ℝ) ≤ Real.log ↑(151 : ℕ) := by
    have hTU := Real.exp_bound' (show (0 : ℝ) ≤ (0.0172798 : ℝ) by norm_num)
      (show (0.0172798 : ℝ) ≤ 1 by norm_num) (n := 12) (by norm_num)
    exact le_log_of 151 (by norm_num) (5.0172798) 5 (0.0172798) _ (by norm_num) hTU
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  have hhi : Real.log ↑(151 : ℕ) ≤ (5.0172799 : ℝ) := by
    have hTL := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (0.0172799 : ℝ) by norm_num) 12
    exact log_le_of 151 (by norm_num) (5.0172799) 5 (0.0172799) _ (by norm_num) (by positivity) hTL
      (by norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial])
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 151) : ℝ) = (5.0172798 : ℝ) from by norm_num [logNatLo]]; exact hlo
  · rw [show (↑(logNatHi 151) : ℝ) = (5.0172799 : ℝ) from by norm_num [logNatHi]]; exact hhi

theorem M_152 : (↑(logNatLo 152) : ℝ) ≤ Real.log ↑(152 : ℕ) ∧ Real.log ↑(152 : ℕ) ≤ ↑(logNatHi 152) := by
  have h := logMul (a := 2) (b := 76) (by norm_num) (by norm_num) M_2 M_76
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 152) : ℝ) = ↑(logNatLo 2) + ↑(logNatLo 76) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 152) : ℝ) = ↑(logNatHi 2) + ↑(logNatHi 76) from by norm_num [logNatHi]]
    exact h.2

theorem M_153 : (↑(logNatLo 153) : ℝ) ≤ Real.log ↑(153 : ℕ) ∧ Real.log ↑(153 : ℕ) ≤ ↑(logNatHi 153) := by
  have h := logMul (a := 3) (b := 51) (by norm_num) (by norm_num) M_3 M_51
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 153) : ℝ) = ↑(logNatLo 3) + ↑(logNatLo 51) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 153) : ℝ) = ↑(logNatHi 3) + ↑(logNatHi 51) from by norm_num [logNatHi]]
    exact h.2

theorem M_154 : (↑(logNatLo 154) : ℝ) ≤ Real.log ↑(154 : ℕ) ∧ Real.log ↑(154 : ℕ) ≤ ↑(logNatHi 154) := by
  have h := logMul (a := 2) (b := 77) (by norm_num) (by norm_num) M_2 M_77
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 154) : ℝ) = ↑(logNatLo 2) + ↑(logNatLo 77) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 154) : ℝ) = ↑(logNatHi 2) + ↑(logNatHi 77) from by norm_num [logNatHi]]
    exact h.2

theorem M_155 : (↑(logNatLo 155) : ℝ) ≤ Real.log ↑(155 : ℕ) ∧ Real.log ↑(155 : ℕ) ≤ ↑(logNatHi 155) := by
  have h := logMul (a := 5) (b := 31) (by norm_num) (by norm_num) M_5 M_31
  refine ⟨?_, ?_⟩
  · rw [show (↑(logNatLo 155) : ℝ) = ↑(logNatLo 5) + ↑(logNatLo 31) from by norm_num [logNatLo]]
    exact h.1
  · rw [show (↑(logNatHi 155) : ℝ) = ↑(logNatHi 5) + ↑(logNatHi 31) from by norm_num [logNatHi]]
    exact h.2

/-! ## Exported theorems -/

/-- **Two-sided rational bound on `Real.log m` for `1 ≤ m ≤ 155`.** -/
theorem logNat_bounds (m : ℕ) (h1 : 1 ≤ m) (h2 : m ≤ 155) :
    (↑(logNatLo m) : ℝ) ≤ Real.log ↑m ∧ Real.log ↑m ≤ ↑(logNatHi m) := by
  interval_cases m
  · exact M_1
  · exact M_2
  · exact M_3
  · exact M_4
  · exact M_5
  · exact M_6
  · exact M_7
  · exact M_8
  · exact M_9
  · exact M_10
  · exact M_11
  · exact M_12
  · exact M_13
  · exact M_14
  · exact M_15
  · exact M_16
  · exact M_17
  · exact M_18
  · exact M_19
  · exact M_20
  · exact M_21
  · exact M_22
  · exact M_23
  · exact M_24
  · exact M_25
  · exact M_26
  · exact M_27
  · exact M_28
  · exact M_29
  · exact M_30
  · exact M_31
  · exact M_32
  · exact M_33
  · exact M_34
  · exact M_35
  · exact M_36
  · exact M_37
  · exact M_38
  · exact M_39
  · exact M_40
  · exact M_41
  · exact M_42
  · exact M_43
  · exact M_44
  · exact M_45
  · exact M_46
  · exact M_47
  · exact M_48
  · exact M_49
  · exact M_50
  · exact M_51
  · exact M_52
  · exact M_53
  · exact M_54
  · exact M_55
  · exact M_56
  · exact M_57
  · exact M_58
  · exact M_59
  · exact M_60
  · exact M_61
  · exact M_62
  · exact M_63
  · exact M_64
  · exact M_65
  · exact M_66
  · exact M_67
  · exact M_68
  · exact M_69
  · exact M_70
  · exact M_71
  · exact M_72
  · exact M_73
  · exact M_74
  · exact M_75
  · exact M_76
  · exact M_77
  · exact M_78
  · exact M_79
  · exact M_80
  · exact M_81
  · exact M_82
  · exact M_83
  · exact M_84
  · exact M_85
  · exact M_86
  · exact M_87
  · exact M_88
  · exact M_89
  · exact M_90
  · exact M_91
  · exact M_92
  · exact M_93
  · exact M_94
  · exact M_95
  · exact M_96
  · exact M_97
  · exact M_98
  · exact M_99
  · exact M_100
  · exact M_101
  · exact M_102
  · exact M_103
  · exact M_104
  · exact M_105
  · exact M_106
  · exact M_107
  · exact M_108
  · exact M_109
  · exact M_110
  · exact M_111
  · exact M_112
  · exact M_113
  · exact M_114
  · exact M_115
  · exact M_116
  · exact M_117
  · exact M_118
  · exact M_119
  · exact M_120
  · exact M_121
  · exact M_122
  · exact M_123
  · exact M_124
  · exact M_125
  · exact M_126
  · exact M_127
  · exact M_128
  · exact M_129
  · exact M_130
  · exact M_131
  · exact M_132
  · exact M_133
  · exact M_134
  · exact M_135
  · exact M_136
  · exact M_137
  · exact M_138
  · exact M_139
  · exact M_140
  · exact M_141
  · exact M_142
  · exact M_143
  · exact M_144
  · exact M_145
  · exact M_146
  · exact M_147
  · exact M_148
  · exact M_149
  · exact M_150
  · exact M_151
  · exact M_152
  · exact M_153
  · exact M_154
  · exact M_155

/-- Lower bound: `logNatLo m ≤ Real.log m` for `1 ≤ m ≤ 155`. -/
theorem logNat_lower (m : ℕ) (h1 : 1 ≤ m) (h2 : m ≤ 155) :
    (↑(logNatLo m) : ℝ) ≤ Real.log ↑m := (logNat_bounds m h1 h2).1

/-- Upper bound: `Real.log m ≤ logNatHi m` for `1 ≤ m ≤ 155`. -/
theorem logNat_upper (m : ℕ) (h1 : 1 ≤ m) (h2 : m ≤ 155) :
    Real.log ↑m ≤ (↑(logNatHi m) : ℝ) := (logNat_bounds m h1 h2).2

end Erdos320
