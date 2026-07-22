import Erdos320.Defs.Basic
import Erdos320.Defs.PrimeCounting

/-!
# Assumptions — the trust boundary of the formalization

Everything the formalization assumes rather than proves, and nothing else:
four axioms, each an external literature input or a computer-assisted finite
certificate. Each gets a section below stating it, noting where the manuscript
uses it, and giving its source. Labels like `comp:low` are the `\label{…}`
names in the TeX source; certificate programs are repo-tracked under
`ComputationalCertificates/`.

* `lowFiniteInput` — the certified `F(⌊e¹⁸⌋)` enclosure (`comp:low`);
* `fioriKadiriSwidinsky_pi_approx` — the explicit prime-counting estimate (`FKS-pi`);
* `dusart_theta_k3` — Dusart's explicit Chebyshev `ϑ` bound (Thm 4.2, `k = 3`);
* `bgmsSTable` — the BGMS exact values `S(0),…,S(83)`.

Not axioms — proved in `Erdos320/Lemmas/`, do not re-axiomatize: the high
finite input `F(⌊e⁶⁵⌋) > 3.2411` (`comp:high`, `highFiniteInput`) and the six
directed-interval certificate lemmas.
-/

namespace Erdos320

/-! ## `lowFiniteInput` — the low finite input `2.78724720 < F(⌊e¹⁸⌋) < 2.79179560`

The certified two-sided enclosure of `F` at `N₀ = 65 659 969 = ⌊e¹⁸⌋`
(`comp:low`, eq. `low-F`); in §8 it gives the upper chord bound `C < 1.16` on
the hypothetical constant phase. Computer-assisted — its ~10¹³-operation
enumeration is not feasibly reproducible in Lean — hence an axiom rather than a
proved theorem.
-/
axiom lowFiniteInput :
    (2.78724720 : ℝ) < F 65659969 ∧ F 65659969 < 2.79179560

/-! Source: the certificate program `pilot_mod_images.cpp` (mode
`--certify-low`), transcript `low_fixed_certificate.out`, repo-tracked in
`ComputationalCertificates/`.
-/

/-! ## `fioriKadiriSwidinsky_pi_approx` — `|π(t) − Li(t)| ≤ 9.2211·t·√(log t)·exp(−0.8476·√(log t))` for `t ≥ 2`

An explicit prime-counting estimate (eq. `FKS-pi`, §4), used throughout the
averaging-relation and shell-count bounds. Mathlib has no explicit-error prime
number theorem of this `e^{−c√log t}` strength.
-/
axiom fioriKadiriSwidinsky_pi_approx (t : ℝ) (ht : 2 ≤ t) :
    |(primePi t : ℝ) - Li t| ≤
      9.2211 * t * Real.sqrt (Real.log t) *
        Real.exp (-0.8476 * Real.sqrt (Real.log t))

/-! Source: A. Fiori, H. Kadiri, J. Swidinsky, *Sharper bounds for the error
term in the Prime Number Theorem*, Research in Number Theory 9 (2023), no. 3,
Paper No. 63 (arXiv:2206.12557; `\cite{FioriKadiriSwidinsky}`), Corollary 22.
-/

/-! ## `dusart_theta_k3` — `|ϑ(t) − t| ≤ t/(log t)³` for `t ≥ 89 967 803`

Dusart's explicit Chebyshev `ϑ` bound (eq. `theta-explicit`, §8), supplying the
prime counts in the `comp:high` argument. The weaker form the proof consumes
is the proved theorem `dusart_theta_approx`, so only this `k = 3` bound is
assumed. Not available in Mathlib.
-/
axiom dusart_theta_k3 (t : ℝ) (ht : (89967803 : ℝ) ≤ t) :
    |chebyshevTheta t - t| ≤ t / (Real.log t) ^ 3

/-! Source: P. Dusart, *Explicit estimates of some functions over primes*, The
Ramanujan Journal 45 (2018), 227–251, DOI 10.1007/s11139-016-9839-4
(`\cite{Dusart}`), Theorem 4.2, the `k = 3` row.
-/

/-! ## `bgmsSTable` — `S m = bgmsTable.getD m 0` for `m ≤ 83`

The exact counts `S m = |𝓔_m|` for `m ≤ 83`, the base of the `comp:high` lower
bounds. The table literal `bgmsTable` it references is given first.
-/

/-- The exact values `S(0), …, S(83)` computed by Bettin–Grenié–Molteni–Sanna
(BGMS Table 2). `bgmsTable[m]` is their value of `|𝓔_m| = S m`. -/
def bgmsTable : List ℕ :=
  [1, 2, 4, 8, 16, 32, 52, 104, 208, 416, 832, 1664, 1856, 3712, 7424, 9664,
   19328, 38656, 59264, 118528, 126976, 224128, 448256, 896512, 936832,
   1873664, 3747328, 7494656, 7771136, 15542272, 15886336, 31772672, 63545344,
   112064512, 224129024, 231010304, 237031424, 474062848, 948125696,
   1896251392, 1928593408, 3857186816, 3925999616, 7851999232, 12445024256,
   12606504960, 25213009920, 50426019840, 51334348800, 102668697600,
   205337395200, 410674790400, 570733363200, 1141466726400, 1721081528320,
   1751601381376, 1767017021440, 3534034042880, 7068068085760, 14136136171520,
   14245758500864, 28491517001728, 56983034003456, 57494604873728,
   114989209747456, 137824242237440, 139033409748992, 278066819497984,
   522131016253440, 1044262032506880, 1051387483914240, 2102774967828480,
   2116809947873280, 4233619895746560, 8467239791493120, 10638462277386240,
   17372520791408640, 17522758873251840, 17647454272880640, 35294908545761280,
   35499851152097280, 70999702304194560, 141999404608389120,
   283998809216778240]

axiom bgmsSTable (m : ℕ) (hm : m ≤ 83) : S m = bgmsTable.getD m 0

/-! Source: S. Bettin, L. Grenié, G. Molteni, C. Sanna, *A lower bound for the
number of Egyptian fractions*, Mathematics of Computation (2026), DOI
10.1090/mcom/4190 (arXiv:2509.10030); `\cite{BGMS}`, Table 2.
-/

end Erdos320
