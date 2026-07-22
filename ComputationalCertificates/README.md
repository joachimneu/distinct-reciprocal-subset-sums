# `ComputationalCertificates/` — the finite computations backing the axioms

This directory is one of the repository's two code pieces (the other is the Lean
formalization in [`../Erdos320/`](../Erdos320/)). It holds the **computational
justification of the finite-input axioms** declared in
`../Erdos320/Assumptions.lean` — the parts that rest on a
finite computation or on published data.

Two of the four axioms are pure literature citations (the explicit
prime-counting estimate `fioriKadiriSwidinsky_pi_approx` and the Chebyshev bound
`dusart_theta_k3`) and are backed by their published papers, not by files here.
The other two rest on artifacts in this directory.

## Contents — which axiom and paper statement each file backs

| File | Backs (axiom / paper item) | Role |
|---|---|---|
| `pilot_mod_images.cpp` | `lowFiniteInput` — the **low finite input** (`comp:low`, Lemma 8.5): the certified `F(⌊e¹⁸⌋)` enclosure, i.e. the `C < 1.16` side of nonconstancy | C++17 program whose low-window enumeration (≈10¹³ operations, a few minutes) certifies the `F(⌊e¹⁸⌋)` enclosure the axiom assumes. Deterministic; self-test included. |
| `low_fixed_certificate.out` | `lowFiniteInput` (`comp:low`, 8.5) | The archived deterministic transcript of that run (a curated extract; see `LOW_FIXED_CERTIFICATE.md`). The axiom's interval is a strict weakening of the transcript's `CERT F_interval` line. |
| `LOW_FIXED_CERTIFICATE.md` | `lowFiniteInput` (`comp:low`, 8.5) | The certificate's documentation: what is computed, and how to rebuild, re-run, and compare. |
| `S_table_0_83.txt` | `bgmsSTable` — the published BGMS `S(0..83)` table, consumed by the **high finite input** (`comp:high`, Lemma 8.6) via the proved theorem `highFiniteInput` | The published BGMS table of `S(0..83)` (Bettin–Grenié–Molteni–Sanna, arXiv:2509.10030, Table 2). The Lean literal `bgmsTable` in `../Erdos320/Assumptions.lean` matches it value-by-value. |

Everything else the paper's argument relies on computationally (the
directed-interval certificate evaluations and the high finite input) is a
**proved theorem** inside Lean (`../Erdos320/Lemmas/Cert*.lean`,
`../Erdos320/Lemmas/HighFiniteAssembly.lean` and its cluster), so those
computations are not mirrored here — this directory holds exactly the finite
inputs that remain outside Lean's kernel.

## Integrity & provenance

The tracked files are pinned, byte for byte, by the repository's git history:
the commit hash cited in the manuscript identifies all of their content, so no
separate checksums are kept.

## Reproducing the low certificate

Follow `LOW_FIXED_CERTIFICATE.md`: build with `g++ -O3 -std=c++17`, run the
self-test, then the certify-low run, and compare the deterministic record
(the `SELFTEST`, `TOTAL`, and `CERT` lines) against `low_fixed_certificate.out`.
