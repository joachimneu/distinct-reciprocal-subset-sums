# Exact fixed-point certificate for the low finite input

`pilot_mod_images.cpp` certifies the low finite input of the manuscript
(Lemma `comp:low`, eq. `low-F`), which is also the Lean axiom
`lowFiniteInput` in `../Erdos320/Assumptions.lean`: the two-sided enclosure

```text
2.78724720 < F(65659969) < 2.79179560,    F(N) = (log(N)/N) log(S(N)),
```

at `N = 65659969 = floor(e^18)`. The run's certified output is the 
outward-rounded `CERT F_interval` line, `2.7872472015 < F < 2.7917955118`, 
of which the assumed interval is a strict weakening; the concluding `CERT PASS` 
line additionally places `F` in the roomier window `2.78 < F < 2.80` over which 
the companion Lean low-certificate lemmas (`../Erdos320/Lemmas/CertLow*.lean`) 
are uniform in `f`. The mathematics is the manuscript's: the
large-prime projection bracket that reduces `S(N)` to a product of exact
modular image sizes, and the substitution that turns the certified enclosures
below into the bounds on `F(N)`, are given in the proof of `comp:low` and in
the reproducibility section, and are not repeated here. This note records
what the manuscript delegates to it: the build, run, and comparison
instructions; the directed-logarithm model and its tail bound; the certified
integer bounds; and the implementation facts the manuscript does not spell
out.

## Building and running

The command

```sh
g++ -O3 -std=c++17 -Wall -Wextra -pedantic pilot_mod_images.cpp \
    -o pilot_mod_images_cert
timeout --signal=TERM --kill-after=10s 60s \
    ./pilot_mod_images_cert --self-test
timeout --signal=TERM --kill-after=10s 900s \
    ./pilot_mod_images_cert --certify-low
```

proves, without using a floating-point logarithm in any certified
comparison, the enclosure

```text
2.7872472015 < F(65659969) < 2.7917955118
```

printed as the `CERT F_interval` line, which implies the assumed interval
above.

The timeout limits are operational guards only; they do not enter a certified
inequality. The full 3,876,158-prime run takes a few minutes.

Portability note: the source is C++17 with three GCC/Clang facilities:
`unsigned __int128` for exact intermediate products, `__builtin_clzll` for
integer range reduction, and `__builtin_popcountll` for exact bit counts.
Straightforward portable replacements are possible for all three.

## Reproducing the archived transcript

`low_fixed_certificate.out` is reproduced, byte for byte, by

```sh
{
  echo "ARCHIVED LOW FINITE-INPUT CERTIFICATE TRANSCRIPT"
  ./pilot_mod_images_cert --self-test 2>&1 | grep -E '^SELFTEST'
  ./pilot_mod_images_cert --certify-low 2>/dev/null | grep -E '^(TOTAL|CERT)'
} > reproduced.out
diff reproduced.out low_fixed_certificate.out
```

The `grep`s keep exactly the deterministic record — the self-test verdict, the
complete `TOTAL` line, and every `CERT` line — and drop the output that varies
by machine: per-shell timing diagnostics, the `DIAGNOSTIC elapsed_seconds=`
line, and stderr progress. Compiler identification and executable digests are
likewise not part of the record because they vary by toolchain.

## Directed logarithms and the certified integer bounds

All set arithmetic is exact, so only the logarithms of the computed
cardinalities need enclosures. Every logarithm is represented by two integers
`lo,hi`, meaning the closed interval `[lo/10^12, hi/10^12]`. For an integer
`n`, exact power-of-two range reduction writes

```text
log(n) = k log(2) + 2 atanh((n-2^k)/(n+2^k)),    2^k <= n < 2^(k+1),
```

with atanh argument in `[0,1/3]`, and the code sums twenty terms of the atanh
series using `unsigned __int128` multiplication with directed integer
floor/ceiling after every operation. The omitted positive tail is at most

```text
2(1/3)^41 / (41(1-1/9)) = 9/(164*3^41) < 10^-12;
```

this final inequality is itself checked by exact integer arithmetic during
the run, and one extra upper lattice unit encloses the tail.

With `sigma_p(m) = |B_{p,m}|` the modular image sizes and `D_Q` the
small-prime denominator of the projection bracket (the manuscript writes
`\mathfrak D_Q`, to distinguish it from the unrelated depth normalization
`D_r(u)`; its prime exponents are found by exact repeated integer
multiplication), the run obtained

```text
10167253604100765904 / 10^12
  <= sum_{p>8206} log sigma_p(floor(N/p))
  <= 10167253604713600287 / 10^12,

16588220134055420 / 10^12  <=  log D_Q  <=  16588220135077951 / 10^12.
```

The product interval's width, about `0.000613`, includes all directed-rounding
error from the 3,876,158 prime contributions and is far smaller than the
final slack.

The same routine certifies `log N < 18`, whence `H_N <= 1 + log N < 19` and
the fiber factor obeys `H_N D_Q + 1 < 20 D_Q`. With `G_lo` the lower product
logarithm and `G_hi` the sum of the upper product logarithm, the upper
`log D_Q`, and the upper `log 20`, the exact rationals
`log_lo(N)·G_lo / (10^24·N)` and `log_hi(N)·G_hi / (10^24·N)` bound `F(N)`
from below and above. The `CERT F_interval` line prints them by exact integer
long division, rounded outward:

```text
2.7872472015 < F(N) < 2.7917955118.
```

This is the certified enclosure that implies the interval assumed by the
manuscript and by Lean. The final `CERT PASS` verdict additionally checks the
two exact rational comparisons

```text
100 log_lo(N) G_lo > 278 N (10^12)^2,
100 log_hi(N) G_hi < 280 N (10^12)^2,
```

i.e. `2.78 < F(N) < 2.80` — membership in the window over which the companion
Lean low-certificate lemmas are uniform.

## Implementation notes

Three facts about the program that the manuscript does not spell out; none
affects the represented residue sets.

- **Shells `m <= 15` are evaluated once, not per prime.** These shells hold
  the overwhelming majority of the primes, far too large for per-prime
  bitsets. Over the common denominator `lcm(1,…,m)` every subset sum is an
  integer numerator in `[0, span]`; the run certifies `span < p` for every
  prime of the shell, so reduction modulo `p` is injective and every prime in
  the shell has the same image size — the exact rational count, computed once.
- **The image set has two exact representations.** It is held as a sorted
  sparse residue list and, once it grows, as a dense cyclic bitset updated by
  rotate-and-OR; the switch is a speed heuristic only.
- **The self-test forces the sparse-to-dense switch early**, so the dense
  bitset logic — not just the sparse path — is compared against the
  independent Boolean-array reference on the test range.
