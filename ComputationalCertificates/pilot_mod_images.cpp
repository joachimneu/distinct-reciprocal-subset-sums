// Exact modular-image certificate for the low numerical input.
//
// Mathematical purpose
// --------------------
// For a prime p and an integer m<p, let
//
//   B_{p,m} = { sum_{k in A} k^{-1} (mod p) : A subset {1,...,m} }.
//
// If floor(N/p)=m, the large-prime decomposition in the paper contributes
// |B_{p,m}| to an exact product that brackets S(N), the number of distinct
// reciprocal subset sums.  We normalize this count by
//
//   F(N) = (log(N)/N) log(S(N)).
//
// In certificate mode this program computes all
// such modular image sizes for
//
//   N = 65,659,969 = floor(exp(18)),  1 <= m <= 8000,
//
// and combines them with the small-prime denominator bound.  The certified
// conclusion is the outward-rounded enclosure printed as CERT F_interval,
// 2.7872472015 < F(N) < 2.7917955118, whose strict weakening
// 2.78724720 < F(N) < 2.79179560 is the interval assumed by the manuscript
// (comp:low) and by the Lean axiom lowFiniteInput.  The closing PASS line
// additionally confirms 2.78 < F(N) < 2.80, membership in the roomier window
// over which the companion Lean low-certificate lemmas are uniform.
//
// How to read this file
// ---------------------
// 1. Lines near the top implement directed fixed-point logarithms.
// 2. image_size() computes B_{p,m}, first as a sorted sparse set and then,
//    when useful, as a dense cyclic bitset.
// 3. evaluate_shell() runs that calculation for primes with floor(N/p)=m.
// 4. print_low_finite_input_certificate() turns the exact product into the stated
//    bounds for F(N).
// 5. main() selects a self-test, an exploratory run, or the fixed certificate.
//
// Only integer arithmetic and directed fixed-point logarithms enter the
// certificate.  The long-double fields are diagnostics for exploratory runs
// and are disabled by --certify-low.  Algorithmic cutoffs change performance,
// not the represented residue sets.

#include <algorithm>
#include <chrono>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <iomanip>
#include <iostream>
#include <limits>
#include <numeric>
#include <optional>
#include <stdexcept>
#include <string>
#include <vector>

using u32 = std::uint32_t;
using u64 = std::uint64_t;
using u128 = unsigned __int128;

// ---------------------------------------------------------------------------
// Part I.  Outward-rounded logarithms on the lattice 10^{-12} Z
// ---------------------------------------------------------------------------

// Directed fixed-point logarithms used by --certify-low.  kLogScale is
// deliberately modest: the final certificate has more than 10^{-3} of
// slack, whereas fewer than four million logarithms are accumulated.
// No floating-point operation contributes to a certified inequality.
static constexpr u64 kLogScale = 1000000000000ULL;
static constexpr unsigned kAtanhTermCount = 20;
static constexpr unsigned kFirstOmittedAtanhPower = 2 * kAtanhTermCount + 1;

// Hybrid subset-image implementation heuristics.  They affect only which
// exact representation is used, never the represented residue set.
static constexpr u32 kDefaultSparseDivisor = 96;
static constexpr std::size_t kMinimumSparseLimit = 64;
static constexpr int kFirstDenseFullnessCheck = 20;
static constexpr int kDenseFullnessCheckPeriod = 2;
static constexpr int kInjectiveShortcutMaxM = 15;
static constexpr u32 kSelfTestSparseDivisor = 4;
static constexpr double kMinimumTimingSeconds = 1e-12;

// The exact low finite input and the rational comparisons certified for it.
static constexpr u64 kLowFiniteInputN = 65659969ULL;
static constexpr int kLowFiniteInputMaxShell = 8000;
static constexpr u64 kLowFiniteInputPrimeCutoff =
    kLowFiniteInputN / (kLowFiniteInputMaxShell + 1);
static constexpr u64 kLogNIntegralUpperBound = 18;
static constexpr u64 kFiberUpperFactor = 20;
static constexpr u64 kComparisonDenominator = 100;
static constexpr u64 kLowerComparisonNumerator = 278;
static constexpr u64 kUpperComparisonNumerator = 280;
static constexpr unsigned kCertificateDecimalPlaces = 10;

static_assert(kLowFiniteInputPrimeCutoff == 8206,
              "the archived low finite-input cutoff changed");
static_assert(kLowFiniteInputPrimeCutoff > static_cast<u64>(kLowFiniteInputMaxShell),
              "all certified denominators must be invertible modulo p");
static_assert(kLowFiniteInputPrimeCutoff * kLowFiniteInputPrimeCutoff > kLowFiniteInputN,
              "the large-prime projection requires Q^2>N");

struct LogInterval {
    u64 lower_units;
    u64 upper_units;  // endpoints divided by kLogScale
};

struct WideLogInterval {
    u128 lower_units = 0;
    u128 upper_units = 0;
};

static u64 floor_div_u128(u128 a, u128 b) {
    return static_cast<u64>(a / b);
}

static u64 ceil_div_u128(u128 a, u128 b) {
    return static_cast<u64>(a / b + (a % b != 0));
}

static u64 mul_down(u64 a, u64 b) {
    return floor_div_u128(u128(a) * b, kLogScale);
}

static u64 mul_up(u64 a, u64 b) {
    return ceil_div_u128(u128(a) * b, kLogScale);
}

// Enclose 2 atanh(a/b), where 0 <= a/b <= 1/3.  kAtanhTermCount terms are
// accumulated with directed integer rounding.  For the configured 20 terms,
// the omitted tail is at most
//
//   2 (1/3)^41 / (41(1-1/9)) = 9/(164*3^41) < 10^{-12},
//
// so one additional lattice unit is a rigorous upper allowance.
static LogInterval twice_atanh_bounds(u64 a, u64 b) {
    if (b == 0 || a > b / 3) {
        throw std::invalid_argument("twice_atanh_bounds requires 0<=a/b<=1/3");
    }
    if (a == 0) return {0, 0};
    u64 z_lower = floor_div_u128(u128(a) * kLogScale, b);
    u64 z_upper = ceil_div_u128(u128(a) * kLogScale, b);
    u64 z_squared_lower = mul_down(z_lower, z_lower);
    u64 z_squared_upper = mul_up(z_upper, z_upper);
    u64 term_lower = z_lower, term_upper = z_upper;
    u64 sum_lower = 0, sum_upper = 0;
    for (unsigned term_index = 0; term_index < kAtanhTermCount; ++term_index) {
        u64 denominator = 2 * term_index + 1;
        sum_lower += term_lower / denominator;
        sum_upper += term_upper / denominator + (term_upper % denominator != 0);
        term_lower = mul_down(term_lower, z_squared_lower);
        term_upper = mul_up(term_upper, z_squared_upper);
    }
    return {2 * sum_lower, 2 * sum_upper + 1};
}

static LogInterval natural_log_bounds(u64 n) {
    if (n == 0 || n >= (u64(1) << 63)) {
        std::cerr << "natural_log_bounds domain error\n";
        std::exit(3);
    }
    static const LogInterval ln2 = twice_atanh_bounds(1, 3);
    unsigned k = 63U - static_cast<unsigned>(__builtin_clzll(n));
    u64 power = u64(1) << k;
    LogInterval reduced_log = twice_atanh_bounds(n - power, n + power);
    return {k * ln2.lower_units + reduced_log.lower_units,
            k * ln2.upper_units + reduced_log.upper_units};
}

static std::string u128_string(u128 x) {
    if (x == 0) return "0";
    std::string s;
    while (x) {
        s.push_back(char('0' + x % 10));
        x /= 10;
    }
    std::reverse(s.begin(), s.end());
    return s;
}

enum class DecimalRounding { Down, Up };

// Decimal display of a nonnegative rational, rounded in the requested
// direction.  This is integer long division, not a floating-point print.
static std::string rational_decimal(u128 num, u128 den, unsigned places,
                                    DecimalRounding rounding) {
    if (den == 0) throw std::invalid_argument("rational_decimal denominator is zero");
    u128 whole = num / den, rem = num % den;
    std::vector<unsigned> digit(places);
    for (unsigned i = 0; i < places; ++i) {
        rem *= 10;
        digit[i] = static_cast<unsigned>(rem / den);
        rem %= den;
    }
    if (rounding == DecimalRounding::Up && rem != 0) {
        int i = static_cast<int>(places) - 1;
        while (i >= 0 && digit[static_cast<unsigned>(i)] == 9) {
            digit[static_cast<unsigned>(i)] = 0;
            --i;
        }
        if (i >= 0) ++digit[static_cast<unsigned>(i)];
        else ++whole;
    }
    std::string ans = u128_string(whole);
    if (places) {
        ans.push_back('.');
        for (unsigned d : digit) ans.push_back(char('0' + d));
    }
    return ans;
}

static std::vector<int> primes_up_to(int n) {
    if (n < 1) return {};
    std::vector<bool> composite(static_cast<std::size_t>(n) + 1, false);
    std::vector<int> primes;
    for (int i = 2; i <= n; ++i) {
        if (!composite[static_cast<std::size_t>(i)]) primes.push_back(i);
        for (int p : primes) {
            long long v = 1LL * i * p;
            if (v > n) break;
            composite[static_cast<std::size_t>(v)] = true;
            if (i % p == 0) break;
        }
    }
    return primes;
}

// ---------------------------------------------------------------------------
// Part II.  Exact subset images in the additive group Z/pZ
// ---------------------------------------------------------------------------

// Preconditions: x,y<p and p<=INT_MAX.  The latter makes x+y fit in u32.
static inline u32 add_residues_mod_prime(u32 x, u32 y, u32 p) {
    u32 z = x + y;
    return z >= p ? z - p : z;
}

// The p meaningful bits of src are the characteristic function of a subset
// of Z/pZ.  Rotation by shift represents translation by shift.  Thus this
// routine performs the subset-sum update
//
//   dest = src union (src + shift).
//
// Every production shift is the inverse of some 1<=k<p.  Bits above p in the
// last machine word are storage padding and are masked off before returning.
static void cyclic_or_shift(const std::vector<u64>& src,
                            std::vector<u64>& dest,
                            u32 p, u32 shift) {
    const std::size_t expected_words =
        (static_cast<std::size_t>(p) + 63U) >> 6;
    if (&src == &dest || p == 0 || shift == 0 || shift >= p ||
        src.size() != expected_words) {
        throw std::invalid_argument("invalid cyclic_or_shift arguments");
    }
    const std::size_t word_count = src.size();
    dest = src;

    // Non-wrapping left shift by shift.
    std::size_t whole_words = shift >> 6;
    unsigned bit_offset = shift & 63U;
    for (std::size_t i = 0; i < word_count; ++i) {
        u64 x = src[i];
        std::size_t destination_word = i + whole_words;
        if (destination_word < word_count) {
            dest[destination_word] |= bit_offset ? (x << bit_offset) : x;
        }
        if (bit_offset && destination_word + 1 < word_count) {
            dest[destination_word + 1] |= x >> (64U - bit_offset);
        }
    }

    // Wrapped part is a right shift by p-shift.
    const u32 wrapped_right_shift = p - shift;
    whole_words = wrapped_right_shift >> 6;
    bit_offset = wrapped_right_shift & 63U;
    for (std::size_t i = whole_words; i < word_count; ++i) {
        u64 x = src[i];
        std::size_t destination_word = i - whole_words;
        if (bit_offset == 0) {
            dest[destination_word] |= x;
        } else {
            dest[destination_word] |= x >> bit_offset;
            if (destination_word > 0) {
                dest[destination_word - 1] |= x << (64U - bit_offset);
            }
        }
    }

    unsigned tail = p & 63U;
    if (tail) dest.back() &= (u64(1) << tail) - 1;
}

static std::size_t popcount_bits(const std::vector<u64>& bits) {
    std::size_t count = 0;
    for (u64 word : bits) {
        count += static_cast<std::size_t>(__builtin_popcountll(word));
    }
    return count;
}

struct ImageComputationOptions {
    u32 sparse_divisor = kDefaultSparseDivisor;
};

// For prime p and 1<=k<p, inv[k] = -(p/k) inv[p%k] (mod p).
static std::vector<u32> modular_inverses_up_to(int max_denominator, u32 prime) {
    if (max_denominator < 1 || static_cast<u32>(max_denominator) >= prime) {
        throw std::invalid_argument("modular inverses require 1<=m<p");
    }
    std::vector<u32> inverse(static_cast<std::size_t>(max_denominator) + 1);
    inverse[1] = 1;
    for (int denominator = 2; denominator <= max_denominator; ++denominator) {
        const u32 k = static_cast<u32>(denominator);
        inverse[static_cast<std::size_t>(denominator)] =
            prime - static_cast<u32>((u64(prime / k) * inverse[prime % k]) % prime);
    }
    return inverse;
}

// Cardinality of B_{p,m}, where B_{p,0}={0} and
//
//   B_{p,k}=B_{p,k-1} union (B_{p,k-1}+k^{-1}).
//
// The sparse vector and dense bitset below are exact representations of the
// same set.  The function switches representations only for speed; neither
// branch approximates the set.
static u32 image_size(int m, u32 p,
                      ImageComputationOptions options = {}) {
    if (options.sparse_divisor == 0) {
        throw std::invalid_argument("sparse_divisor must be positive");
    }
    const std::vector<u32> inverse = modular_inverses_up_to(m, p);

    std::vector<u32> residues{0};
    std::vector<u32> marks(p, 0);
    u32 epoch = 1;
    int k = 1;
    const std::size_t sparse_limit = std::max<std::size_t>(
        kMinimumSparseLimit, p / options.sparse_divisor);
    for (; k <= m && residues.size() < sparse_limit; ++k) {
        // k is an int and hence fewer than 2^31 epochs are possible: wraparound
        // of this u32 counter cannot occur under image_size's precondition.
        ++epoch;
        std::vector<u32> next;
        next.reserve(std::min<std::size_t>(p, 2 * residues.size()));
        for (u32 x : residues) {
            marks[x] = epoch;
            next.push_back(x);
        }
        for (u32 x : residues) {
            u32 y = add_residues_mod_prime(
                x, inverse[static_cast<std::size_t>(k)], p);
            if (marks[y] != epoch) {
                marks[y] = epoch;
                next.push_back(y);
            }
        }
        residues.swap(next);
        if (residues.size() == p) return p;
    }
    if (k > m) return static_cast<u32>(residues.size());

    const std::size_t word_count = (static_cast<std::size_t>(p) + 63U) >> 6;
    std::vector<u64> image_bits(word_count, 0), shifted_union(word_count, 0);
    for (u32 residue : residues) {
        image_bits[residue >> 6] |= u64(1) << (residue & 63U);
    }
    for (; k <= m; ++k) {
        cyclic_or_shift(image_bits, shifted_union, p,
                        inverse[static_cast<std::size_t>(k)]);
        image_bits.swap(shifted_union);
        // Population counts are only an early-fullness optimization.  Delaying
        // them or checking every k leaves the final exact set unchanged.
        if (k >= kFirstDenseFullnessCheck &&
            (k == m || k % kDenseFullnessCheckPeriod == 0)) {
            std::size_t cardinality = popcount_bits(image_bits);
            if (cardinality == p) return p;
        }
    }
    return static_cast<u32>(popcount_bits(image_bits));
}

// Deliberately simple implementation used only by --self-test.  It computes
// the same recurrence in a byte array and obtains inverses independently by
// Fermat's theorem, so it checks both the hybrid representation and the fast
// inverse recurrence used above.
static u32 reference_image_size(int m, u32 p) {
    if (m < 1 || static_cast<u32>(m) >= p) {
        throw std::invalid_argument("reference image requires 1<=m<p");
    }
    std::vector<unsigned char> a(p, 0), b(p, 0);
    a[0] = 1;
    for (int k = 1; k <= m; ++k) {
        // Small self-test only: Fermat inversion by repeated squaring.
        u64 base = static_cast<u32>(k), e = p - 2, acc = 1;
        while (e) {
            if (e & 1) acc = acc * base % p;
            base = base * base % p;
            e >>= 1;
        }
        u32 inverse = static_cast<u32>(acc);
        b = a;
        for (u32 x = 0; x < p; ++x) {
            if (a[x]) b[add_residues_mod_prime(x, inverse, p)] = 1;
        }
        a.swap(b);
    }
    return static_cast<u32>(std::accumulate(a.begin(), a.end(), std::size_t(0)));
}

struct RationalImageSummary {
    u32 cardinality;
    u64 numerator_span;
};

// Put 1,...,1/m over their least common denominator L.  Every subset sum then
// has an integer numerator in [0,span].  Consequently reduction modulo any
// prime p>span is injective, and the modular image has this exact cardinality.
static RationalImageSummary exact_rational_image_summary(int m) {
    if (m < 1 || m > kInjectiveShortcutMaxM) {
        throw std::invalid_argument("rational shortcut is supported for 1<=m<=15");
    }
    u64 common_denominator = 1;
    for (int k = 1; k <= m; ++k)
        common_denominator = std::lcm(common_denominator, static_cast<u64>(k));
    std::vector<u64> numerators{0};
    u64 numerator_span = 0;
    for (int k = 1; k <= m; ++k) {
        const u64 numerator_increment = common_denominator / static_cast<u64>(k);
        numerator_span += numerator_increment;
        std::vector<u64> next = numerators;
        next.reserve(2 * numerators.size());
        for (u64 numerator : numerators) {
            next.push_back(numerator + numerator_increment);
        }
        std::sort(next.begin(), next.end());
        next.erase(std::unique(next.begin(), next.end()), next.end());
        numerators.swap(next);
    }
    return {static_cast<u32>(numerators.size()), numerator_span};
}

// ---------------------------------------------------------------------------
// Part III.  Command-line modes and prime shells
// ---------------------------------------------------------------------------

static constexpr int kSelfTestFailureExitCode = 2;
static constexpr int kInputFailureExitCode = 3;
static constexpr int kCertificateParameterFailureExitCode = 4;
static constexpr int kCertificateComparisonFailureExitCode = 5;

struct ProgramOptions {
    long double x_parameter = 17.0L;
    std::vector<int> shells;
    std::optional<std::size_t> primes_per_shell_limit;
    bool report_only_nonfull_shells = false;
    bool run_self_test = false;
    bool certify_low_input = false;
};

struct PrimeShellBounds {
    int lower_exclusive;
    int upper_inclusive;
};

struct ShellStats {
    std::size_t prime_count = 0;
    std::size_t full_image_count = 0;
    u64 deficit_sum = 0;
    long double floating_log_sum = 0;
    u32 minimum_image = std::numeric_limits<u32>::max();
    u32 maximum_deficit = 0;
    bool used_injective_shortcut = false;
    double elapsed_seconds = 0;
};

struct AggregateStats {
    std::size_t prime_count = 0;
    std::size_t nonfull_image_count = 0;
    u64 deficit_sum = 0;
    long double floating_log_sum = 0;
    WideLogInterval certified_log_product;
};

static int parse_int(const std::string& text, const char* description) {
    std::size_t consumed = 0;
    int value = std::stoi(text, &consumed);
    if (consumed != text.size()) {
        throw std::invalid_argument(std::string("invalid ") + description + ": " + text);
    }
    return value;
}

static long double parse_long_double(const std::string& text,
                                     const char* description) {
    std::size_t consumed = 0;
    long double value = std::stold(text, &consumed);
    if (consumed != text.size()) {
        throw std::invalid_argument(std::string("invalid ") + description + ": " + text);
    }
    return value;
}

static ProgramOptions parse_options(int argc, char** argv) {
    ProgramOptions options;
    for (int i = 1; i < argc; ++i) {
        const std::string argument(argv[i]);
        if (argument.rfind("--X=", 0) == 0) {
            options.x_parameter = parse_long_double(argument.substr(4), "X parameter");
        } else if (argument.rfind("--limit=", 0) == 0) {
            int limit = parse_int(argument.substr(8), "prime limit");
            if (limit < 0) throw std::invalid_argument("prime limit must be nonnegative");
            options.primes_per_shell_limit = static_cast<std::size_t>(limit);
        } else if (argument.rfind("--range=", 0) == 0) {
            const std::string specification = argument.substr(8);
            const std::size_t colon = specification.find(':');
            if (colon == std::string::npos ||
                specification.find(':', colon + 1) != std::string::npos) {
                throw std::invalid_argument("range must have the form a:b");
            }
            int first_shell = parse_int(specification.substr(0, colon), "range start");
            int last_shell = parse_int(specification.substr(colon + 1), "range end");
            if (first_shell <= 0 || first_shell > last_shell ||
                last_shell == std::numeric_limits<int>::max()) {
                throw std::invalid_argument("range must satisfy 1<=a<=b<INT_MAX");
            }
            for (int shell = first_shell; shell <= last_shell; ++shell) {
                options.shells.push_back(shell);
            }
        } else if (argument == "--summary-only") {
            options.report_only_nonfull_shells = true;
        } else if (argument == "--self-test") {
            options.run_self_test = true;
        } else if (argument == "--certify-low") {
            options.certify_low_input = true;
        } else {
            if (argument.rfind("--", 0) == 0) {
                throw std::invalid_argument("unknown option: " + argument);
            }
            options.shells.push_back(parse_int(argument, "shell"));
        }
    }
    return options;
}

static long long exploratory_n(long double x_parameter) {
    const long double exponential = std::exp(x_parameter);
    if (!std::isfinite(exponential) || exponential < 1 ||
        exponential > static_cast<long double>(std::numeric_limits<long long>::max())) {
        throw std::invalid_argument("exp(X) must be a positive signed 64-bit integer");
    }
    return static_cast<long long>(std::floor(exponential));
}

static bool modular_image_self_test() {
    const int test_primes[] = {67, 71, 73, 79, 83, 89, 97, 101, 127, 193};
    for (int p : test_primes) {
        for (int m = 1; m <= std::min(35, p - 1); ++m) {
            u32 fast = image_size(
                m, static_cast<u32>(p), {kSelfTestSparseDivisor});
            u32 slow = reference_image_size(m, static_cast<u32>(p));
            if (fast != slow) {
                std::cerr << "SELFTEST FAIL p=" << p << " m=" << m
                          << " fast=" << fast << " slow=" << slow << "\n";
                return false;
            }
        }
    }
    std::cerr << "SELFTEST PASS\n";
    return true;
}

static void validate_run_inputs(long long n, const std::vector<int>& shells) {
    if (n < 1 || shells.empty()) {
        throw std::invalid_argument("N and the shell list must be nonempty and positive");
    }
    for (int m : shells) {
        if (m <= 0 || m == std::numeric_limits<int>::max()) {
            throw std::invalid_argument("every shell must satisfy 1<=m<INT_MAX");
        }
    }
    const int minimum_shell = *std::min_element(shells.begin(), shells.end());
    if (n / minimum_shell > std::numeric_limits<int>::max()) {
        throw std::invalid_argument("prime sieve bound exceeds INT_MAX");
    }
}

// A "shell" is simply the set of primes for which floor(N/p) has one fixed
// value m.  Equivalently, floor(N/p)=m exactly when N/(m+1)<p<=N/m.
static PrimeShellBounds prime_shell_bounds(long long n, int m) {
    return {static_cast<int>(n / (m + 1)), static_cast<int>(n / m)};
}

using PrimeIterator = std::vector<int>::const_iterator;

static ShellStats evaluate_shell(int m, PrimeShellBounds bounds,
                                 PrimeIterator first, PrimeIterator last,
                                 bool certify,
                                 WideLogInterval& certified_log_product) {
    // This is the computational heart of the run.  For every prime in the
    // shell it adds log |B_{p,m}| either to a diagnostic floating-point sum
    // or to the outward-rounded certificate interval.
    ShellStats stats;
    stats.prime_count = static_cast<std::size_t>(last - first);
    const auto start = std::chrono::steady_clock::now();

    if (m <= kInjectiveShortcutMaxM) {
        const RationalImageSummary rational = exact_rational_image_summary(m);
        stats.used_injective_shortcut =
            static_cast<u64>(bounds.lower_exclusive) > rational.numerator_span;
        if (stats.used_injective_shortcut) {
            stats.minimum_image = rational.cardinality;
            if (!certify) {
                stats.floating_log_sum = static_cast<long double>(stats.prime_count) *
                    std::log(static_cast<long double>(rational.cardinality));
            } else {
                const LogInterval logarithm = natural_log_bounds(rational.cardinality);
                certified_log_product.lower_units +=
                    u128(stats.prime_count) * logarithm.lower_units;
                certified_log_product.upper_units +=
                    u128(stats.prime_count) * logarithm.upper_units;
            }

            // p>lower_exclusive>span implies |B_{p,m}|<=span+1<p, so no image
            // is full.  The archived diagnostic intentionally did not compute
            // p-|B_{p,m}| on this shortcut; retain its zero deficit fields.
            stats.full_image_count = 0;
            stats.deficit_sum = 0;
        }
    }

    for (auto it = stats.used_injective_shortcut ? last : first; it != last; ++it) {
        const u32 prime = static_cast<u32>(*it);
        const u32 cardinality = image_size(m, prime);
        if (!certify) {
            stats.floating_log_sum += std::log(static_cast<long double>(cardinality));
        } else {
            const LogInterval logarithm = natural_log_bounds(cardinality);
            certified_log_product.lower_units += logarithm.lower_units;
            certified_log_product.upper_units += logarithm.upper_units;
        }
        if (cardinality == prime) ++stats.full_image_count;
        stats.deficit_sum += prime - cardinality;
        stats.minimum_image = std::min(stats.minimum_image, cardinality);
        stats.maximum_deficit = std::max(stats.maximum_deficit, prime - cardinality);
    }

    stats.elapsed_seconds = std::chrono::duration<double>(
        std::chrono::steady_clock::now() - start).count();
    return stats;
}

static void accumulate(AggregateStats& aggregate, const ShellStats& shell) {
    aggregate.prime_count += shell.prime_count;
    aggregate.nonfull_image_count += shell.prime_count - shell.full_image_count;
    aggregate.deficit_sum += shell.deficit_sum;
    aggregate.floating_log_sum += shell.floating_log_sum;
}

static void print_shell_stats(int m, const ShellStats& stats) {
    std::cout << "m=" << m << " primes=" << stats.prime_count
              << " full=" << stats.full_image_count
              << " deficit_sum=" << stats.deficit_sum
              << " max_deficit=" << stats.maximum_deficit
              << " min_image=" << stats.minimum_image
              << " logsum=" << std::setprecision(15)
              << static_cast<double>(stats.floating_log_sum)
              << " sec=" << stats.elapsed_seconds
              << " primes_per_sec="
                  << (static_cast<double>(stats.prime_count) /
                  std::max(stats.elapsed_seconds, kMinimumTimingSeconds))
              << (stats.used_injective_shortcut ? " automatic_injective=1" : "")
              << "\n";
}

static u128 integer_power(u64 base, unsigned exponent) {
    u128 result = 1;
    for (unsigned i = 0; i < exponent; ++i) result *= base;
    return result;
}

// ---------------------------------------------------------------------------
// Part IV.  Convert the modular product into the low finite input
// ---------------------------------------------------------------------------

static bool low_finite_input_parameters_are_valid(long long n) {
    const u128 power_of_three = integer_power(3, kFirstOmittedAtanhPower);
    const u128 tail_denominator =
        u128(4) * kFirstOmittedAtanhPower * power_of_three;
    const bool atanh_tail_is_below_one_unit =
        u128(9) * kLogScale < tail_denominator;
    return n == static_cast<long long>(kLowFiniteInputN) &&
           kLowFiniteInputN / (kLowFiniteInputMaxShell + 1) == kLowFiniteInputPrimeCutoff &&
           kLowFiniteInputPrimeCutoff > static_cast<u64>(kLowFiniteInputMaxShell) &&
           kLowFiniteInputPrimeCutoff * kLowFiniteInputPrimeCutoff > kLowFiniteInputN &&
           atanh_tail_is_below_one_unit;
}

// D_Q = product_{q<=Q} q^{floor(log N/log q)}.  Each exponent is found by
// overflow-safe exact multiplication; only log(D_Q) needs an enclosure.
static WideLogInterval denominator_product_log_bounds() {
    const auto small_primes = primes_up_to(static_cast<int>(kLowFiniteInputPrimeCutoff));
    WideLogInterval log_dq;
    for (int q : small_primes) {
        unsigned exponent = 0;
        u64 power = 1;
        while (power <= kLowFiniteInputN / static_cast<u64>(q)) {
            power *= static_cast<u64>(q);
            ++exponent;
        }
        const LogInterval logarithm = natural_log_bounds(static_cast<u64>(q));
        log_dq.lower_units += u128(exponent) * logarithm.lower_units;
        log_dq.upper_units += u128(exponent) * logarithm.upper_units;
    }
    return log_dq;
}

static int print_low_finite_input_certificate(
        long long n, const WideLogInterval& log_product) {
    if (!low_finite_input_parameters_are_valid(n)) {
        std::cerr << "CERT FAIL: low finite-input integer parameters\n";
        return kCertificateParameterFailureExitCode;
    }

    const WideLogInterval log_dq = denominator_product_log_bounds();
    const LogInterval log_n = natural_log_bounds(kLowFiniteInputN);
    const LogInterval log_fiber_factor = natural_log_bounds(kFiberUpperFactor);
    if (log_n.upper_units >= kLogNIntegralUpperBound * kLogScale) {
        std::cerr << "CERT FAIL: log(N)<18 not established\n";
        return kCertificateParameterFailureExitCode;
    }

    // Write sigma_p(m)=|B_{p,m}| and H_N=sum_{n<=N} 1/n.  The exact
    // projection lemma gives
    //   product sigma_p <= S(N) <= (H_N D_Q+1) product sigma_p.
    // log(N)<18 gives H_N<19; since D_Q>=1, the fibre is <20D_Q.
    const u128 lower_log_s_units = log_product.lower_units;
    const u128 upper_log_s_units =
        log_product.upper_units + log_dq.upper_units +
        log_fiber_factor.upper_units;
    const u128 scaled_f_denominator =
        u128(kLogScale) * kLogScale * kLowFiniteInputN;
    const u128 lower_f_numerator =
        u128(log_n.lower_units) * lower_log_s_units;
    const u128 upper_f_numerator =
        u128(log_n.upper_units) * upper_log_s_units;
    const bool lower_pass =
        u128(kComparisonDenominator) * lower_f_numerator >
        u128(kLowerComparisonNumerator) * scaled_f_denominator;
    const bool upper_pass =
        u128(kComparisonDenominator) * upper_f_numerator <
        u128(kUpperComparisonNumerator) * scaled_f_denominator;

    std::cout << "CERT fixed_log_scale=" << kLogScale
              << " terms=" << kAtanhTermCount << " tail_lt_one_unit=1\n";
    std::cout << "CERT log_product_units=["
              << u128_string(log_product.lower_units) << ","
              << u128_string(log_product.upper_units) << "]\n";
    std::cout << "CERT log_DQ_units=[" << u128_string(log_dq.lower_units)
              << "," << u128_string(log_dq.upper_units) << "]\n";
    std::cout << "CERT F_interval=["
              << rational_decimal(lower_f_numerator, scaled_f_denominator,
                                  kCertificateDecimalPlaces,
                                  DecimalRounding::Down)
              << ","
              << rational_decimal(upper_f_numerator, scaled_f_denominator,
                                  kCertificateDecimalPlaces,
                                  DecimalRounding::Up)
              << "]\n";
    std::cout << "CERT compare_lower_2.78=" << (lower_pass ? "PASS" : "FAIL")
              << " compare_upper_2.80=" << (upper_pass ? "PASS" : "FAIL")
              << "\n";
    if (!lower_pass || !upper_pass) {
        return kCertificateComparisonFailureExitCode;
    }
    std::cout << "CERT PASS: 2.78 < F(65659969) < 2.80\n";
    return 0;
}

// ---------------------------------------------------------------------------
// Part V.  Program modes
// ---------------------------------------------------------------------------

int main(int argc, char** argv) {
    try {
        ProgramOptions options = parse_options(argc, argv);

        // Certificate mode takes N from an exact integer constant.  The libm
        // expression remains available only for exploratory runs.
        const long long n = options.certify_low_input
            ? static_cast<long long>(kLowFiniteInputN)
            : exploratory_n(options.x_parameter);

        if (options.run_self_test) {
            if (!modular_image_self_test()) return kSelfTestFailureExitCode;
            if (options.shells.empty() && !options.certify_low_input) return 0;
        }

        if (options.certify_low_input) {
            // The certified path fixes every parameter.  User-selected shell
            // ranges and prime limits are rejected so that a partial run can
            // never be mistaken for the archived certificate.
            if (!options.shells.empty() || options.primes_per_shell_limit) {
                std::cerr << "--certify-low does not accept a range or limit\n";
                return kInputFailureExitCode;
            }
            options.shells.reserve(kLowFiniteInputMaxShell);
            for (int m = 1; m <= kLowFiniteInputMaxShell; ++m) {
                options.shells.push_back(m);
            }
            options.report_only_nonfull_shells = true;
        } else if (options.shells.empty()) {
            options.shells = {10, 20, 30, 50, 100, 154};
        }

        validate_run_inputs(n, options.shells);
        const int minimum_shell =
            *std::min_element(options.shells.begin(), options.shells.end());
        const int maximum_prime = static_cast<int>(n / minimum_shell);
        const auto primes = primes_up_to(maximum_prime);
        std::cerr << "N=" << n << " primes<=pmax=" << primes.size() << "\n";

        AggregateStats aggregate;
        const auto run_start = std::chrono::steady_clock::now();
        for (int m : options.shells) {
            const PrimeShellBounds bounds = prime_shell_bounds(n, m);
            auto first = std::upper_bound(primes.cbegin(), primes.cend(),
                                          bounds.lower_exclusive);
            auto last = std::upper_bound(primes.cbegin(), primes.cend(),
                                         bounds.upper_inclusive);
            if (options.primes_per_shell_limit) {
                const std::size_t available = static_cast<std::size_t>(last - first);
                if (available > *options.primes_per_shell_limit) {
                    last = first + static_cast<std::ptrdiff_t>(
                        *options.primes_per_shell_limit);
                }
            }
            if (first != last && *first <= m) {
                throw std::invalid_argument(
                    "selected shell contains a prime p<=m; reciprocal inverses do not exist");
            }

            const ShellStats shell = evaluate_shell(
                m, bounds, first, last, options.certify_low_input,
                aggregate.certified_log_product);
            accumulate(aggregate, shell);
            if (!options.report_only_nonfull_shells ||
                shell.full_image_count != shell.prime_count) {
                print_shell_stats(m, shell);
            }
        }

        const double elapsed_seconds = std::chrono::duration<double>(
            std::chrono::steady_clock::now() - run_start).count();
        std::cout << "TOTAL shells=" << options.shells.size()
                  << " primes=" << aggregate.prime_count
                  << " nonfull=" << aggregate.nonfull_image_count
                  << " deficit_sum=" << aggregate.deficit_sum;
        if (!options.certify_low_input) {
            std::cout << " logsum=" << std::setprecision(15)
                      << static_cast<double>(aggregate.floating_log_sum);
        } else {
            std::cout << " libm_logsum=disabled";
        }
        // Keep the TOTAL audit record deterministic.  Timing is useful when
        // profiling the several-minute run, but it is not certified data and
        // varies across machines and compiler builds.
        std::cout << "\n";
        std::cout << "DIAGNOSTIC elapsed_seconds=" << elapsed_seconds << "\n";

        if (options.certify_low_input) {
            return print_low_finite_input_certificate(
                n, aggregate.certified_log_product);
        }
        return 0;
    } catch (const std::exception& error) {
        std::cerr << "argument error: " << error.what() << "\n";
        return kInputFailureExitCode;
    }
}
