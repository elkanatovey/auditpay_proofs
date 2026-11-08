#!/usr/bin/env python3
"""Numerical evaluation of the public-hash dependence bound `AuditPay.depBound`.

The Lean definition (formal/AuditPay/Dependence.lean):

    depBound Q n k s q = sum_{t=1}^{s} C(Q,t) * (depStruct n k t + depAlg n k t q)
    depStruct n k t    = C(n,t-1) * ((t-1)/n)^(k*t)
    depAlg n k t q     = sum_{u=t}^{n} C(n,u) * (u/n)^(k*t) * q^(t-1) / q^u

Q = number of addresses whose hashes the adversary has evaluated, n = vector size,
k = number of hash functions, s = cap on the size of a monitored set, q = field size.

THIS IS NOT A CERTIFIED EVALUATION. It is double-precision arithmetic on natural logarithms;
results are printed as log2 and are reliable to a few decimal places at best.

How the sums are handled
------------------------
* Outer sum over t = 1..s: every term is computed; terms are combined with log-sum-exp.
  Prefix sums give the bound for every s <= s_max in one pass.
* C(Q,t) is replaced by the upper bound Q^t / t! (for Q >= 2^64 and t <= 10^6 the relative
  difference is below 1e-7). Factorials and C(n,.) use lgamma.
* Inner sum over u = t..n (the algebraic term): consecutive terms have ratio
      C(n,u+1)/C(n,u) * ((u+1)/u)^(k*t) / q  <=  n * e^k / q  =: r0      (for u >= t),
  which is about 2^-85 for n = 10^6, k = 103, q = 2^254. The script adds terms from u = t
  until a term is 2^-80 times smaller than the largest one, and (when r0 < 1/2) accounts for
  the rest by the geometric bound  last_term * r0 / (1 - r0).  If r0 >= 1/2 it sums all terms.
* `--exact` recomputes small instances with exact rational arithmetic (Python integers) as a
  check of the floating-point code.
* `--brute` enumerates all hash tables for a few tiny parameter sets, computes Pr[Dep s]
  exactly, and compares it with depBound (a sanity check of the statement, not of the proof).

Usage:  python3 depbound.py            # the tables quoted in formal/README.md
        python3 depbound.py --exact    # also cross-check small n exactly (slower)
        python3 depbound.py --brute    # also brute-force Pr[Dep s] for tiny parameters
"""

import argparse
import itertools
import math
from fractions import Fraction

LN2 = math.log(2.0)
NEG_INF = float("-inf")


def logaddexp(a, b):
    """ln(e^a + e^b)."""
    if a == NEG_INF:
        return b
    if b == NEG_INF:
        return a
    if a < b:
        a, b = b, a
    return a + math.log1p(math.exp(b - a))


class DepBound:
    """Evaluates ln of the terms of depBound for fixed n, k, q (q given as log2)."""

    def __init__(self, n, k, log2_q):
        self.n, self.k = n, k
        self.ln_q = log2_q * LN2
        # ln(i!) for i = 0..n
        self.lf = [math.lgamma(i + 1.0) for i in range(n + 1)]
        self.ln_n = math.log(n)
        # bound on the ratio of consecutive inner terms, for u >= t
        self.ln_r0 = self.ln_n + k - self.ln_q

    def ln_choose_n(self, m):
        if m < 0 or m > self.n:
            return NEG_INF
        return self.lf[self.n] - self.lf[m] - self.lf[self.n - m]

    def ln_struct(self, t):
        """ln depStruct n k t."""
        if t - 1 > self.n:
            return NEG_INF
        if t == 1:
            return 0.0 if self.k == 0 else NEG_INF
        return self.ln_choose_n(t - 1) + self.k * t * (math.log(t - 1) - self.ln_n)

    def ln_alg_term(self, t, u):
        return (self.ln_choose_n(u) + self.k * t * (math.log(u) - self.ln_n)
                + (t - 1 - u) * self.ln_q)

    def ln_alg(self, t):
        """ln depAlg n k t q (an upper estimate: includes a geometric bound on the tail)."""
        if t > self.n:
            return NEG_INF
        geometric = self.ln_r0 < -LN2
        acc = NEG_INF
        top = NEG_INF
        u = t
        last = NEG_INF
        while u <= self.n:
            last = self.ln_alg_term(t, u)
            acc = logaddexp(acc, last)
            top = max(top, last)
            u += 1
            if geometric and last < top - 80 * LN2:
                break
        if geometric and u <= self.n:
            # remaining terms: at most last * r0 / (1 - r0)
            tail = last + self.ln_r0 - math.log1p(-math.exp(self.ln_r0))
            acc = logaddexp(acc, tail)
        return acc

    def ln_base(self, t):
        """ln( (depStruct + depAlg) / t! )."""
        return logaddexp(self.ln_struct(t), self.ln_alg(t)) - math.lgamma(t + 1.0)


def prefix_log2_bounds(db, log2_Q, s_max):
    """log2 depBound(Q, n, k, s, q) for every s = 0..s_max (C(Q,t) <= Q^t / t!)."""
    ln_Q = log2_Q * LN2
    out = [NEG_INF]
    acc = NEG_INF
    for t in range(1, s_max + 1):
        acc = logaddexp(acc, t * ln_Q + db.base[t])
        out.append(acc / LN2)
    return out


def log2_bound(db, log2_Q, s):
    """log2 depBound(Q, n, k, s, q) for one s (C(Q,t) <= Q^t / t!)."""
    ln_Q = log2_Q * LN2
    acc = NEG_INF
    for t in range(1, s + 1):
        acc = logaddexp(acc, t * ln_Q + db.base[t])
    return acc / LN2


def max_log2_Q(db, s, target=-128, hi=512):
    """Largest integer e with depBound(2^e, n, k, s, q) <= 2^target (the bound grows with Q)."""
    lo = 0
    if log2_bound(db, lo, s) > target:
        return None
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if log2_bound(db, mid, s) <= target:
            lo = mid
        else:
            hi = mid
    return lo


def exact_depbound(Q, n, k, s, q):
    """depBound as an exact rational number (small parameters only)."""
    total = Fraction(0)
    for t in range(1, s + 1):
        struct = math.comb(n, t - 1) * Fraction(t - 1, n) ** (k * t)
        alg = Fraction(0)
        for u in range(t, n + 1):
            alg += math.comb(n, u) * Fraction(u, n) ** (k * t) * Fraction(q ** (t - 1), q ** u)
        total += math.comb(Q, t) * (struct + alg)
    return total


def rank_mod(rows, q):
    """Rank of a list of vectors over GF(q), q prime."""
    rows = [list(r) for r in rows]
    rank = 0
    ncols = len(rows[0]) if rows else 0
    for c in range(ncols):
        piv = next((i for i in range(rank, len(rows)) if rows[i][c] % q), None)
        if piv is None:
            continue
        rows[rank], rows[piv] = rows[piv], rows[rank]
        inv = pow(rows[rank][c], -1, q)
        rows[rank] = [(x * inv) % q for x in rows[rank]]
        for i in range(len(rows)):
            if i != rank and rows[i][c] % q:
                f = rows[i][c]
                rows[i] = [(x - f * y) % q for x, y in zip(rows[i], rows[rank])]
        rank += 1
    return rank


def brute_prob_dep(Q, n, k, s, q):
    """Exact Pr[Dep s] over uniform position and coefficient tables (tiny parameters, q prime):
    some set of at most s of the Q addresses has linearly dependent rows."""
    subsets = [T for t in range(1, s + 1) for T in itertools.combinations(range(Q), t)]
    bad = total = 0
    for pos in itertools.product(range(n), repeat=Q * k):
        for coef in itertools.product(range(q), repeat=Q * k):
            rows = []
            for a in range(Q):
                row = [0] * n
                for i in range(k):
                    row[pos[a * k + i]] = (row[pos[a * k + i]] + coef[a * k + i]) % q
                rows.append(row)
            total += 1
            if any(rank_mod([rows[a] for a in T], q) < len(T) for T in subsets):
                bad += 1
    return Fraction(bad, total)


def log2_fraction(x):
    if x == 0:
        return NEG_INF
    num, den = x.numerator, x.denominator
    # avoid float overflow: use bit lengths
    shift_n = max(num.bit_length() - 1000, 0)
    shift_d = max(den.bit_length() - 1000, 0)
    return (math.log2(num >> shift_n) + shift_n) - (math.log2(den >> shift_d) + shift_d)


def fmt(x):
    if x == NEG_INF:
        return "       0"
    if x > 0:
        return f"  >1 (2^{x:.3g})"
    return f"{x:10.1f}"


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--exact", action="store_true", help="cross-check small n exactly")
    ap.add_argument("--brute", action="store_true", help="brute-force Pr[Dep s], tiny cases")
    args = ap.parse_args()

    log2_q = 254
    log2_Qs = [64, 80, 100]
    ks = [103, 128]

    print("log2 of depBound(Q, n, k, s, q), q = 2^254. NOT a certified evaluation.")
    print("'>1' means the bound exceeds 1 (it says nothing there).\n")

    # ---- n = 10^6 --------------------------------------------------------------------
    n = 10 ** 6
    fracs = [0.42, 0.5, 0.6, 0.75]
    print(f"n = {n}")
    print(f"{'k':>4} {'s/n':>5} " + " ".join(f"{'Q=2^' + str(e):>16}" for e in log2_Qs))
    thresholds = {}
    budgets = {}
    for k in ks:
        db = DepBound(n, k, log2_q)
        db.base = [NEG_INF] + [db.ln_base(t) for t in range(1, n + 1)]
        rows = {f: [] for f in fracs}
        for f in fracs:
            budgets[(k, f)] = max_log2_Q(db, round(f * n))
        for e in log2_Qs:
            pref = prefix_log2_bounds(db, e, n)
            for f in fracs:
                rows[f].append(pref[round(f * n)])
            # largest s with bound <= 2^-128 (the bound is monotone in s)
            s_ok = max(s for s in range(n + 1) if pref[s] <= -128)
            thresholds[(k, e)] = s_ok
        for f in fracs:
            print(f"{k:>4} {f:>5} " + " ".join(f"{fmt(v):>16}" for v in rows[f]))
    print("\nlargest s/n with depBound <= 2^-128 (n = 10^6):")
    for k in ks:
        print(f"{k:>4}       " + " ".join(
            f"{thresholds[(k, e)] / n:>16.4f}" for e in log2_Qs))
    print("\nlargest integer log2(Q) with depBound <= 2^-128 (n = 10^6):")
    print(f"{'k':>4} " + " ".join(f"{'s/n=' + str(f):>10}" for f in fracs))
    for k in ks:
        print(f"{k:>4} " + " ".join(f"{budgets[(k, f)]:>10}" for f in fracs))

    # ---- small n, s = n/2 --------------------------------------------------------------
    print("\nsmall n, s = n/2")
    print(f"{'n':>6} {'k':>4} {'s':>5} " + " ".join(f"{'Q=2^' + str(e):>16}" for e in log2_Qs))
    for n in [16, 1024]:
        s = n // 2
        for k in ks:
            db = DepBound(n, k, log2_q)
            db.base = [NEG_INF] + [db.ln_base(t) for t in range(1, s + 1)]
            vals = [prefix_log2_bounds(db, e, s)[s] for e in log2_Qs]
            print(f"{n:>6} {k:>4} {s:>5} " + " ".join(f"{fmt(v):>16}" for v in vals))

    if args.exact:
        print("\nexact rational evaluation vs floating point (log2):")
        cases = [(16, 103, 8), (16, 128, 8), (16, 3, 8), (12, 5, 12), (8, 2, 4)]
        for (n, k, s) in cases:
            db = DepBound(n, k, log2_q)
            db.base = [NEG_INF] + [db.ln_base(t) for t in range(1, s + 1)]
            for e in log2_Qs:
                # the float code uses C(Q,t) <= Q^t/t!; for Q >= 2^64 the difference is invisible
                ex = log2_fraction(exact_depbound(2 ** e, n, k, s, 2 ** log2_q))
                fl = prefix_log2_bounds(db, e, s)[s]
                print(f"  n={n:<3} k={k:<4} s={s:<3} Q=2^{e:<4} exact={ex:14.6f} float={fl:14.6f}")

    if args.brute:
        print("\nbrute force: exact Pr[Dep s] vs depBound (tiny parameters)")
        for (Q, n, k, s, q) in [(2, 2, 1, 1, 2), (3, 2, 2, 2, 2), (4, 3, 1, 4, 2), (3, 3, 2, 2, 3),
                                (2, 3, 2, 1, 5), (2, 4, 2, 2, 5), (2, 4, 2, 2, 7), (2, 5, 2, 2, 7)]:
            pr = brute_prob_dep(Q, n, k, s, q)
            bd = exact_depbound(Q, n, k, s, q)
            assert pr <= bd, (Q, n, k, s, q, pr, bd)
            print(f"  Q={Q} n={n} k={k} s={s} q={q}:  Pr[Dep s] = {float(pr):.6f}"
                  f"  <=  depBound = {float(bd):.6f}")


if __name__ == "__main__":
    main()
