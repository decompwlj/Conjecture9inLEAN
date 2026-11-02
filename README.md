# Theorem 1 in Lean

A Lean 4 / Mathlib formalization of **Theorem 1** (stated as Conjecture 9 in the paper below).

> **Theorem 1.** The prime numbers classified by level are rarefying among the primes.

The decomposition comes from Rémi Eismann, *Decomposition into weight × level + jump and application
to a new classification of primes*, [arXiv:0711.0865](https://arxiv.org/abs/0711.0865), and the
[OEIS wiki](https://oeis.org/wiki/Decomposition_into_weight_*_level_%2B_jump).

## What is proved

| Result | Lean name | Status |
|---|---|---|
| Definitions of jump `d_n`, `l_n`, weight `k_n`, level `L_n`, "classified by level" | `WLJ.jump`, `WLJ.lval`, `WLJ.weight`, `WLJ.level`, `WLJ.ClassifiedByLevel` | ✅ |
| Lemma 1.1: the decomposition exists iff `a_{n+1} < (3/2) a_n` | `WLJ.lemma_1_1` | ✅ proved |
| `a_n = k_n × L_n + d_n` with `d_n < k_n` (Euclidean division) | `WLJ.decomposition` | ✅ proved |
| Table 2 of the paper (first 17 primes) is reproduced | `WLJ.Table2.*` | ✅ checked by the kernel |
| **Structural lemma**: if `p_n` is classified by level and `g_n⁴ ≤ l_n`, then `l_n = s·q` with `q` prime and `s ≤ g_n` | `WLJ.lval_eq_mul_prime_of_classifiedByLevel` | ✅ proved |
| Counting bound (below) | `WLJ.levelCount_le` | ✅ proved |
| **Theorem 1**, assuming a classical sieve bound for prime triples | `WLJ.theorem1_of_sieve : TripleSieveBound → Theorem1` | ✅ proved |
| The sieve bound `TripleSieveBound` itself | — | ⏳ not in Mathlib yet (see below) |

There is no `sorry` and no new axiom anywhere. The proofs use only Lean's three standard axioms
(`propext`, `Classical.choice`, `Quot.sound`).

### The precise statement

The primes are `P n = Nat.nth Nat.Prime n`, counted from 0 (`P 0 = 2`), so the paper's `p_n` is our
`P (n-1)`. "Rarefying" is formalized as *density zero among the primes*:

```lean
def Theorem1 : Prop :=
  Tendsto (fun N : ℕ => (#{n < N | P n is classified by level} : ℝ) / N) atTop (𝓝 0)
```

### The one hypothesis: `TripleSieveBound`

```lean
def TripleSieveBound : Prop :=
  ∃ C : ℝ, ∀ g s : ℕ, 1 ≤ g → 1 ≤ s → ∀ X : ℝ, 16 ≤ X →
    #{q ≤ X | q, s q + g, s q + 2 g all prime}
      ≤ C * X * log (g s + 2)^3 * (log log X)^3 / (log X)^3
```

This is a standard upper-bound sieve estimate for three linear forms. Brun's pure sieve gives it,
and Selberg's sieve gives it even without the `(log log X)³` factor (see Halberstam & Richert,
*Sieve Methods*). Mathlib has the Chebyshev bounds and the basic setup of the Selberg sieve, but not
this final estimate. Formalizing it would make Theorem 1 unconditional, and it is the natural next
step.

## The proof (human-readable)

Write `g = g_n` (the jump), `l = l_n = p_n − g`, `k = k_n` (the weight) and `L = l/k` (the level).

1. **No divisor in the middle.** Suppose `p_n` is classified by level (`k > L`) and `e | l` with
   `g < e ≤ √l`. Then `k ≤ e`, because `k` is the least such divisor. So `L = l/k ≥ l/e ≥ e ≥ k`,
   which is a contradiction.
2. **Structure.** Assume moreover `g⁴ ≤ l`. If every prime factor of `l` were `≤ g`, then `l` would
   have a divisor in `(g, g²] ⊆ (g, √l]`, which step 1 rules out. So `l` has a prime factor `q > g`.
   Then `q > √l` by step 1, and `s = l/q < √l`. By step 1 again, `s ≤ g`. Hence `l = s·q` with
   `q` prime and `s ≤ g`. As a result, `p_n = s q + g` and `p_{n+1} = s q + 2g` are both prime.
3. **Counting.** Let `x = p_N` and let `G ≥ 1`. Every `n < N` with `p_n` classified by level falls
   in one of three groups:
   * `g_n > G`. There are at most `x/(G+1)` such `n`, since the gaps add up to less than `x`.
   * `p_n ≤ G⁴ + G`. There are at most `G⁴ + G + 1` such `n`.
   * Otherwise. Step 2 applies, so `n` gives a triple `(g, s, q)` with `s ≤ g ≤ G`, `q ≤ x/s`,
     and `q`, `sq+g`, `sq+2g` all prime.

   This gives `WLJ.levelCount_le`.
4. **Estimates.** The sieve bound turns the double sum into
   `≪ x · G (1 + log G) · log(G²+2)³ (log log x)³ / (log x)³`; the factor `1 + log G` comes from
   `∑ 1/s ≤ 1 + log G`. Take `G = ⌊(log x)^{3/2}⌋`. Chebyshev's bound
   `N ≥ x / (2 log x)` (`Chebyshev.pi_ge` in Mathlib) then gives

   `#{n < N | level}/N ≤ 2/√(log x) + 6 (log x)⁷/x + 3072 C (log log x)⁷/√(log x) → 0`.

The paper's data fits this: 17.11 % of the primes below `p_{5·10⁷}` are classified by level, and
the heuristic proportion `≈ log log x / log x` goes to 0 very slowly.

## How to verify the proof

### Option 1: on GitHub (no installation)

Each push runs the workflow in `.github/workflows/lean.yml`. To check it:

1. Open the **Actions** tab of the repository.
2. Open the latest **Verify Lean proof** run. A green ✓ means Lean accepted every proof.
3. Open the "Build and check the proof" step. At the end it prints the statements and lines like
   ```
   'WLJ.theorem1_of_sieve' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```
   The run fails if any proof uses `sorry` or if a new axiom was added.

To re-run it yourself: **Actions → Verify Lean proof → Run workflow**.

### Option 2: on your computer

Install `elan`, the Lean version manager:

```bash
curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y
```

Then run the verification script from the repository root:

```bash
./scripts/verify.sh
```

The script downloads a pre-compiled Mathlib (a few minutes), checks every file, and prints the
axioms used. It ends with `OK: ...` if everything is correct.

### What to read to trust the result

Lean checks every proof. You only need to check that the *definitions and statements* say what you
mean. They are short and printed by `Verify.lean`:

* `Theorem1inLean/Decomposition.lean`: `jump`, `lval`, `weight`, `level`, `ClassifiedByLevel`.
* `Theorem1inLean/Counting.lean`: `levelCount`, `tripleSet`.
* `Theorem1inLean/Theorem1.lean`: `Theorem1`, `TripleSieveBound`, `theorem1_of_sieve`.

## Files

```
Theorem1inLean/Decomposition.lean  definitions, Lemma 1.1, decomposition, structural lemma
Theorem1inLean/Primes.lean         the sequence of primes P n and its basic properties
Theorem1inLean/Table2.lean         kernel check of Table 2 of the paper
Theorem1inLean/Counting.lean       the combinatorial counting bound
Theorem1inLean/Theorem1.lean       statement of Theorem 1 and its proof from the sieve bound
Verify.lean                        prints statements and axioms
scripts/verify.sh                  one-command verification
```
