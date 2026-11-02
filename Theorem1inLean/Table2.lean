/-
# Sanity check against Table 2 of the paper

We evaluate the (computable) definitions of `Decomposition.lean` on the list of the first 18
primes and check, by `decide` (i.e. inside the Lean kernel), that we recover exactly the
weights, levels, jumps and `l_n` of Table 2 of arXiv:0711.0865 (paper index `n` = our `n - 1`).
-/
import Theorem1inLean.Primes

namespace WLJ.Table2

/-- The first 18 primes. -/
def firstPrimes : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61]

theorem firstPrimes_prime : ∀ p ∈ firstPrimes, p.Prime := by decide

def a (n : ℕ) : ℕ := firstPrimes.getD n 0

/-- Weights `k_n` (OEIS A117078). -/
example : (List.range 17).map (weight a) = [0, 0, 3, 0, 3, 9, 3, 5, 17, 3, 25, 11, 3, 13, 41, 47, 3] := by
  decide +kernel

/-- Levels `L_n` (OEIS A117563). -/
example : (List.range 17).map (level a) = [0, 0, 1, 0, 3, 1, 5, 3, 1, 9, 1, 3, 13, 3, 1, 1, 19] := by
  decide +kernel

/-- Jumps `g_n` (OEIS A001223). -/
example : (List.range 17).map (jump a) = [1, 2, 2, 4, 2, 4, 2, 4, 6, 2, 6, 4, 2, 4, 6, 6, 2] := by
  decide +kernel

/-- `l_n` (OEIS A118534). -/
example : (List.range 17).map (lval a) = [0, 0, 3, 0, 9, 9, 15, 15, 17, 27, 25, 33, 39, 39, 41, 47, 57] := by
  decide +kernel

/-- Which of the first primes are classified by level (`k_n > L_n`):
5, 13, 19, 23, 31, 37, 43, 47, 53 (our indices 2, 5, 7, 8, 10, 11, 13, 14, 15). -/
example : (List.range 17).filter (fun n => decide (ClassifiedByLevel a n)) = [2, 5, 7, 8, 10, 11, 13, 14, 15] := by
  decide +kernel

/-! ### The table really is about the primes `P n = Nat.nth Nat.Prime n` -/

/-- The list `firstPrimes` consists of the first 18 primes: `P n = a n` for `n < 18`. -/
theorem P_eq_a : ∀ n < 18, P n = a n := by
  have key : ∀ p ∈ firstPrimes, P (Nat.count Nat.Prime p) = p := fun p hp =>
    Nat.nth_count (firstPrimes_prime p hp)
  have hc : (List.range 18).map (fun n => Nat.count Nat.Prime (a n)) = List.range 18 := by
    decide +kernel
  intro n hn
  have hmem : a n ∈ firstPrimes := by
    unfold a; interval_cases n <;> decide
  have hcn : Nat.count Nat.Prime (a n) = n := by
    have := congrArg (fun l => l.getD n 0) hc
    simpa [List.getD_eq_getElem?_getD, hn] using this
  rw [← key _ hmem, hcn]

/-- Among the first 17 primes (`n < 17`), `P n` is classified by level exactly for
`P n ∈ {5, 13, 19, 23, 31, 37, 43, 47, 53}`. -/
theorem classifiedByLevel_P_small :
    ∀ n < 17, (ClassifiedByLevel P n ↔ n ∈ [2, 5, 7, 8, 10, 11, 13, 14, 15]) := by
  intro n hn
  rw [classifiedByLevel_congr (P_eq_a n (by omega)) (P_eq_a (n + 1) (by omega))]
  revert n
  decide +kernel

end WLJ.Table2
