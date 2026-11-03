/-
# The decomposition applied to the sequence of primes

`P n = Nat.nth Nat.Prime n` is the `n`-th prime, **counted from 0** (`P 0 = 2`, `P 1 = 3`, …).
So the paper's `p_n` is our `P (n - 1)`; this shift is irrelevant for density statements.
-/
import Conjecture9.Decomposition

namespace WLJ

open Nat

/-- The sequence of primes, `P 0 = 2, P 1 = 3, P 2 = 5, …`. -/
noncomputable abbrev P (n : ℕ) : ℕ := Nat.nth Nat.Prime n

theorem P_prime (n : ℕ) : (P n).Prime := Nat.prime_nth_prime n

theorem P_strictMono : StrictMono P := Nat.nth_strictMono Nat.infinite_setOfPred_prime

theorem P_lt_succ (n : ℕ) : P n < P (n + 1) := P_strictMono (Nat.lt_succ_self n)

theorem jump_P_pos (n : ℕ) : 1 ≤ jump P n := by
  unfold jump; have := P_lt_succ n; omega

theorem P_succ_eq (n : ℕ) : P (n + 1) = P n + jump P n := by
  unfold jump; have := P_lt_succ n; omega

/-- The paper's identity `p_n = l_n + g_n` (when the decomposition exists). -/
theorem P_eq_lval_add_jump {n : ℕ} (h : lval P n ≠ 0) : P n = lval P n + jump P n := by
  have := lval_eq_of_ne_zero h
  unfold lval at *
  split_ifs at * <;> omega

/-- Sum of the gaps telescopes: `∑_{n < N} g_n = P N - 2`. -/
theorem sum_jump_P (N : ℕ) : ∑ n ∈ Finset.range N, jump P n = P N - P 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 := P_lt_succ N
    have h2 : P 0 ≤ P N := P_strictMono.monotone (Nat.zero_le N)
    unfold jump; omega

/-- Exactly `N` primes are smaller than `P N`. -/
theorem primeCounting'_P (N : ℕ) : Nat.primeCounting' (P N) = N := Nat.primeCounting'_nth_eq N

end WLJ
