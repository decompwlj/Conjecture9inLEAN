/-
# Existence and uniqueness of the decomposition `a_n = k_n × L_n + d_n`

Let `d = d_n` be the jump. A *decomposition* of `a_n` is a pair `(k, L)` with

  `a_n = k * L + d`,   `d < k`,   `1 ≤ L`

(so that `d` is the remainder and `L` the quotient of the Euclidean division of `a_n` by `k`).

* `exists_decomposition_iff`: a decomposition exists iff `l_n ≠ 0`, i.e. (Lemma 1.1)
  iff `a_{n+1} < (3/2) a_n`.
* `admissible_iff`: `k` is admissible (`d < k` and `a_n = k * L + d` for some `L`) iff
  `d < k` and `k ∣ l_n`; then `L = l_n / k` is forced.
* `decomposition_unique`: the weight is the *least* admissible `k`, and the pair
  `(k_n, L_n)` is the **unique** decomposition with `k` minimal.
* `div_weight_eq_level`, `mod_weight_eq_jump`: in the Euclidean division of `a_n` by its weight,
  the quotient is the level and the remainder is the jump.
* `isLeast_weight`: `k_n = min {k | k > d_n, a_n mod k = d_n}`.
-/
import Theorem1inLean.Decomposition

namespace WLJ

variable {a : ℕ → ℕ} {n : ℕ}

theorem eq_lval_add_jump (h : lval a n ≠ 0) : a n = lval a n + jump a n := by
  have := lval_eq_of_ne_zero h
  unfold lval at *
  split_ifs at * <;> omega

/-- `k > d` is admissible iff `k ∣ l_n`. -/
theorem admissible_iff (h : lval a n ≠ 0) {k : ℕ} :
    (jump a n < k ∧ ∃ L, a n = k * L + jump a n) ↔ (jump a n < k ∧ k ∣ lval a n) := by
  have hal := eq_lval_add_jump h
  constructor
  · rintro ⟨hk, L, hL⟩
    exact ⟨hk, ⟨L, by omega⟩⟩
  · rintro ⟨hk, L, hL⟩
    exact ⟨hk, L, by omega⟩

/-- For an admissible `k`, the quotient `L` is forced: `L = l_n / k`. -/
theorem quotient_unique {k L L' : ℕ} (hk : 0 < k) (hL : a n = k * L + jump a n)
    (hL' : a n = k * L' + jump a n) : L = L' := by
  have : k * L = k * L' := by omega
  exact Nat.eq_of_mul_eq_mul_left hk this

/-- **Existence.** A decomposition `a_n = k * L + d_n` with `d_n < k` and `L ≥ 1` exists
if and only if `l_n ≠ 0`. -/
theorem exists_decomposition_iff :
    (∃ k L, a n = k * L + jump a n ∧ jump a n < k ∧ 1 ≤ L) ↔ lval a n ≠ 0 := by
  constructor
  · rintro ⟨k, L, hL, hk, hL1⟩
    have hkL : k ≤ k * L := Nat.le_mul_of_pos_right k hL1
    unfold lval
    rw [ite_eq_left_iff.mpr (fun h => absurd (by omega) h)]
    omega
  · intro h
    obtain ⟨hdec, hlt⟩ := decomposition h
    refine ⟨weight a n, level a n, hdec, hlt, ?_⟩
    have hspec := weight_spec (lval_ne_zero_iff.mp h)
    rw [level_eq h]
    exact Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero h) hspec.2) (by omega)

/-- **Uniqueness.** When the decomposition exists, `(k_n, L_n)` is the unique pair `(k, L)` such
that `a_n = k * L + d_n`, `d_n < k`, and `k` is minimal with this property. -/
theorem decomposition_unique (h : lval a n ≠ 0) {k L : ℕ} :
    (a n = k * L + jump a n ∧ jump a n < k ∧
        ∀ k' L', jump a n < k' → a n = k' * L' + jump a n → k ≤ k') ↔
      (k = weight a n ∧ L = level a n) := by
  have hlt := lval_ne_zero_iff.mp h
  obtain ⟨hdec, hwlt⟩ := decomposition h
  constructor
  · rintro ⟨hL, hk, hmin⟩
    have hdvd : k ∣ lval a n := ((admissible_iff h).mp ⟨hk, L, hL⟩).2
    have h1 : weight a n ≤ k := weight_le hlt hk hdvd
    have h2 : k ≤ weight a n := hmin _ _ hwlt hdec
    have hkw : k = weight a n := le_antisymm h2 h1
    refine ⟨hkw, ?_⟩
    subst hkw
    exact quotient_unique (by omega) hL hdec
  · rintro ⟨rfl, rfl⟩
    refine ⟨hdec, hwlt, fun k' L' hk' hL' => ?_⟩
    exact weight_le hlt hk' ((admissible_iff h).mp ⟨hk', L', hL'⟩).2

/-- The jump is the remainder of the Euclidean division of `a_n` by its weight. -/
theorem mod_weight_eq_jump (h : lval a n ≠ 0) : a n % weight a n = jump a n := by
  obtain ⟨hdec, hwlt⟩ := decomposition h
  rw [hdec, add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hwlt]

/-- The level is the quotient of the Euclidean division of `a_n` by its weight. -/
theorem div_weight_eq_level (h : lval a n ≠ 0) : a n / weight a n = level a n := by
  obtain ⟨hdec, hwlt⟩ := decomposition h
  rw [hdec, add_comm, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hwlt, zero_add]

/-- The weight is the least `k > d_n` such that `a_n mod k = d_n`. -/
theorem isLeast_weight (h : lval a n ≠ 0) :
    IsLeast {k | jump a n < k ∧ a n % k = jump a n} (weight a n) := by
  have hlt := lval_ne_zero_iff.mp h
  refine ⟨⟨(decomposition h).2, mod_weight_eq_jump h⟩, ?_⟩
  rintro k ⟨hk, hmod⟩
  apply weight_le hlt hk
  have hal := eq_lval_add_jump h
  have hdm := Nat.div_add_mod (a n) k
  rw [hmod] at hdm
  exact ⟨a n / k, by linarith⟩

end WLJ
