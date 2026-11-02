/-
Copyright (c) 2026. Released under the Apache 2.0 license.

# Decomposition into weight × level + jump

Formalization of Section 1 of

  Rémi Eismann, *Decomposition into weight × level + jump and application to a new
  classification of primes*, arXiv:0711.0865.

For an increasing sequence of natural numbers `a : ℕ → ℕ` we define, exactly as in the paper,

* the **jump**   `d n = a (n+1) - a n`,
* `l n = a n - d n` if `a n - d n > d n`, and `l n = 0` otherwise,
* the **weight** `k n = min {k ≥ 1 | k > d n, k ∣ l n}` if `l n ≠ 0`, and `0` otherwise,
* the **level**  `L n = l n / k n` if `k n ≠ 0`, and `0` otherwise,

and we prove that `a n = k n * L n + d n` whenever `l n ≠ 0` (Lemma 1.1 gives the condition
`2 * a (n+1) < 3 * a n` for this).

We also prove the structural lemma that is the arithmetic heart of Theorem 1:
if `a n` is *classified by level* (`k n > L n`) and `d n ^ 4 ≤ l n`, then
`l n = s * q` with `q` prime and `s ≤ d n`.
-/
import Mathlib

namespace WLJ

variable (a : ℕ → ℕ)

/-- The jump (first difference, gap) `d_n = a_{n+1} - a_n`. -/
def jump (n : ℕ) : ℕ := a (n + 1) - a n

/-- `l_n = a_n - d_n` if `a_n - d_n > d_n`, and `0` otherwise. -/
def lval (n : ℕ) : ℕ := if jump a n < a n - jump a n then a n - jump a n else 0

/-- The weight `k_n = min {k ∈ ℕ* | k > d_n, k ∣ l_n}` if `l_n ≠ 0` (equivalently `d_n < l_n`),
and `0` otherwise. The minimum exists because `k = l_n` is admissible. -/
def weight (n : ℕ) : ℕ :=
  if h : jump a n < lval a n then
    Nat.find (p := fun k => jump a n < k ∧ k ∣ lval a n) ⟨lval a n, h, dvd_rfl⟩
  else 0

/-- The level `L_n = l_n / k_n` if `k_n ≠ 0`, and `0` otherwise. -/
def level (n : ℕ) : ℕ := if weight a n ≠ 0 then lval a n / weight a n else 0

/-- `a_n` is *classified by level* when `k_n > L_n`. -/
def ClassifiedByLevel (n : ℕ) : Prop := level a n < weight a n

/-- `a_n` is *classified by weight* when it is classified (`l_n ≠ 0`) and `k_n ≤ L_n`. -/
def ClassifiedByWeight (n : ℕ) : Prop := lval a n ≠ 0 ∧ weight a n ≤ level a n

instance (n : ℕ) : Decidable (ClassifiedByLevel a n) :=
  inferInstanceAs (Decidable (_ < _))

instance (n : ℕ) : Decidable (ClassifiedByWeight a n) :=
  inferInstanceAs (Decidable (_ ∧ _))

variable {a}

/-! ### Basic properties -/

theorem lval_ne_zero_iff {n : ℕ} : lval a n ≠ 0 ↔ jump a n < lval a n := by
  unfold lval; split_ifs <;> omega

theorem lval_eq_of_ne_zero {n : ℕ} (h : lval a n ≠ 0) : lval a n = a n - jump a n := by
  unfold lval at *; split_ifs at * <;> omega

/-- **Lemma 1.1** (Eismann). For an increasing sequence, the decomposition of `a_n` exists
(i.e. `l_n ≠ 0`) if and only if `a_{n+1} < (3/2) a_n`. -/
theorem lemma_1_1 {n : ℕ} (hmono : a n ≤ a (n + 1)) :
    lval a n ≠ 0 ↔ 2 * a (n + 1) < 3 * a n := by
  unfold lval jump; split_ifs <;> omega

theorem weight_spec {n : ℕ} (h : jump a n < lval a n) :
    jump a n < weight a n ∧ weight a n ∣ lval a n := by
  simp only [weight, h, ↓reduceDIte]
  exact Nat.find_spec (p := fun k => jump a n < k ∧ k ∣ lval a n) ⟨lval a n, h, dvd_rfl⟩

theorem weight_le {n e : ℕ} (h : jump a n < lval a n) (he : jump a n < e) (hdvd : e ∣ lval a n) :
    weight a n ≤ e := by
  simp only [weight, h, ↓reduceDIte]
  exact Nat.find_min' (p := fun k => jump a n < k ∧ k ∣ lval a n) _ ⟨he, hdvd⟩

theorem weight_eq_zero_iff {n : ℕ} : weight a n = 0 ↔ lval a n = 0 := by
  constructor
  · intro hw
    by_contra hl
    have := (weight_spec (lval_ne_zero_iff.mp hl)).1
    omega
  · intro hl
    simp [weight, hl]

theorem level_eq {n : ℕ} (h : lval a n ≠ 0) : level a n = lval a n / weight a n := by
  have : weight a n ≠ 0 := fun hw => h (weight_eq_zero_iff.mp hw)
  simp [level, this]

/-- **The decomposition** `a_n = k_n × L_n + d_n`, with `d_n < k_n`: in the Euclidean division of
`a_n` by its weight, the quotient is the level and the remainder is the jump. -/
theorem decomposition {n : ℕ} (h : lval a n ≠ 0) :
    a n = weight a n * level a n + jump a n ∧ jump a n < weight a n := by
  have hlt := lval_ne_zero_iff.mp h
  obtain ⟨hw, hdvd⟩ := weight_spec hlt
  refine ⟨?_, hw⟩
  rw [level_eq h, Nat.mul_div_cancel' hdvd]
  have := lval_eq_of_ne_zero h
  unfold lval at *
  split_ifs at * <;> omega

theorem lval_ne_zero_of_classifiedByLevel {n : ℕ} (h : ClassifiedByLevel a n) :
    lval a n ≠ 0 := by
  intro hl
  have := weight_eq_zero_iff.mpr hl
  unfold ClassifiedByLevel at h
  omega

/-! ### The decomposition only depends on `a n` and `a (n+1)` -/

section congr

variable {b : ℕ → ℕ} {m : ℕ}

theorem jump_congr {n : ℕ} (h0 : a n = b m) (h1 : a (n + 1) = b (m + 1)) :
    jump a n = jump b m := by
  unfold jump; rw [h0, h1]

theorem lval_congr {n : ℕ} (h0 : a n = b m) (h1 : a (n + 1) = b (m + 1)) :
    lval a n = lval b m := by
  unfold lval; rw [jump_congr h0 h1, h0]

theorem weight_congr {n : ℕ} (h0 : a n = b m) (h1 : a (n + 1) = b (m + 1)) :
    weight a n = weight b m := by
  have hj := jump_congr h0 h1
  have hl := lval_congr h0 h1
  rcases lt_or_ge (jump a n) (lval a n) with h | h
  · have h' : jump b m < lval b m := hj ▸ hl ▸ h
    obtain ⟨s1, s2⟩ := weight_spec h
    obtain ⟨s1', s2'⟩ := weight_spec h'
    exact le_antisymm (weight_le h (hj ▸ s1') (hl ▸ s2')) (weight_le h' (hj ▸ s1) (hl ▸ s2))
  · have ha : lval a n = 0 := by by_contra hc; have := lval_ne_zero_iff.mp hc; omega
    have hb : lval b m = 0 := hl ▸ ha
    rw [weight_eq_zero_iff.mpr ha, weight_eq_zero_iff.mpr hb]

theorem level_congr {n : ℕ} (h0 : a n = b m) (h1 : a (n + 1) = b (m + 1)) :
    level a n = level b m := by
  unfold level; rw [weight_congr h0 h1, lval_congr h0 h1]

theorem classifiedByLevel_congr {n : ℕ} (h0 : a n = b m) (h1 : a (n + 1) = b (m + 1)) :
    ClassifiedByLevel a n ↔ ClassifiedByLevel b m := by
  unfold ClassifiedByLevel; rw [weight_congr h0 h1, level_congr h0 h1]

end congr

/-! ### The structural lemma -/

/-- A number `m > d ≥ 1` all of whose prime factors are `≤ d` has a divisor in `(d, d²]`. -/
theorem exists_dvd_of_smooth {d : ℕ} (hd : 1 ≤ d) :
    ∀ m : ℕ, (∀ p, p.Prime → p ∣ m → p ≤ d) → d < m → ∃ e, e ∣ m ∧ d < e ∧ e ≤ d * d := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hsmooth hdm
    have hm1 : m ≠ 1 := by omega
    have hp := Nat.minFac_prime hm1
    obtain ⟨m', hm'⟩ := Nat.minFac_dvd m
    have hple : m.minFac ≤ d := hsmooth _ hp (Nat.minFac_dvd m)
    have hp2 := hp.two_le
    by_cases hm'd : d < m'
    · have hm'lt : m' < m := by
        rw [hm']
        have : 0 < m' := by omega
        nlinarith
      obtain ⟨e, he, h1, h2⟩ := ih m' hm'lt
        (fun p pp hpd => hsmooth p pp (hm' ▸ Dvd.dvd.mul_left hpd _)) hm'd
      exact ⟨e, hm' ▸ Dvd.dvd.mul_left he _, h1, h2⟩
    · refine ⟨m, dvd_rfl, hdm, ?_⟩
      rw [hm']
      exact Nat.mul_le_mul hple (by omega)

/-- If `a_n` is classified by level then `l_n` has no divisor `e` with `d_n < e ≤ √l_n`. -/
theorem no_middle_divisor {n : ℕ} (hlev : ClassifiedByLevel a n) {e : ℕ}
    (he : e ∣ lval a n) (hde : jump a n < e) (hee : e * e ≤ lval a n) : False := by
  have hl := lval_ne_zero_of_classifiedByLevel hlev
  have hlt := lval_ne_zero_iff.mp hl
  have hk : weight a n ≤ e := weight_le hlt hde he
  have hkpos : 0 < weight a n := by have := (weight_spec hlt).1; omega
  unfold ClassifiedByLevel at hlev
  rw [level_eq hl] at hlev
  have h1 : lval a n / e ≤ lval a n / weight a n := Nat.div_le_div_left hk hkpos
  have h2 : e ≤ lval a n / e := (Nat.le_div_iff_mul_le (by omega)).mpr hee
  omega

/-- **Structural lemma.** If `a_n` is classified by level, `d_n ≥ 1` and `d_n ^ 4 ≤ l_n`, then
`l_n = s * q` with `q` a prime and `s ≤ d_n`. -/
theorem lval_eq_mul_prime_of_classifiedByLevel {n : ℕ} (hlev : ClassifiedByLevel a n)
    (hd : 1 ≤ jump a n) (h4 : jump a n ^ 4 ≤ lval a n) :
    ∃ s q, q.Prime ∧ s ≤ jump a n ∧ lval a n = s * q := by
  set d := jump a n with hd_def
  set l := lval a n with hl_def
  have hl := lval_ne_zero_of_classifiedByLevel hlev
  have hlt : d < l := lval_ne_zero_iff.mp hl
  -- `l` has a prime factor `q > d`.
  obtain ⟨q, hq, hql, hdq⟩ : ∃ q, q.Prime ∧ q ∣ l ∧ d < q := by
    by_contra hcon
    push Not at hcon
    obtain ⟨e, he, hde, hed⟩ := exists_dvd_of_smooth hd l (fun p pp hpd => hcon p pp hpd) hlt
    refine no_middle_divisor hlev he hde ?_
    calc e * e ≤ (d * d) * (d * d) := Nat.mul_le_mul hed hed
      _ = d ^ 4 := by ring
      _ ≤ l := h4
  -- `q > √l`
  have hqq : l < q * q := by
    by_contra hcon
    exact no_middle_divisor hlev hql hdq (by omega)
  obtain ⟨s, hs⟩ := hql
  refine ⟨s, q, hq, ?_, show l = s * q by rw [hs, mul_comm]⟩
  by_contra hsd
  push Not at hsd
  have hsq : s < q := by
    by_contra h
    push Not at h
    have : q * q ≤ q * s := Nat.mul_le_mul_left q h
    omega
  refine no_middle_divisor hlev (show s ∣ l from ⟨q, by rw [hs, mul_comm]⟩) hsd ?_
  show s * s ≤ l
  rw [hs]
  calc s * s ≤ q * s := Nat.mul_le_mul_right s hsq.le
    _ = q * s := rfl

end WLJ
