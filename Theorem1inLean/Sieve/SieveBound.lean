/-
# Proof of `TripleSieveBound`

We combine Brun's sieve (`Brun.lean`) with the prime estimates (`PrimeSums.lean`) and choose

  k = ⌈(a + 3)(3 + log log X)⌉,  z = ⌊exp(log X / (4k))⌋,   where a = 3 e cM,

to obtain, for all `g, s ≥ 1` and `X ≥ 16`,

  #{q ≤ X | q, sq+g, sq+2g prime} ≤ C · X · log(gs+2)³ · (log log X)³ / (log X)³.
-/
import Theorem1inLean.Theorem1
import Theorem1inLean.Sieve.Brun
import Theorem1inLean.Sieve.PrimeSums

namespace WLJ.Sieve

open Finset Real Filter Asymptotics

/-! ### Bounds for the sieving primes -/

theorem natLog_mul_log_two_le {n : ℕ} (hn : n ≠ 0) : (Nat.log 2 n : ℝ) * log 2 ≤ log n := by
  have h : ((2 ^ Nat.log 2 n : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.pow_log_le_self 2 hn
  push_cast at h
  rw [← Real.log_pow]
  exact Real.log_le_log (by positivity) h

theorem one_le_log_three : 1 ≤ log 3 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have := Real.exp_one_lt_d9
  linarith

theorem local_factor_le {g s : ℕ} (hg : 1 ≤ g) (hs : 1 ≤ s) :
    ∏ p ∈ (2 * g * s).primeFactors, (1 - 1 / (p : ℝ))⁻¹ ≤ 4 * exp 1 * log (g * s + 2) := by
  have hm : 2 * g * s ≠ 0 := by positivity
  refine (prod_primeFactors_inv_le hm).trans ?_
  have hgs : (1 : ℝ) ≤ g * s := by
    have : (1 : ℝ) ≤ g := by exact_mod_cast hg
    have : (1 : ℝ) ≤ s := by exact_mod_cast hs
    nlinarith
  have hlg : 1 ≤ log ((g : ℝ) * s + 2) :=
    one_le_log_three.trans (Real.log_le_log (by norm_num) (by linarith))
  have hnl := natLog_mul_log_two_le hm
  have hl2 := Real.log_two_gt_d9
  have hlog : log ((2 * g * s : ℕ) : ℝ) ≤ log 2 + log ((g : ℝ) * s + 2) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    apply Real.log_le_log (by positivity)
    push_cast; nlinarith
  have hN : (Nat.log 2 (2 * g * s) : ℝ) ≤ 1 + 2 * log ((g : ℝ) * s + 2) := by
    have h1 : (Nat.log 2 (2 * g * s) : ℝ) * log 2 ≤ log 2 + log ((g : ℝ) * s + 2) :=
      hnl.trans hlog
    have h0 : (0 : ℝ) ≤ Nat.log 2 (2 * g * s) := Nat.cast_nonneg _
    nlinarith
  have he := (exp_pos 1).le
  calc exp 1 * ((Nat.log 2 (2 * g * s) : ℕ) + 1 : ℝ) ≤ exp 1 * (4 * log ((g : ℝ) * s + 2)) := by
        gcongr; linarith
    _ = 4 * exp 1 * log (g * s + 2) := by ring

theorem prod_sievePrimes_le {g s z : ℕ} (hg : 1 ≤ g) (hs : 1 ≤ s) (hz : 2 ≤ z) :
    ∏ p ∈ sievePrimes g s z, (1 - 3 / (p : ℝ)) ≤ (4 * exp 1 * log (g * s + 2) / log z) ^ 3 := by
  classical
  set P' := sievePrimes g s z
  set D := z.primesBelow.filter (fun p => p ∣ 2 * g * s)
  have hP'3 : ∀ p ∈ P', (3 : ℝ) ≤ p := by
    intro p hp
    obtain ⟨hpp, hpd⟩ := sievePrimes_spec p hp
    have : p ≠ 2 := by
      rintro rfl; exact hpd (dvd_mul_of_dvd_left (dvd_mul_right 2 g) s)
    have := hpp.two_le
    exact_mod_cast (show 3 ≤ p by omega)
  have hfac_pos : ∀ p ∈ z.primesBelow, 0 < 1 - 1 / (p : ℝ) := by
    intro p hp
    have : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primesBelow hp).two_le
    have : 1 / (p : ℝ) ≤ 1 / 2 := by gcongr
    linarith
  -- step 1: `1 - 3/p ≤ (1 - 1/p)^3`
  have h1 : ∏ p ∈ P', (1 - 3 / (p : ℝ)) ≤ (∏ p ∈ P', (1 - 1 / (p : ℝ))) ^ 3 := by
    rw [← prod_pow]
    apply prod_le_prod₀
    · intro p hp
      have := hP'3 p hp
      rw [sub_nonneg, div_le_one (by linarith)]; exact this
    · intro p hp
      have := hP'3 p hp
      have hp0 : (0 : ℝ) < p := by linarith
      have : (1 - 1 / (p : ℝ)) ^ 3 - (1 - 3 / p) = (3 * p - 1) / p ^ 3 := by
        field_simp; ring
      have : 0 ≤ (3 * (p : ℝ) - 1) / p ^ 3 := div_nonneg (by linarith) (by positivity)
      linarith
  -- step 2: split off the primes dividing `2 g s`
  have hsplit := prod_filter_mul_prod_filter_not z.primesBelow (fun p => p ∣ 2 * g * s)
    (fun p => 1 - 1 / (p : ℝ))
  have hDpos : 0 < ∏ p ∈ D, (1 - 1 / (p : ℝ)) :=
    prod_pos fun p hp => hfac_pos p (mem_filter.mp hp).1
  have hP'pos : 0 ≤ ∏ p ∈ P', (1 - 1 / (p : ℝ)) :=
    prod_nonneg fun p hp => (hfac_pos p (mem_filter.mp hp).1).le
  have hDinv : (∏ p ∈ D, (1 - 1 / (p : ℝ)))⁻¹ ≤ 4 * exp 1 * log (g * s + 2) := by
    rw [← prod_inv_distrib]
    refine le_trans ?_ (local_factor_le hg hs)
    apply prod_le_prod_of_subset_of_one_le₀
    · intro p hp
      simp only [D, mem_filter, Nat.mem_primesBelow] at hp
      rw [Nat.mem_primeFactors]
      exact ⟨hp.1.2, hp.2, by positivity⟩
    · intro p hp; exact (inv_pos.mpr (hfac_pos p (mem_filter.mp hp).1)).le
    · intro p hp _
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
      have h1 : 1 / (p : ℝ) ≤ 1 / 2 := by gcongr
      have h2 : 0 < 1 - 1 / (p : ℝ) := by linarith
      rw [one_le_inv₀ h2]
      have : 0 < 1 / (p : ℝ) := by positivity
      linarith
  have hall := prod_one_sub_inv_le hz
  have hlogz : 0 < log z := Real.log_pos (by exact_mod_cast (show 1 < z by omega))
  have h2 : ∏ p ∈ P', (1 - 1 / (p : ℝ)) ≤ 4 * exp 1 * log (g * s + 2) / log z := by
    have heq : ∏ p ∈ P', (1 - 1 / (p : ℝ)) =
        (∏ p ∈ z.primesBelow, (1 - 1 / (p : ℝ))) * (∏ p ∈ D, (1 - 1 / (p : ℝ)))⁻¹ := by
      rw [← hsplit]
      have hD0 : (∏ p ∈ D, (1 - 1 / (p : ℝ))) ≠ 0 := hDpos.ne'
      field_simp
      rw [mul_comm]
      rfl
    rw [heq]
    calc (∏ p ∈ z.primesBelow, (1 - 1 / (p : ℝ))) * (∏ p ∈ D, (1 - 1 / (p : ℝ)))⁻¹
        ≤ (1 / log z) * (4 * exp 1 * log (g * s + 2)) := by
          apply mul_le_mul hall hDinv (inv_pos.mpr hDpos).le (by positivity)
      _ = 4 * exp 1 * log (g * s + 2) / log z := by ring
  calc ∏ p ∈ P', (1 - 3 / (p : ℝ)) ≤ (∏ p ∈ P', (1 - 1 / (p : ℝ))) ^ 3 := h1
    _ ≤ (4 * exp 1 * log (g * s + 2) / log z) ^ 3 := by gcongr

theorem sum_sievePrimes_le (g s z : ℕ) :
    ∑ p ∈ sievePrimes g s z, (1 / (p : ℝ)) ≤ cM * (1 + log (Nat.log 2 z + 1)) :=
  (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)).trans
    (sum_primesBelow_inv_le z)

theorem prod_sievePrimes_nonneg (g s z : ℕ) : 0 ≤ ∏ p ∈ sievePrimes g s z, (1 - 3 / (p : ℝ)) := by
  apply prod_nonneg
  intro p hp
  obtain ⟨hpp, hpd⟩ := sievePrimes_spec p hp
  have : p ≠ 2 := by rintro rfl; exact hpd (dvd_mul_of_dvd_left (dvd_mul_right 2 g) s)
  have := hpp.two_le
  have h3 : (3 : ℝ) ≤ p := by exact_mod_cast (show 3 ≤ p by omega)
  rw [sub_nonneg, div_le_one (by linarith)]; exact h3

/-- The constant `a = 3 e cM` governing the size of the sieve tail. -/
noncomputable def aConst : ℝ := 3 * exp 1 * cM

theorem aConst_pos : 0 < aConst := by unfold aConst; have := cM_pos; positivity

/-- Brun's bound with all prime sums estimated. -/
theorem card_tripleSet_le_param {g s : ℕ} (hg : 1 ≤ g) (hs : 1 ≤ s) {X : ℝ} (hX : 1 ≤ X)
    (z k : ℕ) (hz : 2 ≤ z) :
    ((tripleSet g s X).card : ℝ) ≤
      z + 2 * X * ((4 * exp 1 * log (g * s + 2) / log z) ^ 3 +
        exp (-(2 * k + 1 : ℝ)) * exp (aConst * (1 + log (Nat.log 2 z + 1)))) +
      (3 * (z + 1)) ^ (2 * k) := by
  have h := card_tripleSetN_le (g := g) hs z k (⌊X⌋₊ + 1)
  have hT : tripleSet g s X = tripleSetN g s (⌊X⌋₊ + 1) := rfl
  rw [hT]
  have hM : ((⌊X⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * X := by
    push_cast; have := Nat.floor_le (show 0 ≤ X by linarith); linarith
  have hB0 : 0 ≤ ∏ p ∈ sievePrimes g s z, (1 - 3 / (p : ℝ)) +
      exp (-(2 * k + 1 : ℝ)) * exp (3 * exp 1 * ∑ p ∈ sievePrimes g s z, 1 / (p : ℝ)) :=
    add_nonneg (prod_sievePrimes_nonneg g s z) (by positivity)
  have hB : ∏ p ∈ sievePrimes g s z, (1 - 3 / (p : ℝ)) +
      exp (-(2 * k + 1 : ℝ)) * exp (3 * exp 1 * ∑ p ∈ sievePrimes g s z, 1 / (p : ℝ)) ≤
      (4 * exp 1 * log (g * s + 2) / log z) ^ 3 +
        exp (-(2 * k + 1 : ℝ)) * exp (aConst * (1 + log (Nat.log 2 z + 1))) := by
    have hexp : 3 * exp 1 * ∑ p ∈ sievePrimes g s z, 1 / (p : ℝ) ≤
        aConst * (1 + log (Nat.log 2 z + 1)) := by
      rw [aConst, mul_assoc (3 * exp 1) cM]
      exact mul_le_mul_of_nonneg_left (sum_sievePrimes_le g s z) (by positivity)
    exact add_le_add (prod_sievePrimes_le hg hs hz)
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (exp_pos _).le)
  have := mul_le_mul hM hB hB0 (by linarith)
  linarith

/-! ### Choice of parameters and asymptotics -/

theorem exp_three_log {L : ℝ} (h : 0 < L) : exp (3 * log L) = L ^ 3 := by
  rw [show (3 : ℝ) * log L = log (L ^ 3) by rw [Real.log_pow]; norm_num, Real.exp_log (by positivity)]

/-- The constant `K` with `k ≤ K log log X`. -/
noncomputable def KConst : ℝ := 4 * aConst + 13

theorem KConst_pos : 0 < KConst := by unfold KConst; have := aConst_pos; positivity

theorem eventually_mul_log_le (c : ℝ) : ∀ᶠ L : ℝ in atTop, c * log L ≤ L := by
  have h := isLittleO_log_id_atTop.bound (show (0 : ℝ) < 1 / (|c| + 1) by positivity)
  filter_upwards [h, eventually_ge_atTop 1] with L hL hL1
  have hl : 0 ≤ log L := Real.log_nonneg hL1
  rw [Real.norm_of_nonneg hl, id, Real.norm_of_nonneg (by linarith)] at hL
  have hc := abs_nonneg c
  calc c * log L ≤ |c| * log L := mul_le_mul_of_nonneg_right (le_abs_self c) hl
    _ ≤ (|c| + 1) * log L := by nlinarith
    _ ≤ (|c| + 1) * (1 / (|c| + 1) * L) := by gcongr
    _ = L := by field_simp

/-- The four conditions on `L = log X` used in the final estimate. -/
def GoodL (L : ℝ) : Prop :=
  exp 1 ≤ L ∧ 8 * KConst * log L ≤ L ∧ 4 * log L ≤ L ∧ (4 * KConst * log 6 + 6) * log L ≤ L

theorem eventually_goodL : ∀ᶠ L : ℝ in atTop, GoodL L := by
  filter_upwards [eventually_ge_atTop (exp 1), eventually_mul_log_le (8 * KConst),
    eventually_mul_log_le 4, eventually_mul_log_le (4 * KConst * log 6 + 6)] with L h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

theorem log_three_lt_two : log 3 < 2 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have := Real.add_one_lt_exp (show (2 : ℝ) ≠ 0 by norm_num)
  linarith

/-- The tail of the sieve is at most `L⁻³`. -/
theorem tail_le {L : ℝ} {k z : ℕ} (hLpos : 0 < L) (hlogL : 1 ≤ log L)
    (hk_lo : (aConst + 3) * (3 + log L) ≤ k) (hz0 : z ≠ 0) (hzL : log (z : ℝ) ≤ L) :
    exp (-(2 * k + 1 : ℝ)) * exp (aConst * (1 + log (Nat.log 2 z + 1))) ≤ 1 / L ^ 3 := by
  have ha := aConst_pos
  have hnl : (Nat.log 2 z : ℝ) + 1 ≤ 3 * L := by
    have h1 := natLog_mul_log_two_le hz0
    have := Real.log_two_gt_d9
    have h0 : (0 : ℝ) ≤ Nat.log 2 z := Nat.cast_nonneg _
    have hL1 : 1 ≤ L := by
      by_contra h
      push Not at h
      have : log L ≤ 0 := Real.log_nonpos hLpos.le h.le
      linarith
    nlinarith
  have hlog3 : log ((Nat.log 2 z : ℝ) + 1) ≤ 2 + log L := by
    calc log ((Nat.log 2 z : ℝ) + 1) ≤ log (3 * L) := Real.log_le_log (by positivity) hnl
      _ = log 3 + log L := Real.log_mul (by norm_num) hLpos.ne'
      _ ≤ 2 + log L := by linarith [log_three_lt_two]
  have hexp : -(2 * k + 1 : ℝ) + aConst * (1 + log (Nat.log 2 z + 1)) ≤ -(3 * log L) := by
    have : aConst * (1 + log ((Nat.log 2 z : ℝ) + 1)) ≤ aConst * (3 + log L) :=
      mul_le_mul_of_nonneg_left (by linarith) ha.le
    nlinarith
  rw [← Real.exp_add]
  calc exp (-(2 * k + 1 : ℝ) + aConst * (1 + log (Nat.log 2 z + 1)))
      ≤ exp (-(3 * log L)) := Real.exp_le_exp.mpr hexp
    _ = 1 / L ^ 3 := by rw [Real.exp_neg, exp_three_log hLpos, one_div]

/-- The error term `(3(z+1))^{2k}` is at most `e^L / L³`. -/
theorem error_le {L y : ℝ} {k z : ℕ} (hLpos : 0 < L) (hk_hi : (k : ℝ) ≤ KConst * log L)
    (hky : 2 * (k : ℝ) * y = L / 2) (hz : (z : ℝ) ≤ exp y) (hy1 : 1 ≤ exp y)
    (hL4 : (4 * KConst * log 6 + 6) * log L ≤ L) :
    (3 * ((z : ℝ) + 1)) ^ (2 * k) * L ^ 3 ≤ exp L := by
  have hl6 : 0 < log 6 := Real.log_pos (by norm_num)
  have hpow : (3 * ((z : ℝ) + 1)) ^ (2 * k) ≤ (6 * exp y) ^ (2 * k) :=
    pow_le_pow_left₀ (by positivity) (by linarith) _
  have h6 : (6 * exp y) ^ (2 * k) = exp (2 * k * log 6 + L / 2) := by
    rw [Real.exp_add, ← hky, mul_pow]
    congr 1
    · rw [← Real.exp_log (show (0 : ℝ) < 6 by norm_num), ← Real.exp_nat_mul,
        Real.exp_log (show (0 : ℝ) < 6 by norm_num)]
      push_cast; ring_nf
    · rw [← Real.exp_nat_mul]; push_cast; ring_nf
  have hk : 2 * k * log 6 ≤ 2 * (KConst * log L) * log 6 := by gcongr
  calc (3 * ((z : ℝ) + 1)) ^ (2 * k) * L ^ 3
      ≤ exp (2 * k * log 6 + L / 2) * exp (3 * log L) := by
        rw [← h6, exp_three_log hLpos]; gcongr
    _ = exp (2 * k * log 6 + L / 2 + 3 * log L) := by rw [← Real.exp_add]
    _ ≤ exp L := by
        apply Real.exp_le_exp.mpr
        nlinarith

/-- The main term. -/
theorem mainTerm_le {L y lg : ℝ} {k z : ℕ} (hLpos : 0 < L) (hlg : 0 ≤ lg)
    (hk_hi : (k : ℝ) ≤ KConst * log L) (hyk : y * (4 * k) = L)
    (hlogz : y / 2 ≤ log (z : ℝ)) (hlogz_pos : 0 < log (z : ℝ)) :
    (4 * exp 1 * lg / log z) ^ 3 ≤ (32 * exp 1 * KConst) ^ 3 * lg ^ 3 * log L ^ 3 / L ^ 3 := by
  have hK := KConst_pos
  have : 4 * exp 1 * lg / log z ≤ 32 * exp 1 * KConst * lg * log L / L := by
    rw [div_le_div_iff₀ hlogz_pos hLpos]
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have h1 : L ≤ 8 * k * log z := by nlinarith
    have h2 : 0 ≤ 4 * exp 1 * lg := by positivity
    calc 4 * exp 1 * lg * L ≤ 4 * exp 1 * lg * (8 * k * log z) :=
          mul_le_mul_of_nonneg_left h1 h2
      _ ≤ 4 * exp 1 * lg * (8 * (KConst * log L) * log z) := by gcongr
      _ = 32 * exp 1 * KConst * lg * log L * log z := by ring
  calc (4 * exp 1 * lg / log z) ^ 3 ≤ (32 * exp 1 * KConst * lg * log L / L) ^ 3 := by
        gcongr
    _ = (32 * exp 1 * KConst) ^ 3 * lg ^ 3 * log L ^ 3 / L ^ 3 := by ring

theorem card_tripleSet_le_large {g s : ℕ} (hg : 1 ≤ g) (hs : 1 ≤ s) {X : ℝ} (hX : 1 ≤ X)
    (hL : GoodL (log X)) :
    ((tripleSet g s X).card : ℝ) ≤
      (4 + 2 * (32 * exp 1 * KConst) ^ 3) * X * log (g * s + 2) ^ 3 * log (log X) ^ 3 /
        log X ^ 3 := by
  obtain ⟨hL1, hL2, hL3, hL4⟩ := hL
  have hX0 : 0 < X := by linarith
  have he := Real.exp_one_gt_d9
  have hLpos : 0 < log X := by linarith
  have hexpL : exp (log X) = X := Real.exp_log hX0
  have hlogL : 1 ≤ log (log X) := by rw [Real.le_log_iff_exp_le hLpos]; exact hL1
  have ha := aConst_pos
  have hK := KConst_pos
  -- the parameter `k`
  obtain ⟨k, hk_lo, hk_hi⟩ : ∃ k : ℕ, (aConst + 3) * (3 + log (log X)) ≤ k ∧
      (k : ℝ) ≤ KConst * log (log X) := by
    refine ⟨⌈(aConst + 3) * (3 + log (log X))⌉₊, Nat.le_ceil _, ?_⟩
    have := Nat.ceil_lt_add_one (show 0 ≤ (aConst + 3) * (3 + log (log X)) by positivity)
    have h1 : (3 * aConst + 10) * 1 ≤ (3 * aConst + 10) * log (log X) :=
      mul_le_mul_of_nonneg_left hlogL (by linarith)
    rw [KConst]; nlinarith
  have hk1 : (1 : ℝ) ≤ k := by nlinarith
  have hk0 : (0 : ℝ) < k := by linarith
  -- the parameter `z`
  obtain ⟨y, hyk⟩ : ∃ y : ℝ, y * (4 * k) = log X := ⟨log X / (4 * k), by field_simp⟩
  have hy2 : 2 ≤ y := by nlinarith
  have hyL : y ≤ log X / 4 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 4)]; nlinarith
  have hexpy : 2 * 2 ≤ exp y := by
    have h1 : exp 2 ≤ exp y := Real.exp_le_exp.mpr hy2
    have h2 : exp 2 = exp 1 * exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith
  obtain ⟨z, hz_le, hz_ge⟩ : ∃ z : ℕ, (z : ℝ) ≤ exp y ∧ exp y - 1 < z :=
    ⟨⌊exp y⌋₊, Nat.floor_le (exp_pos y).le, by have := Nat.lt_floor_add_one (exp y); linarith⟩
  have hz2' : (2 : ℝ) ≤ z := by linarith
  have hz2 : 2 ≤ z := by exact_mod_cast hz2'
  have hlogz : y / 2 ≤ log (z : ℝ) := by
    have h1 : exp y / 2 ≤ z := by linarith
    have h2 : log (exp y / 2) ≤ log z := Real.log_le_log (by positivity) h1
    rw [Real.log_div (exp_pos y).ne' (by norm_num), Real.log_exp] at h2
    have := Real.log_two_lt_d9
    linarith
  have hexp_le : exp y ≤ exp (log X / 4) := Real.exp_le_exp.mpr hyL
  have hzX : (z : ℝ) ≤ X := by
    have : exp (log X / 4) ≤ exp (log X) := Real.exp_le_exp.mpr (by linarith)
    linarith
  have hlogz_pos : 0 < log (z : ℝ) := Real.log_pos (by linarith)
  have hzL : log (z : ℝ) ≤ log X := Real.log_le_log (by linarith) hzX
  -- the four pieces
  have hmain := card_tripleSet_le_param hg hs hX z k hz2
  set lg := log ((g : ℝ) * s + 2) with hlgdef
  have hlg : 1 ≤ lg := by
    have : (1 : ℝ) ≤ g * s := by
      have : (1 : ℝ) ≤ g := by exact_mod_cast hg
      have : (1 : ℝ) ≤ s := by exact_mod_cast hs
      nlinarith
    exact one_le_log_three.trans (Real.log_le_log (by norm_num) (by linarith))
  have hL3pos : 0 < log X ^ 3 := by positivity
  have hT1 : (z : ℝ) ≤ X / log X ^ 3 := by
    rw [le_div_iff₀ hL3pos]
    have h3 : log X ^ 3 ≤ exp (3 * log X / 4) := by
      rw [← exp_three_log hLpos]; apply Real.exp_le_exp.mpr; linarith
    calc (z : ℝ) * log X ^ 3 ≤ exp (log X / 4) * exp (3 * log X / 4) := by
          gcongr; linarith
      _ = exp (log X) := by rw [← Real.exp_add]; ring_nf
      _ = X := hexpL
  have hT2 := mainTerm_le hLpos (by linarith : (0 : ℝ) ≤ lg) hk_hi hyk hlogz
    hlogz_pos
  have hT3 := tail_le hLpos hlogL hk_lo (by omega) hzL
  have hT4 : (3 * ((z : ℝ) + 1)) ^ (2 * k) ≤ X / log X ^ 3 := by
    rw [le_div_iff₀ hL3pos]
    calc (3 * ((z : ℝ) + 1)) ^ (2 * k) * log X ^ 3 ≤ exp (log X) :=
          error_le hLpos hk_hi (by nlinarith) hz_le (by linarith) hL4
      _ = X := hexpL
  -- assembling
  have hfinal : ((tripleSet g s X).card : ℝ) ≤
      X / log X ^ 3 + 2 * X * ((32 * exp 1 * KConst) ^ 3 * lg ^ 3 * log (log X) ^ 3 / log X ^ 3 +
        1 / log X ^ 3) + X / log X ^ 3 := by
    exact hmain.trans (add_le_add (add_le_add hT1 (mul_le_mul_of_nonneg_left
      (add_le_add hT2 hT3) (by positivity : (0 : ℝ) ≤ 2 * X))) hT4)
  have hone : 1 ≤ lg ^ 3 * log (log X) ^ 3 :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hlg) (one_le_pow₀ hlogL)
  have hc : 0 ≤ 2 * (32 * exp 1 * KConst) ^ 3 := by positivity
  calc ((tripleSet g s X).card : ℝ)
      ≤ X / log X ^ 3 + 2 * X * ((32 * exp 1 * KConst) ^ 3 * lg ^ 3 * log (log X) ^ 3 /
          log X ^ 3 + 1 / log X ^ 3) + X / log X ^ 3 := hfinal
    _ = (X / log X ^ 3) * (4 + 2 * (32 * exp 1 * KConst) ^ 3 * (lg ^ 3 * log (log X) ^ 3)) := by
        field_simp; ring
    _ ≤ (X / log X ^ 3) * ((4 + 2 * (32 * exp 1 * KConst) ^ 3) * (lg ^ 3 * log (log X) ^ 3)) := by
        gcongr
        nlinarith
    _ = (4 + 2 * (32 * exp 1 * KConst) ^ 3) * X * lg ^ 3 * log (log X) ^ 3 / log X ^ 3 := by
        ring

/-- **The sieve bound for prime triples** (`TripleSieveBound`), proved by Brun's pure sieve. -/
theorem tripleSieveBound : TripleSieveBound := by
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.mp eventually_goodL
  set X₀ := max 16 (exp L₀) with hX₀
  set C₁ : ℝ := 4 + 2 * (32 * exp 1 * KConst) ^ 3
  refine ⟨max C₁ (2 * log X₀ ^ 3), ?_⟩
  intro g s hg hs X hX
  have hX1 : 1 ≤ X := by linarith
  have hlg : 1 ≤ log ((g : ℝ) * s + 2) := by
    have : (1 : ℝ) ≤ g * s := by
      have : (1 : ℝ) ≤ g := by exact_mod_cast hg
      have : (1 : ℝ) ≤ s := by exact_mod_cast hs
      nlinarith
    exact one_le_log_three.trans (Real.log_le_log (by norm_num) (by linarith))
  have hlog16 : exp 1 ≤ log X := by
    have h16 : log 16 ≤ log X := Real.log_le_log (by norm_num) hX
    have : log (16 : ℝ) = 4 * log 2 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_gt_d9
    have := Real.exp_one_lt_d9
    linarith
  have hLpos : 0 < log X := by have := exp_pos 1; linarith
  have hloglog : 1 ≤ log (log X) := by rw [Real.le_log_iff_exp_le hLpos]; exact hlog16
  have hR0 : 0 ≤ X * log ((g : ℝ) * s + 2) ^ 3 * log (log X) ^ 3 / log X ^ 3 := by positivity
  by_cases hbig : X₀ ≤ X
  · have hgood : GoodL (log X) := by
      apply hL₀
      have : exp L₀ ≤ X := (le_max_right _ _).trans hbig
      calc L₀ = log (exp L₀) := (Real.log_exp L₀).symm
        _ ≤ log X := Real.log_le_log (exp_pos _) this
    have h := card_tripleSet_le_large hg hs hX1 hgood
    calc ((tripleSet g s X).card : ℝ)
        ≤ C₁ * X * log ((g : ℝ) * s + 2) ^ 3 * log (log X) ^ 3 / log X ^ 3 := h
      _ = C₁ * (X * log ((g : ℝ) * s + 2) ^ 3 * log (log X) ^ 3 / log X ^ 3) := by ring
      _ ≤ max C₁ (2 * log X₀ ^ 3) *
            (X * log ((g : ℝ) * s + 2) ^ 3 * log (log X) ^ 3 / log X ^ 3) := by
          gcongr; exact le_max_left _ _
      _ = _ := by ring
  · push Not at hbig
    have htriv : ((tripleSet g s X).card : ℝ) ≤ 2 * X := by
      have h1 : (tripleSet g s X).card ≤ ⌊X⌋₊ + 1 := by
        unfold tripleSet
        exact (card_filter_le _ _).trans (by rw [card_range])
      have h2 : ((⌊X⌋₊ + 1 : ℕ) : ℝ) ≤ X + 1 := by
        push_cast; linarith [Nat.floor_le (show 0 ≤ X by linarith)]
      have : ((tripleSet g s X).card : ℝ) ≤ ((⌊X⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast h1
      linarith
    have hlogX : log X ≤ log X₀ := Real.log_le_log (by linarith) hbig.le
    have hfac : 1 ≤ log ((g : ℝ) * s + 2) ^ 3 * log (log X) ^ 3 :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ hlg) (one_le_pow₀ hloglog)
    have hXL : 0 ≤ X / log X ^ 3 := div_nonneg (by linarith) (pow_nonneg hLpos.le 3)
    calc ((tripleSet g s X).card : ℝ) ≤ 2 * X := htriv
      _ = 2 * log X ^ 3 * (X / log X ^ 3) := by field_simp
      _ ≤ 2 * log X₀ ^ 3 * (X / log X ^ 3 * (log ((g : ℝ) * s + 2) ^ 3 * log (log X) ^ 3)) := by
          exact mul_le_mul (by gcongr) (le_mul_of_one_le_right hXL hfac)
            hXL (mul_nonneg (by norm_num) (pow_nonneg (hLpos.le.trans hlogX) 3))
      _ ≤ max C₁ (2 * log X₀ ^ 3) *
            (X / log X ^ 3 * (log ((g : ℝ) * s + 2) ^ 3 * log (log X) ^ 3)) := by
          gcongr; exact le_max_right _ _
      _ = _ := by ring

end WLJ.Sieve

namespace WLJ

/-- **Theorem 1** (Conjecture 9 of arXiv:0711.0865), unconditionally: the primes classified by
level are rarefying among the primes. -/
theorem theorem1 : Theorem1 := theorem1_of_sieve Sieve.tripleSieveBound

end WLJ
