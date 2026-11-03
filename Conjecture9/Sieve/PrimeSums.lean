/-
# Elementary estimates for sums and products over primes

* `prod_one_sub_inv_le`: the Euler product bound `∏_{p < N} (1 - 1/p) ≤ 1 / log N`,
  deduced from Mathlib's Euler product for `n ↦ n^{-σ}` by letting `σ → 1⁺`.
* `sum_primesBelow_inv_le`: a Mertens-type upper bound
  `∑_{p < N} 1/p ≤ cM · (1 + log (log₂ N + 1))`, deduced from Mathlib's Chebyshev bound
  `π(x) ≪ x / log x` by summing over dyadic blocks.
* `prod_primeFactors_inv_le`: `∏_{p ∣ m} (1 - 1/p)⁻¹ ≤ e · (log₂ m + 1)`.
-/
import Mathlib

namespace WLJ.Sieve

open Real Finset Filter Topology

/-! ### The Euler product lower bound -/

theorem sum_rpow_le_prod_primesBelow (N : ℕ) {σ : ℝ} (hσ : 1 < σ) :
    ∑ m ∈ Ico 1 N, (m : ℝ) ^ (-σ) ≤ ∏ p ∈ N.primesBelow, (1 - (p : ℝ) ^ (-σ))⁻¹ := by
  classical
  let f : ℕ →* ℝ :=
    { toFun := fun n => (n : ℝ) ^ (-σ)
      map_one' := by simp
      map_mul' := fun a b => by
        push_cast
        exact Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _) }
  have hsum : Summable f := Real.summable_nat_rpow.mpr (by linarith)
  have h := EulerProduct.prod_primesBelow_geometric_eq_tsum_smoothNumbers hsum N
  have hf : ∀ n : ℕ, f n = (n : ℝ) ^ (-σ) := fun n => rfl
  simp only [hf] at h
  rw [h]
  have hsub : Summable (fun m : N.smoothNumbers => ((m : ℕ) : ℝ) ^ (-σ)) :=
    (hsum.subtype N.smoothNumbers)
  have hmem : ∀ m ∈ Ico 1 N, m ∈ N.smoothNumbers := fun m hm => by
    rw [mem_Ico] at hm
    exact Nat.mem_smoothNumbers_of_lt (by omega) hm.2
  calc ∑ m ∈ Ico 1 N, (m : ℝ) ^ (-σ)
      = ∑ m ∈ (Ico 1 N).subtype (· ∈ N.smoothNumbers), ((m : ℕ) : ℝ) ^ (-σ) :=
        (sum_subtype_of_mem (fun m : ℕ => (m : ℝ) ^ (-σ)) hmem).symm
    _ ≤ ∑' m : N.smoothNumbers, ((m : ℕ) : ℝ) ^ (-σ) :=
        hsub.sum_le_tsum _ (fun _ _ => by positivity)

theorem sum_inv_le_prod_primesBelow (N : ℕ) :
    ∑ m ∈ Ico 1 N, (1 / (m : ℝ)) ≤ ∏ p ∈ N.primesBelow, (1 - 1 / (p : ℝ))⁻¹ := by
  have hcont_sum : Tendsto (fun σ : ℝ => ∑ m ∈ Ico 1 N, (m : ℝ) ^ (-σ)) (𝓝[>] 1)
      (𝓝 (∑ m ∈ Ico 1 N, (m : ℝ) ^ (-(1 : ℝ)))) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    apply tendsto_finsetSum
    intro m hm
    rw [mem_Ico] at hm
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm.1
    have hm0 : (m : ℝ) ≠ 0 := by linarith
    exact ((continuous_const.rpow continuous_neg (fun _ => Or.inl hm0)).tendsto 1)
  have hcont_prod : Tendsto (fun σ : ℝ => ∏ p ∈ N.primesBelow, (1 - (p : ℝ) ^ (-σ))⁻¹) (𝓝[>] 1)
      (𝓝 (∏ p ∈ N.primesBelow, (1 - (p : ℝ) ^ (-(1 : ℝ)))⁻¹)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    apply tendsto_finsetProd
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primesBelow hp).two_le
    have hp0 : (p : ℝ) ≠ 0 := by linarith
    have hc : Tendsto (fun σ : ℝ => (p : ℝ) ^ (-σ)) (𝓝 1) (𝓝 ((p : ℝ) ^ (-(1 : ℝ)))) :=
      (continuous_const.rpow continuous_neg (fun _ => Or.inl hp0)).tendsto 1
    refine (tendsto_const_nhds.sub hc).inv₀ ?_
    rw [Real.rpow_neg_one]
    have : (p : ℝ)⁻¹ ≤ 1 / 2 := by rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    linarith
  have hle := le_of_tendsto_of_tendsto hcont_sum hcont_prod
    (eventually_nhdsWithin_of_forall fun σ hσ => sum_rpow_le_prod_primesBelow N hσ)
  simpa [Real.rpow_neg_one] using hle

/-- **Euler product bound.** For `N ≥ 2`, `∏_{p < N} (1 - 1/p) ≤ 1 / log N`. -/
theorem prod_one_sub_inv_le {N : ℕ} (hN : 2 ≤ N) :
    ∏ p ∈ N.primesBelow, (1 - 1 / (p : ℝ)) ≤ 1 / log N := by
  have hharm : log N ≤ ∑ m ∈ Ico 1 N, (1 / (m : ℝ)) := by
    have h := log_add_one_le_harmonic (N - 1)
    rw [harmonic_eq_sum_Icc] at h
    push_cast at h
    have hIcc : Icc 1 (N - 1) = Ico 1 N := by
      ext m; simp only [mem_Icc, mem_Ico]; omega
    rw [hIcc] at h
    have hc : ((N - 1 : ℕ) : ℝ) + 1 = N := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [hc] at h
    simpa [one_div] using h
  have hlog : 0 < log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hprod := (hharm.trans (sum_inv_le_prod_primesBelow N))
  rw [prod_inv_distrib] at hprod
  have hpos : 0 < ∏ p ∈ N.primesBelow, (1 - 1 / (p : ℝ)) := by
    apply prod_pos
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primesBelow hp).two_le
    rw [sub_pos, div_lt_one (by linarith)]; linarith
  rw [le_inv_comm₀ hlog hpos] at hprod
  rwa [one_div]

/-! ### A Mertens-type upper bound -/

/-- The constant in the Mertens-type bound. -/
noncomputable def cM : ℝ := 4 * (log 4 + 1) / log 2

theorem cM_pos : 0 < cM := by
  unfold cM
  have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have := Real.log_pos (by norm_num : (1 : ℝ) < 4)
  positivity

/-- `π(2^{J+1}) ≤ cM · 2^J / (J+1)`. -/
theorem primeCounting_two_pow_le (J : ℕ) :
    (Nat.primeCounting (2 ^ (J + 1)) : ℝ) ≤ cM * 2 ^ J / (J + 1) := by
  set x : ℝ := 2 ^ (J + 1) with hx
  have hx2 : (2 : ℝ) ≤ x := by
    rw [hx]; calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (J + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have h := Chebyshev.pi_le_log4_mul_div (x := x) (by linarith)
  have hfl : ⌊x⌋₊ = 2 ^ (J + 1) := by rw [hx]; exact_mod_cast Nat.floor_natCast (2 ^ (J + 1))
  rw [hfl] at h
  have hl2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hlogsqrt : log √x = (J + 1) * log 2 / 2 := by
    rw [Real.log_sqrt (by linarith), hx, Real.log_pow]; push_cast; ring
  have hls_pos : 0 < log √x := by rw [hlogsqrt]; positivity
  -- `√x ≤ x / log √x` because `log √x ≤ √x`
  have hsq : √x ≤ x / log √x := by
    rw [le_div_iff₀ hls_pos]
    have h1 : log √x ≤ √x := (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
    have h2 : √x * √x = x := Real.mul_self_sqrt (by linarith)
    nlinarith [Real.sqrt_nonneg x]
  have h4 : log 4 = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  calc (Nat.primeCounting (2 ^ (J + 1)) : ℝ) ≤ log 4 * x / log √x + √x := h
    _ ≤ log 4 * x / log √x + x / log √x := by linarith
    _ = (log 4 + 1) * x / log √x := by ring
    _ = cM * 2 ^ J / (J + 1) := by
        rw [hlogsqrt, hx, cM]
        field_simp
        ring

theorem sum_primesBelow_two_pow_le (J : ℕ) :
    ∑ p ∈ (2 ^ J : ℕ).primesBelow, (1 / (p : ℝ)) ≤ cM * harmonic J := by
  induction J with
  | zero => simp
  | succ J ih =>
    classical
    set S := (2 ^ (J + 1)).primesBelow
    have hsplit := sum_filter_add_sum_filter_not S (fun p => 2 ^ J ≤ p) (fun p => 1 / (p : ℝ))
    have hlow : S.filter (fun p => ¬ 2 ^ J ≤ p) = (2 ^ J : ℕ).primesBelow := by
      ext p
      simp only [S, mem_filter, Nat.mem_primesBelow]
      constructor
      · rintro ⟨⟨_, hp⟩, h⟩; exact ⟨by omega, hp⟩
      · rintro ⟨h, hp⟩; exact ⟨⟨by rw [pow_succ]; omega, hp⟩, by omega⟩
    have hblock : ∑ p ∈ S.filter (fun p => 2 ^ J ≤ p), (1 / (p : ℝ)) ≤ cM / (J + 1) := by
      calc ∑ p ∈ S.filter (fun p => 2 ^ J ≤ p), (1 / (p : ℝ))
          ≤ ∑ p ∈ S.filter (fun p => 2 ^ J ≤ p), (1 / (2 : ℝ) ^ J) := by
            apply sum_le_sum
            intro p hp
            rw [mem_filter] at hp
            have : (2 : ℝ) ^ J ≤ p := by exact_mod_cast hp.2
            gcongr
        _ = (S.filter (fun p => 2 ^ J ≤ p)).card * (1 / (2 : ℝ) ^ J) := by
            rw [sum_const, nsmul_eq_mul]
        _ ≤ (Nat.primeCounting (2 ^ (J + 1)) : ℝ) * (1 / (2 : ℝ) ^ J) := by
            gcongr
            have h1 := card_filter_le S (fun p => 2 ^ J ≤ p)
            have h2 : S.card ≤ Nat.primeCounting (2 ^ (J + 1)) := by
              rw [Nat.primesBelow_card_eq_primeCounting']
              exact Nat.monotone_primeCounting' (Nat.le_succ _)
            exact_mod_cast h1.trans h2
        _ ≤ cM * 2 ^ J / (J + 1) * (1 / (2 : ℝ) ^ J) := by
            gcongr; exact primeCounting_two_pow_le J
        _ = cM / (J + 1) := by field_simp
    rw [← hsplit, hlow]
    calc _ ≤ cM / (J + 1) + cM * harmonic J := add_le_add hblock ih
      _ = cM * harmonic (J + 1) := by rw [harmonic_succ]; push_cast; ring

/-- **Mertens-type bound.** `∑_{p < N} 1/p ≤ cM · (1 + log (log₂ N + 1))`. -/
theorem sum_primesBelow_inv_le (N : ℕ) :
    ∑ p ∈ N.primesBelow, (1 / (p : ℝ)) ≤ cM * (1 + log (Nat.log 2 N + 1)) := by
  set J := Nat.log 2 N + 1
  have hsub : N.primesBelow ⊆ (2 ^ J : ℕ).primesBelow := by
    intro p hp
    rw [Nat.mem_primesBelow] at hp ⊢
    exact ⟨hp.1.trans (Nat.lt_pow_succ_log_self (by norm_num) N), hp.2⟩
  calc ∑ p ∈ N.primesBelow, (1 / (p : ℝ)) ≤ ∑ p ∈ (2 ^ J : ℕ).primesBelow, (1 / (p : ℝ)) :=
        sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ cM * harmonic J := sum_primesBelow_two_pow_le J
    _ ≤ cM * (1 + log J) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast harmonic_le_one_add_log J) cM_pos.le
    _ = cM * (1 + log (Nat.log 2 N + 1)) := by simp [J]

/-! ### The local factor `∏_{p ∣ m} (1 - 1/p)⁻¹` -/

theorem prod_Icc_div_eq (y : ℕ) (hy : 1 ≤ y) :
    ∏ n ∈ Icc 2 y, (1 - 1 / (n : ℝ))⁻¹ = y := by
  induction y with
  | zero => omega
  | succ y ih =>
    rcases Nat.eq_zero_or_pos y with rfl | hy0
    · simp
    rw [prod_Icc_succ_top (by omega), ih hy0]
    push_cast
    have hy1 : (1 : ℝ) ≤ y := by exact_mod_cast hy0
    have hy0' : (y : ℝ) ≠ 0 := by linarith
    have : (1 - 1 / ((y : ℝ) + 1)) = y / (y + 1) := by field_simp; ring
    rw [this, inv_div]
    field_simp

/-- `∏_{p ∣ m} (1 - 1/p)⁻¹ ≤ e · (log₂ m + 1)`. -/
theorem prod_primeFactors_inv_le {m : ℕ} (hm : m ≠ 0) :
    ∏ p ∈ m.primeFactors, (1 - 1 / (p : ℝ))⁻¹ ≤ exp 1 * (Nat.log 2 m + 1) := by
  classical
  set y := Nat.log 2 m + 1 with hy
  have hfac : ∀ p ∈ m.primeFactors, (2 : ℝ) ≤ p := fun p hp => by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
  have hpos : ∀ p : ℕ, (2 : ℝ) ≤ p → 0 ≤ (1 - 1 / (p : ℝ))⁻¹ := fun p hp => by
    have : 1 / (p : ℝ) ≤ 1 / 2 := by gcongr
    have : 0 < 1 - 1 / (p : ℝ) := by linarith
    positivity
  have hone : ∀ p : ℕ, (2 : ℝ) ≤ p → 1 ≤ (1 - 1 / (p : ℝ))⁻¹ := fun p hp => by
    have h1 : 1 / (p : ℝ) ≤ 1 / 2 := by gcongr
    have h2 : 0 < 1 - 1 / (p : ℝ) := by linarith
    rw [one_le_inv₀ h2]
    have : 0 < 1 / (p : ℝ) := by positivity
    linarith
  rw [← prod_filter_mul_prod_filter_not m.primeFactors (fun p => p ≤ y)]
  -- small primes
  have hsmall : ∏ p ∈ m.primeFactors.filter (fun p => p ≤ y), (1 - 1 / (p : ℝ))⁻¹ ≤ y := by
    calc ∏ p ∈ m.primeFactors.filter (fun p => p ≤ y), (1 - 1 / (p : ℝ))⁻¹
        ≤ ∏ n ∈ Icc 2 y, (1 - 1 / (n : ℝ))⁻¹ := by
          apply prod_le_prod_of_subset_of_one_le₀
          · intro p hp
            rw [mem_filter] at hp
            rw [mem_Icc]
            exact ⟨(Nat.prime_of_mem_primeFactors hp.1).two_le, hp.2⟩
          · intro p hp; exact hpos p (hfac p (mem_filter.mp hp).1)
          · intro n hn _
            rw [mem_Icc] at hn
            exact hone n (by exact_mod_cast hn.1)
      _ = y := prod_Icc_div_eq y (by omega)
  -- large primes
  set D := m.primeFactors.filter (fun p => ¬ p ≤ y)
  have hDcard : D.card < y := by
    have h1 : 2 ^ D.card ≤ ∏ p ∈ D, p := by
      rw [← prod_const]
      exact Finset.prod_le_prod
        (fun p hp => (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1).two_le)
    have h2 : ∏ p ∈ D, p ∣ m :=
      (prod_dvd_prod_of_subset _ _ _ (filter_subset _ _)).trans (Nat.prod_primeFactors_dvd m)
    have h3 := Nat.le_of_dvd (Nat.pos_of_ne_zero hm) h2
    have := Nat.le_log_of_pow_le (by norm_num) (h1.trans h3)
    omega
  have hy0 : (0 : ℝ) < y := by positivity
  have hlarge : ∏ p ∈ D, (1 - 1 / (p : ℝ))⁻¹ ≤ exp 1 := by
    calc ∏ p ∈ D, (1 - 1 / (p : ℝ))⁻¹ ≤ ∏ p ∈ D, (1 + 1 / (y : ℝ)) := by
          apply Finset.prod_le_prod₀
          · intro p hp; exact hpos p (hfac p (mem_filter.mp hp).1)
          · intro p hp
            rw [mem_filter] at hp
            have hpy : (y : ℝ) + 1 ≤ p := by exact_mod_cast (show y + 1 ≤ p by omega)
            have hp1 : (0 : ℝ) < p - 1 := by linarith
            have : (1 - 1 / (p : ℝ))⁻¹ = 1 + 1 / (p - 1) := by
              have : (p : ℝ) ≠ 0 := by linarith
              field_simp
              ring
            rw [this]
            gcongr
            linarith
      _ = (1 + 1 / (y : ℝ)) ^ D.card := prod_const _
      _ ≤ (exp (1 / (y : ℝ))) ^ D.card := by
          gcongr; linarith [Real.add_one_le_exp (1 / (y : ℝ))]
      _ = exp (D.card / (y : ℝ)) := by rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ exp 1 := by
          gcongr
          rw [div_le_one hy0]
          exact_mod_cast hDcard.le
  have hDpos : 0 ≤ ∏ p ∈ D, (1 - 1 / (p : ℝ))⁻¹ :=
    prod_nonneg fun p hp => hpos p (hfac p (mem_filter.mp hp).1)
  calc (∏ p ∈ m.primeFactors.filter (fun p => p ≤ y), (1 - 1 / (p : ℝ))⁻¹) *
        ∏ p ∈ D, (1 - 1 / (p : ℝ))⁻¹ ≤ y * exp 1 := by
        apply mul_le_mul hsmall hlarge hDpos hy0.le
    _ = exp 1 * (Nat.log 2 m + 1) := by rw [hy]; push_cast; ring

end WLJ.Sieve
