/-
# Theorem 1 (= Conjecture 9 of arXiv:0711.0865)

> The prime numbers classified by level are rarefying among the primes.

Formally: the proportion of the first `N` primes that are classified by level (`k_n > L_n`)
tends to `0` as `N → ∞`.

## Status of the proof

The proof is complete **relative to one explicitly stated hypothesis**, `TripleSieveBound`,
which is a classical upper-bound sieve estimate for prime triples (a direct consequence of
Brun's pure sieve or of Selberg's sieve; see `README.md`). That estimate is not yet available in
Mathlib. Everything else is proved here: there is no `sorry` and no new axiom (`#print axioms`
in `Verify.lean` checks this). The main result is

  `theorem1_of_sieve : TripleSieveBound → Theorem1`.

## Proof outline

Let `x = P N` and `G = ⌊(log x)^{3/2}⌋`. By `levelCount_le`,

  #{n < N | classified by level} ≤ x/(G+1) + (G⁴+G+1) + ∑_{g ≤ G} ∑_{s ≤ g} #{q ≤ x/s | q, sq+g, sq+2g prime}.

The sieve bound gives `≪ x (log G)⁴ (log log x)³ G / (log x)³` for the double sum (the inner
sum over `s` contributes a factor `∑ 1/s ≤ 1 + log G`). Since `N ≫ x / log x` (Chebyshev,
`Chebyshev.pi_ge` in Mathlib), the ratio is

  ≪ 1/√(log x) + (log x)⁷/x + (log log x)⁷/√(log x) → 0.
-/
import Theorem1inLean.Counting

namespace WLJ

open Finset Real Filter Topology Asymptotics

/-- **The sieve hypothesis.** There is a constant `C` such that, for all `g, s ≥ 1` and `X ≥ 16`,

  #{q ≤ X | q, s q + g, s q + 2 g all prime} ≤ C · X · log(g s + 2)³ · (log log X)³ / (log X)³.

This is a classical consequence of Brun's pure sieve (or of Selberg's upper-bound sieve), which
gives even the stronger bound without the factor `(log log X)³`. -/
def TripleSieveBound : Prop :=
  ∃ C : ℝ, ∀ g s : ℕ, 1 ≤ g → 1 ≤ s → ∀ X : ℝ, 16 ≤ X →
    ((tripleSet g s X).card : ℝ) ≤ C * X * log (g * s + 2) ^ 3 * log (log X) ^ 3 / log X ^ 3

/-- **Theorem 1** (Conjecture 9 of the paper): the primes classified by level are rarefying among
the primes, i.e. `#{n < N | P n is classified by level} / N → 0`. -/
def Theorem1 : Prop :=
  Tendsto (fun N : ℕ => (levelCount N : ℝ) / N) atTop (𝓝 0)

/-! ### Step 1: summing the sieve bound -/

theorem sum_tripleSet_le {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ g s : ℕ, 1 ≤ g → 1 ≤ s → ∀ X : ℝ, 16 ≤ X →
      ((tripleSet g s X).card : ℝ) ≤ C * X * log (g * s + 2) ^ 3 * log (log X) ^ 3 / log X ^ 3)
    {x : ℝ} {G : ℕ} (hG1 : 1 ≤ G) (hGx : (G : ℝ) ≤ √x / 16) :
    ∑ g ∈ Icc 1 G, ∑ s ∈ Icc 1 g, ((tripleSet g s (x / s)).card : ℝ) ≤
      8 * C * x * log ((G : ℝ) ^ 2 + 2) ^ 3 * log (log x) ^ 3 / log x ^ 3 *
        (G * (1 + log G)) := by
  have hG1' : (1 : ℝ) ≤ G := by exact_mod_cast hG1
  have hsqrt : 16 ≤ √x := by linarith
  have hx0 : 0 < x := Real.sqrt_pos.mp (by linarith)
  have hxsq : √x * √x = x := Real.mul_self_sqrt hx0.le
  have hx1 : 1 < x := by nlinarith
  have hlogx : 0 < log x := Real.log_pos hx1
  have hloglogx : 0 ≤ log (log x) := by
    apply Real.log_nonneg
    rw [Real.le_log_iff_exp_le hx0]
    have := Real.exp_one_lt_d9
    nlinarith
  set K := 8 * C * x * log ((G : ℝ) ^ 2 + 2) ^ 3 * log (log x) ^ 3 / log x ^ 3 with hK
  have hK0 : 0 ≤ K := by
    have : 0 ≤ log ((G : ℝ) ^ 2 + 2) := Real.log_nonneg (by nlinarith)
    rw [hK]; positivity
  have hterm : ∀ g ∈ Icc 1 G, ∀ s ∈ Icc 1 g,
      ((tripleSet g s (x / s)).card : ℝ) ≤ K * (1 / s) := by
    intro g hg s hs
    rw [mem_Icc] at hg hs
    have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs.1
    have hsG : (s : ℝ) ≤ G := by exact_mod_cast hs.2.trans hg.2
    have hgG : (g : ℝ) ≤ G := by exact_mod_cast hg.2
    have hg0 : (0 : ℝ) ≤ g := by positivity
    have hspos : (0 : ℝ) < s := by linarith
    have hX1 : 16 * √x ≤ x / s := by
      rw [le_div_iff₀ hspos]
      nlinarith
    have hX16 : 16 ≤ x / s := by nlinarith
    have hXsq : √x ≤ x / s := by nlinarith
    have hXx : x / s ≤ x := div_le_self hx0.le hs1
    have hXpos : 0 < x / s := by linarith
    have hlogX_ge : log x / 2 ≤ log (x / s) := by
      rw [← Real.log_sqrt hx0.le]; exact Real.log_le_log (by positivity) hXsq
    have hlogX_le : log (x / s) ≤ log x := Real.log_le_log hXpos hXx
    have hlogX_one : 1 ≤ log (x / s) := by
      rw [Real.le_log_iff_exp_le hXpos]
      have := Real.exp_one_lt_d9
      linarith
    have hll0 : 0 ≤ log (log (x / s)) := Real.log_nonneg hlogX_one
    have hll : log (log (x / s)) ≤ log (log x) := Real.log_le_log (by linarith) hlogX_le
    have hgs0 : 0 ≤ log ((g : ℝ) * s + 2) := Real.log_nonneg (by nlinarith)
    have hgs : log ((g : ℝ) * s + 2) ≤ log ((G : ℝ) ^ 2 + 2) :=
      Real.log_le_log (by positivity) (by nlinarith)
    calc ((tripleSet g s (x / s)).card : ℝ)
        ≤ C * (x / s) * log ((g : ℝ) * s + 2) ^ 3 * log (log (x / s)) ^ 3 / log (x / s) ^ 3 :=
          hC g s hg.1 hs.1 (x / s) hX16
      _ ≤ C * (x / s) * log ((G : ℝ) ^ 2 + 2) ^ 3 * log (log x) ^ 3 / (log x / 2) ^ 3 := by
          have hGA : 0 ≤ log ((G : ℝ) ^ 2 + 2) := Real.log_nonneg (by nlinarith)
          gcongr
      _ = K * (1 / s) := by
          rw [hK]; field_simp; ring
  calc ∑ g ∈ Icc 1 G, ∑ s ∈ Icc 1 g, ((tripleSet g s (x / s)).card : ℝ)
      ≤ ∑ g ∈ Icc 1 G, ∑ s ∈ Icc 1 g, K * (1 / (s : ℝ)) :=
        sum_le_sum fun g hg => sum_le_sum fun s hs => hterm g hg s hs
    _ = ∑ g ∈ Icc 1 G, K * (harmonic g : ℝ) := by
        refine sum_congr rfl fun g _ => ?_
        rw [← mul_sum, harmonic_eq_sum_Icc]
        push_cast
        simp [one_div]
    _ ≤ ∑ g ∈ Icc 1 G, K * (1 + log G) := by
        refine sum_le_sum fun g hg => ?_
        rw [mem_Icc] at hg
        gcongr
        refine (harmonic_le_one_add_log g).trans ?_
        gcongr
        · exact_mod_cast hg.1
        · exact hg.2
    _ = K * (G * (1 + log G)) := by
        rw [sum_const, Nat.card_Icc, nsmul_eq_mul]
        push_cast
        ring

/-! ### Step 2: the number of primes -/

theorem primeCounting_P (N : ℕ) : Nat.primeCounting (P N) = N + 1 := by
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_succ, ← Nat.primeCounting',
    primeCounting'_P]
  simp [P_prime N]

theorem tendsto_P : Tendsto (fun N => (P N : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp P_strictMono.tendsto_atTop

/-- `N ≥ x / (2 log x)` where `x = P N`, as soon as `log (x+1) + log x ≤ x (log 2 - 1/2)`. -/
theorem N_ge {N : ℕ} (hlog : 1 ≤ log (P N : ℝ))
    (h : log ((P N : ℝ) + 1) + log (P N : ℝ) ≤ (P N : ℝ) * (log 2 - 1 / 2)) :
    (P N : ℝ) / (2 * log (P N : ℝ)) ≤ N := by
  have hpi := Chebyshev.pi_ge (P N)
  rw [primeCounting_P] at hpi
  push_cast at hpi
  have hy : 0 < log (P N : ℝ) := by linarith
  rw [div_le_iff₀ hy] at hpi
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-! ### Step 3: the final estimate -/

/-- The explicit majorant of the proportion `levelCount N / N`, as a function of `x = P N`. -/
noncomputable def majorant (C x : ℝ) : ℝ :=
  2 / √(log x) + 6 * (log x ^ 7 / x) + 3072 * C * (log (log x) ^ 7 / √(log x))

theorem tendsto_majorant (C : ℝ) : Tendsto (majorant C) atTop (𝓝 0) := by
  have h1 : Tendsto (fun x => 2 / √(log x)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_sqrt_atTop.comp tendsto_log_atTop)
  have h2 : Tendsto (fun x => log x ^ 7 / x) atTop (𝓝 0) := by
    have := tendsto_pow_log_div_mul_add_atTop 1 0 7 one_ne_zero
    simpa using this
  have h3 : Tendsto (fun y => log y ^ 7 / √y) atTop (𝓝 0) := by
    have := (isLittleO_log_rpow_rpow_atTop (7 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with y hy
    rw [Real.sqrt_eq_rpow]
    norm_cast
  have h3' := h3.comp tendsto_log_atTop
  have := (h1.add (h2.const_mul 6)).add (h3'.const_mul (3072 * C))
  rw [show (0 : ℝ) = 0 + 6 * 0 + 3072 * C * 0 by ring]
  exact this

theorem levelCount_div_le {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ g s : ℕ, 1 ≤ g → 1 ≤ s → ∀ X : ℝ, 16 ≤ X →
      ((tripleSet g s X).card : ℝ) ≤ C * X * log (g * s + 2) ^ 3 * log (log X) ^ 3 / log X ^ 3)
    {N : ℕ} (hE1 : 3 ≤ log (P N : ℝ))
    (hE2 : log (P N : ℝ) * √(log (P N : ℝ)) ≤ √(P N : ℝ) / 16)
    (hE3 : log ((P N : ℝ) + 1) + log (P N : ℝ) ≤ (P N : ℝ) * (log 2 - 1 / 2)) :
    (levelCount N : ℝ) / N ≤ majorant C (P N) := by
  set x : ℝ := (P N : ℝ) with hx
  set y := log x with hy
  have hy3 : 3 ≤ y := hE1
  have hy0 : 0 < y := by linarith
  have hsy1 : 1 ≤ √y := by rw [Real.one_le_sqrt]; linarith
  have hsyy : √y * √y = y := Real.mul_self_sqrt hy0.le
  have hsy0 : 0 < √y := by linarith
  have hx0 : 0 < x := by rw [hx]; exact_mod_cast (P_prime N).pos
  set G : ℕ := ⌊y * √y⌋₊ with hG
  have hGle : (G : ℝ) ≤ y * √y := Nat.floor_le (by positivity)
  have hGlt : y * √y < G + 1 := Nat.lt_floor_add_one _
  have hG1 : 1 ≤ G := Nat.le_floor (by push_cast; nlinarith)
  have hG1' : (1 : ℝ) ≤ G := by exact_mod_cast hG1
  have hGx : (G : ℝ) ≤ √x / 16 := hGle.trans hE2
  -- the counting bound, in `ℝ`
  have hcount : (levelCount N : ℝ) ≤ x / (G + 1) + ((G : ℝ) ^ 4 + G + 1) +
      8 * C * x * log ((G : ℝ) ^ 2 + 2) ^ 3 * log y ^ 3 / y ^ 3 * (G * (1 + log G)) := by
    have h := levelCount_le N G
    have h' : (levelCount N : ℝ) ≤ ((P N / (G + 1) : ℕ) : ℝ) + ((G : ℝ) ^ 4 + G + 1) +
        ∑ g ∈ Icc 1 G, ∑ s ∈ Icc 1 g, ((tripleSet g s ((P N : ℝ) / s)).card : ℝ) := by
      exact_mod_cast h
    have hdiv : ((P N / (G + 1) : ℕ) : ℝ) ≤ x / (G + 1) := by
      rw [hx]; exact_mod_cast Nat.cast_div_le
    have hsum := sum_tripleSet_le hC0 hC hG1 hGx
    linarith
  -- `N ≥ x / (2 y)`
  have hN : x / (2 * y) ≤ N := N_ge (by linarith) hE3
  have hxy : 0 < x / (2 * y) := by positivity
  have hcount0 : (0 : ℝ) ≤ levelCount N := by positivity
  -- bounds on the pieces
  have hlogy : 1 ≤ log y := by
    rw [Real.le_log_iff_exp_le hy0]
    have := Real.exp_one_lt_d9
    linarith
  have hlogG : log G ≤ log y + log y / 2 := by
    calc log G ≤ log (y * √y) := Real.log_le_log (by positivity) hGle
      _ = log y + log y / 2 := by
        rw [Real.log_mul hy0.ne' hsy0.ne', Real.log_sqrt hy0.le]
  have hlogG0 : 0 ≤ log (G : ℝ) := Real.log_nonneg hG1'
  have hA : log ((G : ℝ) ^ 2 + 2) ≤ 4 * log y := by
    rw [← Real.log_rpow hy0]
    apply Real.log_le_log (by positivity)
    have hG2 : (G : ℝ) ^ 2 ≤ y ^ 3 := by
      calc (G : ℝ) ^ 2 ≤ (y * √y) ^ 2 := by gcongr
        _ = y ^ 3 := by rw [mul_pow, Real.sq_sqrt hy0.le]; ring
    have : y ^ 3 + 2 ≤ y ^ (4 : ℝ) := by
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      nlinarith [pow_pos hy0 3]
    linarith
  have hA0 : 0 ≤ log ((G : ℝ) ^ 2 + 2) := Real.log_nonneg (by nlinarith)
  have hG4 : (G : ℝ) ^ 4 + G + 1 ≤ 3 * y ^ 6 := by
    have hGy : (G : ℝ) ≤ y ^ 2 := by
      calc (G : ℝ) ≤ y * √y := hGle
        _ ≤ y * y := by gcongr; nlinarith
        _ = y ^ 2 := by ring
    have : (G : ℝ) ^ 4 ≤ y ^ 6 := by
      calc (G : ℝ) ^ 4 ≤ (y * √y) ^ 4 := by gcongr
        _ = y ^ 6 := by
          rw [mul_pow, show √y ^ 4 = (√y * √y) ^ 2 by ring, hsyy]; ring
    have : y ^ 2 ≤ y ^ 6 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have : (1 : ℝ) ≤ y ^ 6 := one_le_pow₀ (by linarith)
    linarith
  calc (levelCount N : ℝ) / N
      ≤ (levelCount N : ℝ) / (x / (2 * y)) := div_le_div_of_nonneg_left hcount0 hxy hN
    _ = (levelCount N : ℝ) * (2 * y / x) := by field_simp
    _ ≤ (x / (G + 1) + ((G : ℝ) ^ 4 + G + 1) +
          8 * C * x * log ((G : ℝ) ^ 2 + 2) ^ 3 * log y ^ 3 / y ^ 3 * (G * (1 + log G))) *
          (2 * y / x) := by gcongr
    _ = 2 * y / (G + 1) + ((G : ℝ) ^ 4 + G + 1) * 2 * y / x +
          16 * C * G * (1 + log G) * log ((G : ℝ) ^ 2 + 2) ^ 3 * log y ^ 3 / y ^ 2 := by
        field_simp
        ring
    _ ≤ 2 / √y + 6 * (y ^ 7 / x) + 3072 * C * (log y ^ 7 / √y) := by
        gcongr ?_ + ?_ + ?_
        · rw [div_le_div_iff₀ (by positivity) hsy0]
          nlinarith
        · rw [div_le_iff₀ hx0, mul_div_assoc', div_mul_cancel₀ _ hx0.ne']
          nlinarith [pow_pos hy0 6]
        · calc 16 * C * G * (1 + log G) * log ((G : ℝ) ^ 2 + 2) ^ 3 * log y ^ 3 / y ^ 2
              ≤ 16 * C * (y * √y) * (3 * log y) * (4 * log y) ^ 3 * log y ^ 3 / y ^ 2 := by
                gcongr
                linarith
            _ = 3072 * C * (log y ^ 7 / √y) := by
                field_simp
                rw [Real.sq_sqrt hy0.le]
                ring
    _ = majorant C x := by simp [majorant, hy]

/-- **Theorem 1, conditional on the sieve bound.** If `TripleSieveBound` holds, then the primes
classified by level have density zero among the primes. -/
theorem theorem1_of_sieve (H : TripleSieveBound) : Theorem1 := by
  obtain ⟨C₀, hC₀⟩ := H
  set C := max C₀ 0 with hCdef
  have hC0 : 0 ≤ C := le_max_right _ _
  have hC : ∀ g s : ℕ, 1 ≤ g → 1 ≤ s → ∀ X : ℝ, 16 ≤ X →
      ((tripleSet g s X).card : ℝ) ≤ C * X * log (g * s + 2) ^ 3 * log (log X) ^ 3 / log X ^ 3 := by
    intro g s hg hs X hX
    refine (hC₀ g s hg hs X hX).trans ?_
    have hX0 : 0 < X := by linarith
    have hlogX : 1 ≤ log X := by
      rw [Real.le_log_iff_exp_le hX0]
      have := Real.exp_one_lt_d9
      linarith
    have : 0 ≤ log (log X) := Real.log_nonneg hlogX
    have : 0 ≤ log ((g : ℝ) * s + 2) := Real.log_nonneg (by
      have : (0 : ℝ) ≤ g * s := by positivity
      linarith)
    gcongr
    exact le_max_left _ _
  -- the three eventual conditions on `x`
  have hE1 : ∀ᶠ x : ℝ in atTop, 3 ≤ log x := tendsto_log_atTop.eventually_ge_atTop 3
  have hE2 : ∀ᶠ x : ℝ in atTop, log x * √(log x) ≤ √x / 16 := by
    have h := (isLittleO_log_rpow_rpow_atTop (3 / 2 : ℝ)
      (by norm_num : (0 : ℝ) < 1 / 2)).bound (by norm_num : (0 : ℝ) < 1 / 16)
    filter_upwards [h, hE1, eventually_gt_atTop (0 : ℝ)] with x hx hx3 hx0
    have hl0 : 0 < log x := by linarith
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)] at hx
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hl0, Real.rpow_one,
      ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hx
    linarith
  have hE3 : ∀ᶠ x : ℝ in atTop, log (x + 1) + log x ≤ x * (log 2 - 1 / 2) := by
    have h := isLittleO_log_id_atTop.bound (by norm_num : (0 : ℝ) < 1 / 20)
    filter_upwards [h, eventually_ge_atTop (20 : ℝ)] with x hx hx20
    have hx0 : 0 < x := by linarith
    rw [Real.norm_of_nonneg (Real.log_nonneg (by linarith)), id, Real.norm_of_nonneg hx0.le] at hx
    have h2 : log (x + 1) ≤ log 2 + log x := by
      rw [← Real.log_mul (by norm_num) hx0.ne']
      exact Real.log_le_log (by linarith) (by linarith)
    have := Real.log_two_gt_d9
    have := Real.log_two_lt_d9
    nlinarith
  have hev : ∀ᶠ N : ℕ in atTop, (levelCount N : ℝ) / N ≤ majorant C (P N) := by
    filter_upwards [tendsto_P.eventually hE1, tendsto_P.eventually hE2,
      tendsto_P.eventually hE3] with N h1 h2 h3
    exact levelCount_div_le hC0 hC h1 h2 h3
  exact squeeze_zero' (Eventually.of_forall fun N => by positivity) hev
    ((tendsto_majorant C).comp tendsto_P)

end WLJ
