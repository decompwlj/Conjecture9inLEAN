/-
# Brun's pure sieve for the prime triples `q, s q + g, s q + 2 g`

Main result (`tripleCountN_le`): for every `z, k, M`, writing
`P = {p < z prime | p ∤ 2 g s}`,

  #{q < M | q, sq+g, sq+2g prime}
    ≤ z + M · (∏_{p ∈ P} (1 - 3/p) + e^{-(2k+1)} · exp(3e ∑_{p ∈ P} 1/p)) + (3 (z+1))^{2k}.

Ingredients:
* the Bonferroni inequalities (truncated inclusion–exclusion at an even level is an upper bound),
* the count in residue classes from `RootCount.lean`,
* Rankin's trick for the tail of the inclusion–exclusion sum.
-/
import Theorem1inLean.Sieve.RootCount

namespace WLJ.Sieve

open Finset Real

/-! ### Combinatorial lemmas -/

/-- Bonferroni: truncated alternating binomial sums at an even level dominate `[n = 0]`. -/
theorem bonferroni (n k : ℕ) :
    (if n = 0 then (1 : ℝ) else 0) ≤ ∑ j ∈ range (2 * k + 1), (-1 : ℝ) ^ j * n.choose j := by
  rcases n with _ | n
  · rw [sum_range_succ']
    simp
  · have h := Int.alternating_sum_range_choose_eq_choose (n := n) (m := 2 * k)
    have h' : ∑ j ∈ range (2 * k + 1), (-1 : ℝ) ^ j * ((n + 1).choose j : ℝ) =
        (n.choose (2 * k) : ℝ) := by
      have := congrArg (fun z : ℤ => (z : ℝ)) h
      push_cast at this
      rw [this, pow_mul]
      simp
    simp only [Nat.succ_ne_zero, ite_false]
    rw [h']
    positivity

/-- Grouping a sum over subsets of size `≤ m` according to the size. -/
theorem sum_powerset_filter_card_le {α : Type*} (A : Finset α) (m : ℕ) (g : ℕ → ℝ) :
    ∑ B ∈ A.powerset.filter (fun B => B.card ≤ m), g B.card =
      ∑ j ∈ range (m + 1), (A.card.choose j : ℝ) * g j := by
  rw [sum_filter, sum_powerset_apply_card (fun j => if j ≤ m then g j else 0)]
  set n := A.card
  set N := max n m
  have h1 : ∑ j ∈ range (n + 1), (n.choose j) • (if j ≤ m then g j else 0) =
      ∑ j ∈ range (N + 1), (n.choose j : ℝ) * (if j ≤ m then g j else 0) := by
    simp only [nsmul_eq_mul]
    apply sum_subset
    · intro j hj; simp only [mem_range] at hj ⊢; omega
    · intro j _ hj
      simp only [mem_range, not_lt] at hj
      rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
  have h2 : ∑ j ∈ range (m + 1), (n.choose j : ℝ) * g j =
      ∑ j ∈ range (N + 1), (n.choose j : ℝ) * (if j ≤ m then g j else 0) := by
    have h3 : ∑ j ∈ range (m + 1), (n.choose j : ℝ) * g j =
        ∑ j ∈ range (m + 1), (n.choose j : ℝ) * (if j ≤ m then g j else 0) := by
      apply sum_congr rfl
      intro j hj
      simp only [mem_range] at hj
      rw [ite_eq_left_iff.mpr (fun h => absurd (by omega) h)]
    rw [h3]
    apply sum_subset
    · intro j hj; simp only [mem_range] at hj ⊢; omega
    · intro j _ hj
      simp only [mem_range, not_lt] at hj
      rw [ite_eq_right_iff.mpr (fun h => absurd h (by omega))]; simp
  rw [h1, h2]

theorem sum_powerset_subset_eq {α : Type*} [DecidableEq α] {A P : Finset α} (hAP : A ⊆ P)
    (m : ℕ) (h : Finset α → ℝ) :
    ∑ B ∈ A.powerset.filter (fun B => B.card ≤ m), h B =
      ∑ B ∈ P.powerset.filter (fun B => B.card ≤ m), if B ⊆ A then h B else 0 := by
  rw [← sum_filter]
  congr 1
  ext B
  simp only [mem_filter, mem_powerset]
  constructor
  · rintro ⟨hBA, hc⟩; exact ⟨⟨hBA.trans hAP, hc⟩, hBA⟩
  · rintro ⟨⟨_, hc⟩, hBA⟩; exact ⟨hBA, hc⟩

/-! ### The sifted set and Bonferroni -/

/-- The integers `q < M` such that `F(q)` has no prime factor in `P`. -/
def siftSet (g s : ℕ) (P : Finset ℕ) (M : ℕ) : Finset ℕ :=
  (range M).filter (fun q => ∀ p ∈ P, ¬ p ∣ F g s q)

/-- The number of `q < M` with `(∏_{p ∈ B} p) ∣ F(q)`. -/
def mult (g s : ℕ) (B : Finset ℕ) (M : ℕ) : ℕ :=
  ((range M).filter (fun q => (∏ p ∈ B, p) ∣ F g s q)).card

theorem prod_dvd_iff {g s q : ℕ} {B : Finset ℕ} (hB : ∀ p ∈ B, p.Prime) :
    (∏ p ∈ B, p) ∣ F g s q ↔ ∀ p ∈ B, p ∣ F g s q := by
  constructor
  · intro h p hp; exact (dvd_prod_of_mem _ hp).trans h
  · intro h; exact Finset.prod_primes_dvd _ (fun p hp => (hB p hp).prime) h

theorem card_siftSet_le (g s : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (k M : ℕ) :
    ((siftSet g s P M).card : ℝ) ≤
      ∑ B ∈ P.powerset.filter (fun B => B.card ≤ 2 * k), (-1 : ℝ) ^ B.card * mult g s B M := by
  classical
  set A : ℕ → Finset ℕ := fun q => P.filter (fun p => p ∣ F g s q) with hA
  have hAP : ∀ q, A q ⊆ P := fun q => filter_subset _ _
  calc ((siftSet g s P M).card : ℝ)
      = ∑ q ∈ range M, (if (A q).card = 0 then (1 : ℝ) else 0) := by
        unfold siftSet
        rw [natCast_card_filter]
        apply sum_congr rfl
        intro q _
        congr 1
        simp only [A, card_eq_zero, filter_eq_empty_iff]
    _ ≤ ∑ q ∈ range M, ∑ j ∈ range (2 * k + 1), (-1 : ℝ) ^ j * ((A q).card.choose j) :=
        sum_le_sum fun q _ => bonferroni _ _
    _ = ∑ q ∈ range M, ∑ B ∈ P.powerset.filter (fun B => B.card ≤ 2 * k),
          (if B ⊆ A q then (-1 : ℝ) ^ B.card else 0) := by
        apply sum_congr rfl
        intro q _
        rw [← sum_powerset_subset_eq (hAP q) (2 * k) (fun B => (-1 : ℝ) ^ B.card),
          sum_powerset_filter_card_le (A q) (2 * k) (fun j => (-1 : ℝ) ^ j)]
        apply sum_congr rfl; intro j _; ring
    _ = ∑ B ∈ P.powerset.filter (fun B => B.card ≤ 2 * k),
          ∑ q ∈ range M, (if B ⊆ A q then (-1 : ℝ) ^ B.card else 0) := sum_comm
    _ = ∑ B ∈ P.powerset.filter (fun B => B.card ≤ 2 * k), (-1 : ℝ) ^ B.card * mult g s B M := by
        apply sum_congr rfl
        intro B hB
        simp only [mem_filter, mem_powerset] at hB
        have hBp : ∀ p ∈ B, p.Prime := fun p hp => hP p (hB.1 hp)
        rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
        congr 2
        unfold mult
        congr 1
        ext q
        simp only [mem_filter, mem_range, A, prod_dvd_iff hBp]
        constructor
        · rintro ⟨hq, hsub⟩; exact ⟨hq, fun p hp => (mem_filter.mp (hsub hp)).2⟩
        · rintro ⟨hq, hdiv⟩; exact ⟨hq, fun p hp => mem_filter.mpr ⟨hB.1 hp, hdiv p hp⟩⟩

/-! ### Main term and Rankin's trick -/

theorem prod_one_sub_eq (P : Finset ℕ) (f : ℕ → ℝ) :
    ∏ p ∈ P, (1 - f p) = ∑ B ∈ P.powerset, (-1 : ℝ) ^ B.card * ∏ p ∈ B, f p := by
  have := prod_one_add (f := fun p => -f p) P
  simp only [← sub_eq_add_neg] at this
  rw [this]
  apply sum_congr rfl
  intro B _
  rw [prod_neg]

theorem truncated_le (P : Finset ℕ) (f : ℕ → ℝ) (hf : ∀ p, 0 ≤ f p) (k : ℕ) :
    ∑ B ∈ P.powerset.filter (fun B => B.card ≤ 2 * k), (-1 : ℝ) ^ B.card * ∏ p ∈ B, f p ≤
      ∏ p ∈ P, (1 - f p) + exp (-(2 * k + 1 : ℝ)) * exp (exp 1 * ∑ p ∈ P, f p) := by
  have hfull := prod_one_sub_eq P f
  rw [← sum_filter_add_sum_filter_not P.powerset (fun B => B.card ≤ 2 * k)] at hfull
  set R := P.powerset.filter (fun B => ¬ B.card ≤ 2 * k)
  have hrest : |∑ B ∈ R, (-1 : ℝ) ^ B.card * ∏ p ∈ B, f p| ≤
      exp (-(2 * k + 1 : ℝ)) * exp (exp 1 * ∑ p ∈ P, f p) := by
    calc |∑ B ∈ R, (-1 : ℝ) ^ B.card * ∏ p ∈ B, f p|
        ≤ ∑ B ∈ R, |(-1 : ℝ) ^ B.card * ∏ p ∈ B, f p| := abs_sum_le_sum_abs _ _
      _ = ∑ B ∈ R, ∏ p ∈ B, f p := by
          apply sum_congr rfl; intro B _
          rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
            abs_of_nonneg (prod_nonneg fun p _ => hf p)]
      _ ≤ ∑ B ∈ R, exp (B.card - (2 * k + 1 : ℝ)) * ∏ p ∈ B, f p := by
          apply sum_le_sum
          intro B hB
          simp only [R, mem_filter, not_le] at hB
          have : (1 : ℝ) ≤ exp (B.card - (2 * k + 1 : ℝ)) := by
            rw [Real.one_le_exp_iff]
            have : (2 * k + 1 : ℝ) ≤ B.card := by exact_mod_cast hB.2
            linarith
          have h0 : 0 ≤ ∏ p ∈ B, f p := prod_nonneg fun p _ => hf p
          nlinarith
      _ ≤ ∑ B ∈ P.powerset, exp (B.card - (2 * k + 1 : ℝ)) * ∏ p ∈ B, f p := by
          apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          intro B _ _; exact mul_nonneg (exp_pos _).le (prod_nonneg fun p _ => hf p)
      _ = exp (-(2 * k + 1 : ℝ)) * ∑ B ∈ P.powerset, ∏ p ∈ B, (exp 1 * f p) := by
          rw [mul_sum]
          apply sum_congr rfl; intro B _
          rw [prod_mul_distrib, prod_const, ← Real.exp_nat_mul, ← mul_assoc, ← Real.exp_add]
          ring_nf
      _ = exp (-(2 * k + 1 : ℝ)) * ∏ p ∈ P, (1 + exp 1 * f p) := by rw [prod_one_add]
      _ ≤ exp (-(2 * k + 1 : ℝ)) * exp (∑ p ∈ P, exp 1 * f p) := by
          gcongr
          exact Real.prod_one_add_le_exp_sum P (fun p => mul_nonneg (exp_pos 1).le (hf p))
      _ = exp (-(2 * k + 1 : ℝ)) * exp (exp 1 * ∑ p ∈ P, f p) := by rw [mul_sum]
  have := (abs_le.mp hrest).1
  linarith

/-! ### The error term -/

theorem sum_three_pow_le (P : Finset ℕ) (m : ℕ) :
    ∑ B ∈ P.powerset.filter (fun B => B.card ≤ m), (3 : ℝ) ^ B.card ≤ (3 * (P.card + 1)) ^ m := by
  rw [sum_powerset_filter_card_le P m (fun j => (3 : ℝ) ^ j)]
  set n := P.card
  calc ∑ j ∈ range (m + 1), (n.choose j : ℝ) * 3 ^ j
      ≤ ∑ j ∈ range (m + 1), (m.choose j : ℝ) * (3 * n) ^ j * 1 ^ (m - j) := by
        apply sum_le_sum
        intro j hj
        simp only [mem_range] at hj
        have h1 : (n.choose j : ℝ) ≤ n ^ j := by exact_mod_cast Nat.choose_le_pow n j
        have h2 : (1 : ℝ) ≤ m.choose j := by exact_mod_cast Nat.choose_pos (by omega)
        rw [one_pow, mul_one, mul_pow]
        have h3 : (0 : ℝ) ≤ 3 ^ j := by positivity
        have h4 : (0 : ℝ) ≤ (n : ℝ) ^ j := by positivity
        have h5 : (n.choose j : ℝ) ≤ m.choose j * n ^ j := h1.trans (le_mul_of_one_le_left h4 h2)
        calc (n.choose j : ℝ) * 3 ^ j ≤ (m.choose j * n ^ j) * 3 ^ j :=
              mul_le_mul_of_nonneg_right h5 h3
          _ = m.choose j * (3 ^ j * n ^ j) := by ring
    _ = (3 * n + 1) ^ m := by rw [add_pow]; apply sum_congr rfl; intro j _; ring
    _ ≤ (3 * (n + 1)) ^ m := by gcongr; linarith

/-! ### Brun's sieve -/

theorem card_siftSet_le_brun (g s : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ ¬ p ∣ 2 * g * s)
    (k M : ℕ) :
    ((siftSet g s P M).card : ℝ) ≤
      M * (∏ p ∈ P, (1 - 3 / (p : ℝ)) +
        exp (-(2 * k + 1 : ℝ)) * exp (exp 1 * ∑ p ∈ P, 3 / (p : ℝ))) +
      (3 * (P.card + 1)) ^ (2 * k) := by
  set 𝓑 := P.powerset.filter (fun B => B.card ≤ 2 * k)
  have hB : ∀ B ∈ 𝓑, (-1 : ℝ) ^ B.card * mult g s B M ≤
      M * ((-1 : ℝ) ^ B.card * ∏ p ∈ B, (3 / (p : ℝ))) + 3 ^ B.card := by
    intro B hB
    simp only [𝓑, mem_filter, mem_powerset] at hB
    have hBp : ∀ p ∈ B, p.Prime ∧ ¬ p ∣ 2 * g * s := fun p hp => hP p (hB.1 hp)
    have hprod0 : (∏ p ∈ B, p) ≠ 0 := prod_ne_zero_iff.mpr fun p hp => (hBp p hp).1.ne_zero
    have hest := abs_card_dvd_sub_le (g := g) (s := s) hprod0 M
    rw [rootCount_prod B hBp] at hest
    have hmain : (M : ℝ) * ((3 ^ B.card : ℕ) : ℝ) / ((∏ p ∈ B, p : ℕ) : ℝ) =
        M * ∏ p ∈ B, (3 / (p : ℝ)) := by
      rw [prod_div_distrib, prod_const]; push_cast; ring
    rw [hmain] at hest
    unfold mult
    push_cast at hest ⊢
    have hsign : (-1 : ℝ) ^ B.card = 1 ∨ (-1 : ℝ) ^ B.card = -1 := neg_one_pow_eq_or ℝ _
    rw [abs_le] at hest
    obtain ⟨hl, hr⟩ := hest
    rcases hsign with h | h <;> rw [h] <;> linarith
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  calc ((siftSet g s P M).card : ℝ)
      ≤ ∑ B ∈ 𝓑, (-1 : ℝ) ^ B.card * mult g s B M :=
        card_siftSet_le g s P (fun p hp => (hP p hp).1) k M
    _ ≤ ∑ B ∈ 𝓑, (M * ((-1 : ℝ) ^ B.card * ∏ p ∈ B, (3 / (p : ℝ))) + 3 ^ B.card) :=
        sum_le_sum hB
    _ = M * ∑ B ∈ 𝓑, (-1 : ℝ) ^ B.card * ∏ p ∈ B, (3 / (p : ℝ)) +
          ∑ B ∈ 𝓑, (3 : ℝ) ^ B.card := by rw [sum_add_distrib, mul_sum]
    _ ≤ M * (∏ p ∈ P, (1 - 3 / (p : ℝ)) +
          exp (-(2 * k + 1 : ℝ)) * exp (exp 1 * ∑ p ∈ P, 3 / (p : ℝ))) +
        (3 * (P.card + 1)) ^ (2 * k) := by
        gcongr
        · exact truncated_le P (fun p => 3 / (p : ℝ)) (fun p => by positivity) k
        · exact sum_three_pow_le P (2 * k)

/-! ### From the sifted set to prime triples -/

/-- `{q < M | q, s q + g, s q + 2 g all prime}`. -/
def tripleSetN (g s M : ℕ) : Finset ℕ :=
  (range M).filter (fun q => q.Prime ∧ (s * q + g).Prime ∧ (s * q + 2 * g).Prime)

/-- The sieving primes: `p < z`, `p ∤ 2 g s`. -/
def sievePrimes (g s z : ℕ) : Finset ℕ := z.primesBelow.filter (fun p => ¬ p ∣ 2 * g * s)

theorem sievePrimes_spec {g s z : ℕ} : ∀ p ∈ sievePrimes g s z, p.Prime ∧ ¬ p ∣ 2 * g * s := by
  intro p hp
  simp only [sievePrimes, mem_filter, Nat.mem_primesBelow] at hp
  exact ⟨hp.1.2, hp.2⟩

theorem card_sievePrimes_le (g s z : ℕ) : (sievePrimes g s z).card ≤ z := by
  calc (sievePrimes g s z).card ≤ z.primesBelow.card := card_filter_le _ _
    _ ≤ (range z).card := card_le_card (filter_subset _ _)
    _ = z := card_range z

theorem card_tripleSetN_le_sift {g s : ℕ} (hs : 1 ≤ s) (z M : ℕ) :
    (tripleSetN g s M).card ≤ z + (siftSet g s (sievePrimes g s z) M).card := by
  classical
  have hsub : tripleSetN g s M ⊆ range z ∪ siftSet g s (sievePrimes g s z) M := by
    intro q hq
    simp only [tripleSetN, mem_filter, mem_range] at hq
    obtain ⟨hqM, hq1, hq2, hq3⟩ := hq
    rw [mem_union]
    by_cases hqz : q < z
    · exact Or.inl (mem_range.mpr hqz)
    right
    simp only [siftSet, mem_filter, mem_range]
    refine ⟨hqM, fun p hp hdvd => ?_⟩
    have hpP := sievePrimes_spec p hp
    simp only [sievePrimes, mem_filter, Nat.mem_primesBelow] at hp
    have hpz := hp.1.1
    have hge : ∀ r : ℕ, r.Prime → q ≤ r → p ∣ r → False := fun r hr hqr hpr => by
      have := (Nat.prime_dvd_prime_iff_eq hpP.1 hr).mp hpr
      omega
    unfold F at hdvd
    rcases (Nat.Prime.dvd_mul hpP.1).mp hdvd with h | h
    · rcases (Nat.Prime.dvd_mul hpP.1).mp h with h' | h'
      · exact hge q hq1 le_rfl h'
      · exact hge _ hq2 (by nlinarith) h'
    · exact hge _ hq3 (by nlinarith) h
  calc (tripleSetN g s M).card ≤ (range z ∪ siftSet g s (sievePrimes g s z) M).card :=
        card_le_card hsub
    _ ≤ (range z).card + (siftSet g s (sievePrimes g s z) M).card := card_union_le _ _
    _ = z + (siftSet g s (sievePrimes g s z) M).card := by rw [card_range]

/-- **Brun's sieve bound for prime triples.** -/
theorem card_tripleSetN_le {g s : ℕ} (hs : 1 ≤ s) (z k M : ℕ) :
    ((tripleSetN g s M).card : ℝ) ≤
      z + M * (∏ p ∈ sievePrimes g s z, (1 - 3 / (p : ℝ)) +
        exp (-(2 * k + 1 : ℝ)) * exp (3 * exp 1 * ∑ p ∈ sievePrimes g s z, 1 / (p : ℝ))) +
      (3 * (z + 1)) ^ (2 * k) := by
  have h1 : ((tripleSetN g s M).card : ℝ) ≤ z + (siftSet g s (sievePrimes g s z) M).card := by
    exact_mod_cast card_tripleSetN_le_sift hs z M
  have h2 := card_siftSet_le_brun g s (sievePrimes g s z) sievePrimes_spec k M
  have h3 : ((sievePrimes g s z).card : ℝ) ≤ z := by exact_mod_cast card_sievePrimes_le g s z
  have h4 : (3 * ((sievePrimes g s z).card + 1 : ℝ)) ^ (2 * k) ≤ (3 * (z + 1)) ^ (2 * k) := by
    gcongr
  have h5 : exp 1 * ∑ p ∈ sievePrimes g s z, 3 / (p : ℝ) =
      3 * exp 1 * ∑ p ∈ sievePrimes g s z, 1 / (p : ℝ) := by
    rw [mul_sum, mul_sum]; apply sum_congr rfl; intro p _; ring
  rw [h5] at h2
  linarith

end WLJ.Sieve
