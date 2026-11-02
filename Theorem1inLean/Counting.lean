/-
# The combinatorial counting bound

For every `N` and every `G ≥ 0`, writing `x = P N`,

  #{n < N | P n classified by level}
      ≤ x / (G + 1) + (G⁴ + G + 1) + ∑_{1 ≤ g ≤ G} ∑_{1 ≤ s ≤ g} #{q ≤ x/s | q, s q + g, s q + 2 g prime}.

* The first term counts the `n` with a large gap `g_n > G` (the gaps add up to `< x`).
* The second term counts the `n` with `P n ≤ G⁴ + G`.
* For the remaining `n`, the structural lemma gives `l_n = s q` with `q` prime and `s ≤ g_n`,
  so that `P n = s q + g_n` and `P (n+1) = s q + 2 g_n` are prime: `n` is recorded by a prime
  triple.
-/
import Theorem1inLean.Primes

namespace WLJ

open Finset

/-- `{q ≤ X | q, s q + g, s q + 2 g are all prime}`. -/
noncomputable def tripleSet (g s : ℕ) (X : ℝ) : Finset ℕ :=
  (range (⌊X⌋₊ + 1)).filter (fun q => q.Prime ∧ (s * q + g).Prime ∧ (s * q + 2 * g).Prime)

/-- The number of `n < N` such that the prime `P n` is classified by level. -/
noncomputable def levelCount (N : ℕ) : ℕ := ((range N).filter (ClassifiedByLevel P)).card

theorem levelCount_le (N G : ℕ) :
    levelCount N ≤ P N / (G + 1) + (G ^ 4 + G + 1) +
      ∑ g ∈ Icc 1 G, ∑ s ∈ Icc 1 g, (tripleSet g s ((P N : ℝ) / s)).card := by
  classical
  set S := (range N).filter (ClassifiedByLevel P) with hS
  set A := S.filter (fun n => G < jump P n)
  set B := S.filter (fun n => P n ≤ G ^ 4 + G)
  set C := S.filter (fun n => jump P n ≤ G ∧ G ^ 4 + G < P n)
  have hsub : S ⊆ A ∪ B ∪ C := by
    intro n hn
    simp only [A, B, C, mem_union, mem_filter]
    by_cases h1 : G < jump P n
    · exact Or.inl (Or.inl ⟨hn, h1⟩)
    by_cases h2 : P n ≤ G ^ 4 + G
    · exact Or.inl (Or.inr ⟨hn, h2⟩)
    exact Or.inr ⟨hn, by omega, by omega⟩
  have hS_le : S.card ≤ A.card + B.card + C.card :=
    (card_le_card hsub).trans ((card_union_le _ _).trans (by
      have := card_union_le A B; omega))
  -- Large gaps.
  have hA : A.card ≤ P N / (G + 1) := by
    rw [Nat.le_div_iff_mul_le (Nat.succ_pos G)]
    calc A.card * (G + 1) = A.card • (G + 1) := by rw [smul_eq_mul]
      _ ≤ ∑ n ∈ A, jump P n := card_nsmul_le_sum _ _ _ (fun n hn => by
          simp only [A, mem_filter] at hn; omega)
      _ ≤ ∑ n ∈ range N, jump P n :=
          sum_le_sum_of_subset (fun n hn => by
            simp only [A, S, mem_filter] at hn; exact hn.1.1)
      _ = P N - P 0 := sum_jump_P N
      _ ≤ P N := Nat.sub_le _ _
  -- Small primes.
  have hB : B.card ≤ G ^ 4 + G + 1 := by
    have := card_le_card_of_injOn (s := B) (t := range (G ^ 4 + G + 1)) P
      (fun n hn => by
        simp only [B, coe_filter, Set.mem_ofPred_eq] at hn
        simp only [coe_range, Set.mem_Iio]; omega)
      (P_strictMono.injective.injOn)
    simpa using this
  -- The rest is controlled by prime triples.
  have hC : C.card ≤ ∑ g ∈ Icc 1 G, ∑ s ∈ Icc 1 g, (tripleSet g s ((P N : ℝ) / s)).card := by
    set U := (Icc 1 G).biUnion (fun g => (Icc 1 g).biUnion
      (fun s => (tripleSet g s ((P N : ℝ) / s)).image (fun q => s * q + g)))
    have hmaps : Set.MapsTo P C U := by
      intro n hn
      simp only [C, S, coe_filter, mem_filter, mem_range, Set.mem_ofPred_eq] at hn
      obtain ⟨⟨hnN, hlev⟩, hgG, hPG⟩ := hn
      have hl := lval_ne_zero_of_classifiedByLevel hlev
      have hPeq := P_eq_lval_add_jump hl
      have hg1 := jump_P_pos n
      have h4 : jump P n ^ 4 ≤ lval P n := by
        have : jump P n ^ 4 ≤ G ^ 4 := Nat.pow_le_pow_left hgG 4
        omega
      obtain ⟨s, q, hq, hsg, hlsq⟩ := lval_eq_mul_prime_of_classifiedByLevel hlev hg1 h4
      have hs1 : 1 ≤ s := by
        rcases Nat.eq_zero_or_pos s with h | h
        · rw [h, zero_mul] at hlsq; exact absurd hlsq hl
        · exact h
      have hPN : P n < P N := P_strictMono hnN
      simp only [U, coe_biUnion, coe_Icc, Set.mem_iUnion, coe_image, Set.mem_image,
        Set.mem_Icc, exists_prop]
      refine ⟨jump P n, ⟨hg1, hgG⟩, s, ⟨hs1, hsg⟩, q, ?_, by rw [hPeq, hlsq]⟩
      simp only [tripleSet, coe_filter, mem_range, Set.mem_ofPred_eq]
      refine ⟨?_, hq, ?_, ?_⟩
      · rw [Nat.lt_add_one_iff]
        apply Nat.le_floor
        rw [le_div_iff₀ (by exact_mod_cast hs1)]
        have : q * s ≤ P N := by rw [mul_comm]; omega
        exact_mod_cast this
      · rw [← hlsq, ← hPeq]; exact P_prime n
      · have : s * q + 2 * jump P n = P (n + 1) := by rw [P_succ_eq, hPeq, hlsq]; ring
        rw [this]; exact P_prime (n + 1)
    calc C.card ≤ U.card := card_le_card_of_injOn P hmaps P_strictMono.injective.injOn
      _ ≤ ∑ g ∈ Icc 1 G, ((Icc 1 g).biUnion
            (fun s => (tripleSet g s ((P N : ℝ) / s)).image (fun q => s * q + g))).card :=
          card_biUnion_le
      _ ≤ _ := sum_le_sum (fun g _ => card_biUnion_le.trans
            (sum_le_sum (fun s _ => card_image_le)))
  unfold levelCount
  rw [← hS]
  omega

end WLJ
