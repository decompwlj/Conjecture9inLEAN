/-
# Counting roots of `F(q) = q (s q + g) (s q + 2 g)` modulo products of primes

* `rootCount g s m = #{r < m | m ∣ F(r)}`.
* It is multiplicative on coprime moduli (Chinese remainder theorem): `rootCount_mul`.
* For a prime `p ∤ 2 g s` it equals `3`: `rootCount_prime`.
* Hence `rootCount (∏_{p ∈ B} p) = 3 ^ |B|` for a set `B` of such primes: `rootCount_prod`.
* The number of `q < M` with `m ∣ F(q)` is `M · rootCount m / m` up to an error at most
  `rootCount m`: `abs_card_dvd_sub_le`.
-/
import Mathlib

namespace WLJ.Sieve

open Finset

/-- The polynomial `F(q) = q (s q + g) (s q + 2 g)`. -/
def F (g s q : ℕ) : ℕ := q * (s * q + g) * (s * q + 2 * g)

theorem F_modEq {g s a b m : ℕ} (h : a ≡ b [MOD m]) : F g s a ≡ F g s b [MOD m] := by
  unfold F
  have h1 : s * a + g ≡ s * b + g [MOD m] := (h.mul_left s).add_right g
  have h2 : s * a + 2 * g ≡ s * b + 2 * g [MOD m] := (h.mul_left s).add_right _
  exact (h.mul h1).mul h2

theorem dvd_F_iff_mod {g s m q : ℕ} : m ∣ F g s q ↔ m ∣ F g s (q % m) :=
  (F_modEq (Nat.mod_modEq q m).symm).dvd_iff dvd_rfl

/-- The number of roots of `F` modulo `m`. -/
def rootCount (g s m : ℕ) : ℕ := ((range m).filter (fun r => m ∣ F g s r)).card

theorem rootCount_one (g s : ℕ) : rootCount g s 1 = 1 := by
  simp [rootCount]

theorem rootCount_mul {g s m n : ℕ} (hmn : m.Coprime n) (hm : m ≠ 0) (hn : n ≠ 0) :
    rootCount g s (m * n) = rootCount g s m * rootCount g s n := by
  unfold rootCount
  rw [← card_product]
  refine card_nbij' (fun r => (r % m, r % n))
    (fun ab => (Nat.chineseRemainder hmn ab.1 ab.2 : ℕ)) ?_ ?_ ?_ ?_
  · intro r hr
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hr
    simp only [coe_product, coe_filter, mem_range, Set.mem_prod, Set.mem_ofPred_eq]
    refine ⟨⟨Nat.mod_lt _ (Nat.pos_of_ne_zero hm), ?_⟩, ⟨Nat.mod_lt _ (Nat.pos_of_ne_zero hn), ?_⟩⟩
    · exact dvd_F_iff_mod.mp (dvd_trans (dvd_mul_right m n) hr.2)
    · exact dvd_F_iff_mod.mp (dvd_trans (dvd_mul_left n m) hr.2)
  · rintro ⟨a, b⟩ hab
    simp only [coe_product, coe_filter, mem_range, Set.mem_prod, Set.mem_ofPred_eq] at hab
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq]
    set c := Nat.chineseRemainder hmn a b
    refine ⟨Nat.chineseRemainder_lt_mul hmn a b hm hn, ?_⟩
    apply hmn.mul_dvd_of_dvd_of_dvd
    · exact ((F_modEq c.prop.1).dvd_iff dvd_rfl).mpr hab.1.2
    · exact ((F_modEq c.prop.2).dvd_iff dvd_rfl).mpr hab.2.2
  · intro r hr
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hr
    have hu := Nat.chineseRemainder_modEq_unique hmn (Nat.mod_modEq r m).symm
      (Nat.mod_modEq r n).symm
    have hlt := Nat.chineseRemainder_lt_mul hmn (r % m) (r % n) hm hn
    exact (Nat.ModEq.eq_of_lt_of_lt hu hr.1 hlt).symm
  · rintro ⟨a, b⟩ hab
    simp only [coe_product, coe_filter, mem_range, Set.mem_prod, Set.mem_ofPred_eq] at hab
    set c := Nat.chineseRemainder hmn a b
    have h1 : (c : ℕ) % m = a % m := c.prop.1
    have h2 : (c : ℕ) % n = b % n := c.prop.2
    simp only [Prod.mk.injEq]
    exact ⟨by rw [h1, Nat.mod_eq_of_lt hab.1.1], by rw [h2, Nat.mod_eq_of_lt hab.2.1]⟩

/-- For a prime `p ∤ 2 g s`, `F` has exactly three roots modulo `p`. -/
theorem rootCount_prime {g s p : ℕ} (hp : p.Prime) (hpd : ¬ p ∣ 2 * g * s) :
    rootCount g s p = 3 := by
  have := Fact.mk hp
  have hp2 : ¬ p ∣ 2 := fun h => hpd (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h _) _)
  have hpg : ¬ p ∣ g := fun h => hpd (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h _) _)
  have hps : ¬ p ∣ s := fun h => hpd (dvd_mul_of_dvd_right h _)
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h; apply hp2; exact_mod_cast (ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast h)
  have hg : (g : ZMod p) ≠ 0 := fun h => hpg ((ZMod.natCast_eq_zero_iff g p).mp h)
  have hs : (s : ZMod p) ≠ 0 := fun h => hps ((ZMod.natCast_eq_zero_iff s p).mp h)
  -- the three roots in `ZMod p`
  have hroots : ∀ x : ZMod p, x * (s * x + g) * (s * x + 2 * g) = 0 ↔
      x = 0 ∨ x = -(g : ZMod p) / s ∨ x = -(2 * g : ZMod p) / s := by
    intro x
    simp only [mul_eq_zero]
    constructor
    · rintro ((h | h) | h)
      · exact Or.inl h
      · right; left; rw [eq_div_iff hs]; linear_combination h
      · right; right; rw [eq_div_iff hs]; linear_combination h
    · rintro (h | h | h)
      · exact Or.inl (Or.inl h)
      · left; right; rw [h, mul_div_cancel₀ _ hs]; ring
      · right; rw [h, mul_div_cancel₀ _ hs]; ring
  have h12 : (0 : ZMod p) ≠ -(g : ZMod p) / s := by
    intro h
    rw [eq_div_iff hs] at h
    exact hg (by linear_combination h)
  have h13 : (0 : ZMod p) ≠ -(2 * g : ZMod p) / s := by
    intro h
    rw [eq_div_iff hs] at h
    exact mul_ne_zero h2 hg (by linear_combination h)
  have h23 : -(g : ZMod p) / s ≠ -(2 * g : ZMod p) / s := by
    intro h
    rw [div_eq_div_iff hs hs] at h
    exact mul_ne_zero hg hs (by linear_combination h)
  -- transfer to `range p`
  unfold rootCount
  have hbij : ((range p).filter (fun r => p ∣ F g s r)).card =
      ((Finset.univ : Finset (ZMod p)).filter
        (fun x : ZMod p => x * ((s : ZMod p) * x + (g : ZMod p)) * ((s : ZMod p) * x + 2 * (g : ZMod p)) = 0)).card := by
    refine card_nbij' (fun r => (r : ZMod p)) (fun x => x.val) ?_ ?_ ?_ ?_
    · intro r hr
      simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hr
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq]
      have := (ZMod.natCast_eq_zero_iff (F g s r) p).mpr hr.2
      simpa [F] using this
    · intro x hx
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx
      simp only [coe_filter, mem_range, Set.mem_ofPred_eq]
      refine ⟨ZMod.val_lt x, ?_⟩
      rw [← ZMod.natCast_eq_zero_iff]
      simpa [F, ZMod.natCast_val, ZMod.cast_id] using hx
    · intro r hr
      simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hr
      exact ZMod.val_natCast_of_lt hr.1
    · intro x _
      simp
  rw [hbij]
  have hset : (Finset.univ : Finset (ZMod p)).filter
      (fun x : ZMod p => x * ((s : ZMod p) * x + (g : ZMod p)) * ((s : ZMod p) * x + 2 * (g : ZMod p)) = 0) =
        {0, -(g : ZMod p) / s, -(2 * g : ZMod p) / s} := by
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
    exact hroots x
  rw [hset, card_insert_of_notMem (by simp [h12, h13]), card_pair h23]

theorem rootCount_prod {g s : ℕ} (B : Finset ℕ)
    (hB : ∀ p ∈ B, p.Prime ∧ ¬ p ∣ 2 * g * s) :
    rootCount g s (∏ p ∈ B, p) = 3 ^ B.card := by
  induction B using Finset.induction_on with
  | empty => simp [rootCount_one]
  | insert p B hpB ih =>
    have hp := hB p (mem_insert_self p B)
    have hB' : ∀ q ∈ B, q.Prime ∧ ¬ q ∣ 2 * g * s := fun q hq => hB q (mem_insert_of_mem hq)
    rw [prod_insert hpB, card_insert_of_notMem hpB, pow_succ]
    have hcop : p.Coprime (∏ q ∈ B, q) := by
      apply Nat.Coprime.prod_right
      intro q hq
      exact (Nat.coprime_primes hp.1 (hB' q hq).1).mpr (fun h => hpB (h ▸ hq))
    have hprod0 : (∏ q ∈ B, q) ≠ 0 :=
      prod_ne_zero_iff.mpr fun q hq => (hB' q hq).1.ne_zero
    rw [rootCount_mul hcop hp.1.ne_zero hprod0, rootCount_prime hp.1 hp.2, ih hB', mul_comm]

/-! ### Counting in residue classes -/

theorem card_filter_dvd_eq_sum {g s m : ℕ} (hm : m ≠ 0) (M : ℕ) :
    ((range M).filter (fun q => m ∣ F g s q)).card =
      ∑ r ∈ (range m).filter (fun r => m ∣ F g s r),
        ((range M).filter (fun q => q % m = r)).card := by
  rw [card_eq_sum_card_fiberwise (f := fun q => q % m)]
  · apply sum_congr rfl
    intro r hr
    simp only [mem_filter, mem_range] at hr
    congr 1
    ext q
    simp only [mem_filter, mem_range]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨⟨h1, dvd_F_iff_mod.mpr (h3 ▸ hr.2)⟩, h3⟩
  · intro q hq
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hq
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq]
    exact ⟨Nat.mod_lt _ (Nat.pos_of_ne_zero hm), dvd_F_iff_mod.mp hq.2⟩

theorem abs_card_mod_eq_sub_le {m r : ℕ} (hm : m ≠ 0) (hr : r < m) (M : ℕ) :
    |(((range M).filter (fun q => q % m = r)).card : ℝ) - M / m| ≤ 1 := by
  have hcount := Nat.count_modEq_card M (Nat.pos_of_ne_zero hm) r
  rw [Nat.count_eq_card_filter_range] at hcount
  have heq : (range M).filter (fun q => q % m = r) = (range M).filter (· ≡ r [MOD m]) := by
    ext q; simp [Nat.ModEq, Nat.mod_eq_of_lt hr]
  rw [heq, hcount]
  have hm' : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hdiv : ((M / m : ℕ) : ℝ) ≤ M / m := Nat.cast_div_le
  have hdiv2 : (M : ℝ) / m < (M / m : ℕ) + 1 := by
    rw [div_lt_iff₀ hm']
    have := Nat.lt_div_mul_add (a := M) (Nat.pos_of_ne_zero hm)
    exact_mod_cast (by nlinarith [this] : M < (M / m + 1) * m)
  rw [abs_le]
  split_ifs <;> push_cast <;> constructor <;> linarith

/-- The number of `q < M` with `m ∣ F(q)` is `M · ρ(m)/m + O(ρ(m))`. -/
theorem abs_card_dvd_sub_le {g s m : ℕ} (hm : m ≠ 0) (M : ℕ) :
    |(((range M).filter (fun q => m ∣ F g s q)).card : ℝ) - M * rootCount g s m / m| ≤
      rootCount g s m := by
  rw [card_filter_dvd_eq_sum hm M]
  unfold rootCount
  set R := (range m).filter (fun r => m ∣ F g s r)
  have hR : (M : ℝ) * R.card / m = ∑ r ∈ R, ((M : ℝ) / m) := by
    rw [sum_const, nsmul_eq_mul]; ring
  push_cast
  rw [hR, ← sum_sub_distrib]
  calc |∑ r ∈ R, ((((range M).filter (fun q => q % m = r)).card : ℝ) - M / m)|
      ≤ ∑ r ∈ R, |(((range M).filter (fun q => q % m = r)).card : ℝ) - M / m| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ r ∈ R, (1 : ℝ) :=
        sum_le_sum fun r hr => abs_card_mod_eq_sub_le hm (mem_range.mp (mem_filter.mp hr).1) M
    _ = R.card := by simp

end WLJ.Sieve
