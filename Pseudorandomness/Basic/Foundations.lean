/-
  Boolean Functions and Truth Tables - Foundation Module
  =======================================================

  Core Boolean function abstractions, encoding/decoding, and bijection proofs.

  This module provides the foundational definitions for representing Boolean
  functions as truth tables and natural numbers, along with complete proofs
  that these representations are bijective.

  Key results:
  - toTruthTable and fromTruthTable form a bijection
  - encode and decode form a bijection
  - getBit correctly extracts binary representation
  - binary_representation theorem: every number equals the sum of its bits
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Bool.Basic
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Algebra.Order.Ring.Canonical
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Topology.Basic
import Mathlib.Algebra.Order.Ring.GeomSum
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Conjecture Macro

A `conjecture` is a theorem statement that is believed to be true but not yet proved.
-/

macro mods:declModifiers "conjecture " n:declId sig:declSig val:declVal : command =>
  `($mods:declModifiers theorem $n $sig $val)

namespace ComplexityBarriers

/-! ## Boolean Functions and Truth Tables -/

/-- A Boolean function on n variables -/
def BoolFun (n : ℕ) := (Fin (2^n)) → Bool

/-- Truth table representation: a Boolean function as a bitvector of length 2^n -/
def TruthTable (n : ℕ) := Fin (2^(2^n))

/-- Convert between representations -/
def toTruthTable {n : ℕ} (f : BoolFun n) : TruthTable n :=
  -- The truth table is the binary encoding of f's values
  -- Each bit i in the result represents f(i)
  -- We construct a natural number and take mod 2^(2^n)
  let value := (Finset.univ : Finset (Fin (2^n))).sum fun i =>
    if f i then 2^i.val else 0
  ⟨value % 2^(2^n), Nat.mod_lt _ (pow_pos (by norm_num : 0 < 2) (2^n))⟩

def fromTruthTable {n : ℕ} (tt : TruthTable n) : BoolFun n :=
  -- Extract bit i from the truth table to get f(i)
  fun i => (tt.val / 2^i.val) % 2 = 1

/-- The sum in toTruthTable is bounded by 2^(2^n) - 1 -/
lemma toTruthTable_sum_bound {n : ℕ} (f : BoolFun n) :
    (Finset.univ : Finset (Fin (2^n))).sum (fun i => if f i then 2^i.val else 0) < 2^(2^n) := by
  have step1 : (Finset.univ : Finset (Fin (2^n))).sum (fun i => if f i then 2^i.val else 0)
             ≤ (Finset.univ : Finset (Fin (2^n))).sum (fun i => 2^i.val) := by
    apply Finset.sum_le_sum
    intro i _
    split_ifs
    · exact Nat.le_refl _
    · exact Nat.zero_le _
  have step2 : (Finset.univ : Finset (Fin (2^n))).sum (fun i => 2^i.val)
             ≤ Finset.sum (Finset.range (2^n)) (fun i => 2^i) := by
    -- Convert using sum_image
    calc (Finset.univ : Finset (Fin (2^n))).sum (fun i => 2^i.val)
        = Finset.sum (Finset.image Fin.val (Finset.univ : Finset (Fin (2^n)))) (fun k => 2^k) := by
          symm
          rw [Finset.sum_image]
          intro j₁ _ j₂ _ h
          exact Fin.ext h
      _ ≤ Finset.sum (Finset.range (2^n)) (fun k => 2^k) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro k hk
            simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_range] at hk ⊢
            obtain ⟨j, _, rfl⟩ := hk
            exact j.isLt
          · intros; exact Nat.zero_le _
  calc (Finset.univ : Finset (Fin (2^n))).sum (fun i => if f i then 2^i.val else 0)
      ≤ Finset.sum (Finset.range (2^n)) (fun i => 2^i) := Nat.le_trans step1 step2
    _ < 2^(2^n) := by
        -- Use the fact that sum of 2^i for i < m is 2^m - 1 < 2^m
        have h : Finset.sum (Finset.range (2^n)) (fun i => 2^i) ≤ 2^(2^n) - 1 := by
          induction (2^n) with
          | zero => simp
          | succ m ih =>
            rw [Finset.sum_range_succ]
            have h1 : 1 ≤ 2^m := Nat.one_le_pow m 2 (by norm_num)
            calc Finset.sum (Finset.range m) (fun i => 2^i) + 2^m
                ≤ (2^m - 1) + 2^m := Nat.add_le_add_right ih _
              _ = 2^m + 2^m - 1 := by rw [Nat.add_sub_assoc h1]; ring
              _ = 2 * 2^m - 1 := by ring_nf
              _ = 2^(m+1) - 1 := by rw [← pow_succ']
        exact Nat.lt_of_le_of_lt h (Nat.sub_lt (pow_pos (by norm_num : 0 < 2) (2^n)) (by norm_num))

/-! ## Complete Proof of Boolean Function Encoding Bijection -/

/-
  Complete Proof of getBit_encode
  ================================

  The key lemma: getBit (Σⱼ (if f j then 2^j else 0)) i = f i

  Proof strategy:
  1. Split the sum into three parts: j < i, j = i, j > i
  2. Show the "low" part (j < i) is < 2^i
  3. Show the "high" part (j > i) is divisible by 2^(i+1)
  4. Use the bit extraction properties to conclude
-/

/-- Extract bit i from natural number x -/
def getBit (x i : ℕ) : Bool := (x / 2^i) % 2 = 1

/-! ### Lemmas about sums of powers of 2 -/

/-- Sum of 2^j for j < i is equal to 2^i - 1 -/
lemma geom_sum_two_pow (i : ℕ) : Finset.sum (Finset.range i) (fun j => 2^j) = 2^i - 1 := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    have h1 : 1 ≤ 2^i := Nat.one_le_pow i 2 (by norm_num)
    have h2 : 2^i - 1 + 2^i = 2^i + 2^i - 1 := by
      rw [Nat.add_sub_assoc h1]
      ring
    rw [h2]
    ring_nf

/-- Sum of 2^j for j < i is less than 2^i -/
lemma sum_pow_lt_pow (n i : ℕ) (_ : i ≤ n) :
    Finset.sum (Finset.filter (· < i) (Finset.range n)) (fun j => 2^j) < 2^i := by
  calc Finset.sum (Finset.filter (· < i) (Finset.range n)) (fun j => 2^j)
      ≤ Finset.sum (Finset.range i) (fun j => 2^j) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro x hx
          simp at hx ⊢
          exact hx.2
        · intros; exact Nat.zero_le _
    _ = 2^i - 1 := geom_sum_two_pow i
    _ < 2^i := Nat.sub_lt (pow_pos (by norm_num : 0 < 2) i) (by norm_num)

/-- Sum of 2^j for j > i is divisible by 2^(i+1) -/
lemma sum_pow_dvd (n i : ℕ) (S : Finset ℕ) (hS : ∀ j ∈ S, i < j ∧ j < n) :
    2^(i+1) ∣ Finset.sum S (fun j => 2^j) := by
  induction S using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    obtain ⟨hij, _⟩ := hS a (Finset.mem_insert_self _ _)
    have h1 : i + 1 ≤ a := hij
    have h2 : 2^(i+1) ∣ 2^a := pow_dvd_pow 2 h1
    have h3 : 2^(i+1) ∣ Finset.sum s (fun j => 2^j) := by
      apply ih
      intro j hj
      exact hS j (Finset.mem_insert_of_mem hj)
    exact Nat.dvd_add h2 h3

/-- Adding a multiple of 2^(i+1) doesn't affect bit i -/
lemma getBit_add_mul (a k i : ℕ) :
    getBit (a + k * 2^(i+1)) i = getBit a i := by
  simp only [getBit]
  have pos_i : 0 < 2^i := pow_pos (by norm_num : 0 < 2) i
  have h1 : (a + k * 2^(i+1)) / 2^i = a / 2^i + k * 2 := by
    calc (a + k * 2^(i+1)) / 2^i
        = (a + k * (2 * 2^i)) / 2^i := by rw [← pow_succ']
      _ = (a + (k * 2) * 2^i) / 2^i := by ring_nf
      _ = a / 2^i + k * 2 := by rw [Nat.add_mul_div_right _ _ pos_i]
  rw [h1, Nat.add_mul_mod_self_right]

/-- For a < 2^i, getBit (a + c * 2^i) i = (c % 2 = 1) -/
lemma getBit_add_exact (a c i : ℕ) (ha : a < 2^i) :
    getBit (a + c * 2^i) i = (c % 2 = 1) := by
  simp only [getBit]
  have pos_i : 0 < 2^i := pow_pos (by norm_num : 0 < 2) i
  have : (a + c * 2^i) / 2^i = c := by
    rw [Nat.add_mul_div_right _ _ pos_i]
    have : a / 2^i = 0 := Nat.div_eq_of_lt ha
    simp [this]
  rw [this]
  simp only [decide_eq_true_eq]

/-! ### The Core Theorem -/

/-- Partition Finset.univ for Fin n into three parts relative to i -/
lemma fin_partition {n : ℕ} (i : Fin n) :
    Finset.univ =
    (Finset.filter (fun j : Fin n => j.val < i.val) Finset.univ) ∪
    {i} ∪
    (Finset.filter (fun j : Fin n => j.val > i.val) Finset.univ) := by
  ext j
  simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_filter, Finset.mem_singleton, true_and]
  constructor
  · intro _
    rcases Nat.lt_trichotomy j.val i.val with h | h | h
    · left; left; exact h
    · left; right; exact Fin.ext h
    · right; exact h
  · intro _; trivial

/-- Helper: Sum over filtered Fin n where j.val < i.val is bounded by 2^i - 1 -/
lemma sum_fin_lt_bound {n : ℕ} (a : Fin n → ℕ) (ha : ∀ j, a j ≤ 1) (i : Fin n) :
    Finset.sum (Finset.filter (fun j : Fin n => j.val < i.val) Finset.univ)
      (fun j => a j * 2^j.val) < 2^i.val := by
  -- First bound by sum of 2^j.val
  have step1 : Finset.sum (Finset.filter (fun j : Fin n => j.val < i.val) Finset.univ) (fun j => a j * 2^j.val)
             ≤ Finset.sum (Finset.filter (fun j : Fin n => j.val < i.val) Finset.univ) (fun j => 2^j.val) := by
    apply Finset.sum_le_sum
    intro j _
    calc a j * 2^j.val
        ≤ 1 * 2^j.val := Nat.mul_le_mul_right _ (ha j)
      _ = 2^j.val := by ring
  -- Then bound by geometric sum via transitivity
  have step2 : Finset.sum (Finset.filter (fun j : Fin n => j.val < i.val) Finset.univ) (fun j => 2^j.val)
             ≤ Finset.sum (Finset.range i.val) (fun j => 2^j) := by
    -- Use the fact that the filtered sum equals sum over image, which is a subset of range
    calc Finset.sum (Finset.filter (fun j : Fin n => j.val < i.val) Finset.univ) (fun j => 2^j.val)
        = Finset.sum (Finset.image Fin.val (Finset.filter (fun j : Fin n => j.val < i.val) Finset.univ)) (fun k => 2^k) := by
          -- The image gives us the set of natural numbers, use sum_image
          symm
          rw [Finset.sum_image]
          intro j₁ hj₁ j₂ hj₂ h
          simp at hj₁ hj₂
          exact Fin.ext h
      _ ≤ Finset.sum (Finset.range i.val) (fun k => 2^k) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro k hk
            simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range] at hk ⊢
            obtain ⟨j, hj, rfl⟩ := hk
            exact hj
          · intros; exact Nat.zero_le _
  calc Finset.sum (Finset.filter (fun j : Fin n => j.val < i.val) Finset.univ) (fun j => a j * 2^j.val)
      ≤ Finset.sum (Finset.filter (fun j : Fin n => j.val < i.val) Finset.univ) (fun j => 2^j.val) := step1
    _ ≤ Finset.sum (Finset.range i.val) (fun j => 2^j) := step2
    _ = 2^i.val - 1 := geom_sum_two_pow i.val
    _ < 2^i.val := Nat.sub_lt (pow_pos (by norm_num : 0 < 2) i.val) (by norm_num)

/-- Helper: Sum over filtered Fin n where j.val > i.val is divisible by 2^(i+1) -/
lemma sum_fin_gt_dvd {n : ℕ} (a : Fin n → ℕ) (ha : ∀ j, a j ≤ 1) (i : Fin n) :
    2^(i.val + 1) ∣ Finset.sum (Finset.filter (fun j : Fin n => i.val < j.val) Finset.univ)
      (fun j => a j * 2^j.val) := by
  -- Convert to a sum over powers, using that a j ∈ {0, 1}
  -- When a j = 0, the term contributes 0; when a j = 1, it contributes 2^j.val
  have key : Finset.sum (Finset.filter (fun j : Fin n => i.val < j.val) Finset.univ) (fun j => a j * 2^j.val)
           = Finset.sum (Finset.filter (fun j : Fin n => i.val < j.val ∧ a j = 1) Finset.univ) (fun j => 2^j.val) := by
    -- Rewrite using the fact that a j * 2^j.val = 0 when a j = 0, and = 2^j.val when a j = 1
    have h_split : ∀ j : Fin n, a j * 2^j.val = if a j = 1 then 2^j.val else 0 := by
      intro j
      have hj := ha j
      -- Since a j ≤ 1, we have a j ∈ {0, 1}
      have : a j = 0 ∨ a j = 1 := Nat.le_one_iff_eq_zero_or_eq_one.mp hj
      cases this with
      | inl h => simp [h]
      | inr h => simp [h]
    -- Transform the sum
    calc Finset.sum (Finset.filter (fun j : Fin n => i.val < j.val) Finset.univ) (fun j => a j * 2^j.val)
        = Finset.sum (Finset.filter (fun j : Fin n => i.val < j.val) Finset.univ)
            (fun j => if a j = 1 then 2^j.val else 0) := by
          congr 1
          ext j
          exact h_split j
      _ = Finset.sum (Finset.filter (fun j : Fin n => i.val < j.val ∧ a j = 1) Finset.univ) (fun j => 2^j.val) := by
          -- The sum of "if a j = 1 then 2^j else 0" over {j | i < j}
          -- equals the sum of "2^j" over {j | i < j ∧ a j = 1}
          rw [← Finset.sum_filter]
          congr 1
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [key]
  -- Now apply sum_pow_dvd to the set of j.val where i.val < j.val ∧ a j = 1
  let S := Finset.image (fun j : Fin n => j.val)
    (Finset.filter (fun j : Fin n => i.val < j.val ∧ a j = 1) Finset.univ)
  have hS : ∀ k ∈ S, i.val < k ∧ k < n := by
    intro k hk
    simp only [S, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hk
    obtain ⟨j, hj, rfl⟩ := hk
    exact ⟨hj.1, j.isLt⟩
  have sum_eq : Finset.sum (Finset.filter (fun j : Fin n => i.val < j.val ∧ a j = 1) Finset.univ) (fun j => 2^j.val)
              = Finset.sum S (fun k => 2^k) := by
    symm
    rw [Finset.sum_image]
    · intro j₁ hj₁ j₂ hj₂ h
      simp at hj₁ hj₂
      exact Fin.ext h
  rw [sum_eq]
  exact sum_pow_dvd n i.val S hS

/--
  **Core Theorem**: For any function a : Fin n → {0, 1} and any i < n,
  getBit (Σⱼ a(j) * 2^j) i = (a(i) = 1)
-/
theorem getBit_weighted_sum {n : ℕ} (a : Fin n → ℕ) (ha : ∀ j, a j ≤ 1) (i : Fin n) :
    getBit (Finset.sum Finset.univ (fun j : Fin n => a j * 2^j.val)) i.val = (a i = 1) := by
  -- Partition the sum using fin_partition
  rw [fin_partition i]
  rw [Finset.sum_union, Finset.sum_union]
  · -- Now we have sum_L + (sum_M + sum_H)
    -- where sum_L = sum over j < i, sum_M = sum over {i}, sum_H = sum over j > i

    simp only [Finset.sum_singleton]

    -- Let L, M, H denote the three parts
    set L := Finset.sum (Finset.filter (fun j : Fin n => j.val < i.val) Finset.univ)
               (fun j => a j * 2^j.val) with hL
    set M := a i * 2^i.val with hM
    set H := Finset.sum (Finset.filter (fun j : Fin n => i.val < j.val) Finset.univ)
               (fun j => a j * 2^j.val) with hH

    -- Key facts:
    -- 1. L < 2^i (from sum_fin_lt_bound)
    have hL_bound : L < 2^i.val := sum_fin_lt_bound a ha i

    -- 2. H is divisible by 2^(i+1) (from sum_fin_gt_dvd)
    have hH_dvd : 2^(i.val + 1) ∣ H := sum_fin_gt_dvd a ha i

    -- 3. M = a(i) * 2^i, where a(i) ∈ {0, 1}
    have ha_i : a i = 0 ∨ a i = 1 := Nat.le_one_iff_eq_zero_or_eq_one.mp (ha i)

    -- Now we can extract the bit
    -- Total = L + M + H = L + a(i) * 2^i + H

    cases ha_i with
    | inl h =>
      -- Case: a i = 0, so M = 0
      simp only [hM, h, zero_mul, add_zero]
      -- getBit (L + H) i = false
      obtain ⟨k, hk⟩ := hH_dvd
      rw [hk, mul_comm, getBit_add_mul, getBit]
      have : L / 2^i.val = 0 := Nat.div_eq_of_lt hL_bound
      simp [this]
    | inr h =>
      -- Case: a i = 1, so M = 2^i
      simp only [hM, h, one_mul]
      -- getBit (L + 2^i + H) i = true
      obtain ⟨k, hk⟩ := hH_dvd
      rw [hk, mul_comm]
      -- Rearrange: L + 2^i + k*2^(i+1) = (L + 1*2^i) + k*2^(i+1)
      have : L + 2^i.val + k*2^(i.val+1) = (L + 1*2^i.val) + k*2^(i.val+1) := by ring
      rw [this, getBit_add_mul, one_mul]
      -- Now the goal is: (getBit (L + 2^i.val) i.val = true) = True
      rw [show L + 2^i.val = L + 1*2^i.val by ring, getBit_add_exact L 1 i.val hL_bound]
      simp
  · -- Disjointness: filter (j < i) ∩ {i} = ∅
    simp only [Finset.disjoint_iff_ne, Finset.mem_filter, Finset.mem_singleton,
               Finset.mem_univ, true_and]
    intro j hj k hk heq
    subst heq hk
    exact absurd hj (Nat.lt_irrefl j.val)
  · -- Disjointness: (filter (j < i) ∪ {i}) ∩ filter (j > i) = ∅
    simp only [Finset.disjoint_iff_ne, Finset.mem_union, Finset.mem_filter,
               Finset.mem_singleton, Finset.mem_univ, true_and]
    intro j hj k hk heq
    subst heq
    cases hj with
    | inl hjlt => exact absurd hjlt (Nat.not_lt.mpr (Nat.le_of_lt hk))
    | inr hjeq => subst hjeq; exact absurd hk (Nat.lt_irrefl j.val)

/-! ### Main Results -/

/-- Boolean function encoding -/
def encode {n : ℕ} (f : Fin (2^n) → Bool) : ℕ :=
  Finset.sum Finset.univ (fun i : Fin (2^n) => if f i then 2^i.val else 0)

/-- Boolean function decoding -/
def decode {n : ℕ} (x : ℕ) : Fin (2^n) → Bool := fun i => getBit x i.val

/-- **Theorem 1**: decode (encode f) = f -/
theorem decode_encode {n : ℕ} (f : Fin (2^n) → Bool) : decode (encode f) = f := by
  ext i
  simp only [decode, encode]
  -- Convert to weighted sum form
  have heq : Finset.sum Finset.univ (fun j : Fin (2^n) => if f j then 2^j.val else 0)
           = Finset.sum Finset.univ (fun j : Fin (2^n) => (if f j then 1 else 0) * 2^j.val) := by
    congr 1; ext j; split_ifs <;> ring
  rw [heq]
  have bound_check : ∀ j : Fin (2^n), (if f j then 1 else 0) ≤ 1 := by
    intro j; split_ifs <;> norm_num
  have h := getBit_weighted_sum (fun j => if f j then 1 else 0) bound_check i
  -- Case split on f i to show getBit ... = f i
  cases hf : f i
  · -- f i = false, so (if f i then 1 else 0) = 0
    simp [hf] at h ⊢
    exact h
  · -- f i = true, so (if f i then 1 else 0) = 1
    simp [hf] at h ⊢
    exact h

/--
  **Theorem**: fromTruthTable and toTruthTable are inverses (left inverse).

  This proof uses the fact that the sum in toTruthTable is always less than 2^(2^n)
  (by toTruthTable_sum_bound), so the modulo operation doesn't change the value,
  and then applies getBit_weighted_sum.
-/
theorem fromTruthTable_toTruthTable {n : ℕ} (f : BoolFun n) :
    fromTruthTable (toTruthTable f) = f := by
  funext i
  simp only [fromTruthTable, toTruthTable]
  -- The sum is less than 2^(2^n), so modulo doesn't change it
  have hbound := toTruthTable_sum_bound f
  have hmod : ((Finset.univ : Finset (Fin (2^n))).sum fun j => if f j then 2^j.val else 0) % 2^(2^n)
            = (Finset.univ : Finset (Fin (2^n))).sum fun j => if f j then 2^j.val else 0 :=
    Nat.mod_eq_of_lt hbound
  simp only [hmod]
  -- Convert to weighted sum form
  have heq : (Finset.univ : Finset (Fin (2^n))).sum (fun j => if f j then 2^j.val else 0)
           = (Finset.univ : Finset (Fin (2^n))).sum (fun j => (if f j then 1 else 0) * 2^j.val) := by
    congr 1; ext j; split_ifs <;> ring
  simp only [heq]
  have bound_check : ∀ j : Fin (2^n), (if f j then 1 else 0) ≤ 1 := by
    intro j; split_ifs <;> norm_num
  have h := getBit_weighted_sum (fun j => if f j then 1 else 0) bound_check i
  simp only [getBit] at h
  -- Case split on f i to show the result
  cases hf : f i
  · -- f i = false
    simp [hf] at h ⊢
    exact h
  · -- f i = true
    simp [hf] at h ⊢
    exact h

/-- Helper: getBit of x%2^k for i < k equals getBit of x i

This states that taking x modulo 2^k (which keeps the lower k bits) and then
extracting bit i (where i < k) gives the same result as directly extracting bit i from x.

**Proof**: x % 2^k keeps only the lower k bits. For i < k, bit i is within these lower k bits,
so it's preserved. We use the division algorithm: x = q * 2^k + (x % 2^k), and show that
the extra term q * 2^(k-i) is even when computing (x / 2^i) % 2.
-/
theorem getBit_mod_two_pow {x k i : ℕ} (hi : i < k) : getBit (x % 2^k) i = getBit x i := by
  simp only [getBit]
  -- Need to show: (x % 2^k) / 2^i % 2 = 1 ↔ x / 2^i % 2 = 1
  -- Suffices to show: (x % 2^k) / 2^i % 2 = x / 2^i % 2
  congr 1

  -- Write x = q * 2^k + r where r = x % 2^k
  set q := x / 2^k
  set r := x % 2^k
  have hx : x = q * 2^k + r := by
    have := Nat.div_add_mod x (2^k)
    rw [mul_comm] at this
    exact this.symm

  -- Express 2^k = 2^i * 2^(k-i)
  have hpow : 2^k = 2^i * 2^(k-i) := by
    rw [← pow_add]
    congr 1
    exact (Nat.add_sub_cancel' (Nat.le_of_lt hi)).symm

  -- Compute x / 2^i
  have hdiv : x / 2^i = q * 2^(k-i) + r / 2^i := by
    have pos : 0 < 2^i := pow_pos (by norm_num : 0 < 2) i
    calc x / 2^i = (q * 2^k + r) / 2^i := by rw [hx]
      _ = (q * (2^i * 2^(k-i)) + r) / 2^i := by rw [hpow]
      _ = (q * 2^(k-i) * 2^i + r) / 2^i := by ring_nf
      _ = (r + q * 2^(k-i) * 2^i) / 2^i := by rw [add_comm]
      _ = (r + 2^i * (q * 2^(k-i))) / 2^i := by ring_nf
      _ = r / 2^i + q * 2^(k-i) := by rw [Nat.add_mul_div_left _ _ pos]
      _ = q * 2^(k-i) + r / 2^i := by rw [add_comm]

  -- Since k - i ≥ 1, we have 2 | q * 2^(k-i)
  have heven : 2 ∣ q * 2^(k-i) := by
    have hki : 1 ≤ k - i := Nat.sub_pos_of_lt hi
    have hdvd : 2 ∣ 2^(k-i) := by
      use 2^(k-i-1)
      rw [← pow_succ']
      congr 1
      exact (Nat.sub_add_cancel hki).symm
    exact dvd_mul_of_dvd_right hdvd q

  -- Now compute mod 2
  have hcalc : x / 2^i % 2 = r / 2^i % 2 := by
    calc x / 2^i % 2 = (q * 2^(k-i) + r / 2^i) % 2 := by rw [hdiv]
      _ = (q * 2^(k-i) % 2 + r / 2^i % 2) % 2 := by rw [Nat.add_mod]
      _ = (0 + r / 2^i % 2) % 2 := by
          congr 2
          have : q * 2^(k-i) % 2 = 0 := Nat.mod_eq_zero_of_dvd heven
          exact this
      _ = r / 2^i % 2 := by
          simp only [zero_add]
          exact Nat.mod_eq_of_lt (Nat.mod_lt _ (by norm_num))
  rw [hcalc]

/--
  **Binary Representation Theorem**: Every natural number x < 2^n equals the sum of
  its bit representations.

  **Proof** by induction on n:
  - Base case: x < 1 implies x = 0, and the empty sum equals 0
  - Inductive step: Use Nat.div_add_mod to split x into low bits (x % 2^n) and high bit (x / 2^n)
-/
theorem binary_representation (n : ℕ) (x : ℕ) (hx : x < 2^n) :
    x = Finset.sum (Finset.range n) (fun i => if getBit x i then 2^i else 0) := by
  induction n generalizing x with
  | zero =>
    -- x < 2^0 = 1, so x = 0
    have : x = 0 := by
      have : 2^0 = 1 := by norm_num
      rw [this] at hx
      exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hx)
    simp [this]
  | succ n ih =>
    -- x < 2^(n+1) = 2 * 2^n
    -- Write x = (x % 2^n) + (x / 2^n) * 2^n
    have hdiv := Nat.div_add_mod x (2^n)
    conv_lhs => rw [← hdiv]
    -- x / 2^n is either 0 or 1
    have hquot : x / 2^n < 2 := by
      have pos_n : 0 < 2^n := pow_pos (by norm_num : 0 < 2) n
      have div_eq : 2^(n+1) / 2^n = 2 := by
        rw [pow_succ]
        simp
      calc x / 2^n
          ≤ x / 2^n := Nat.le_refl _
        _ < 2^(n+1) / 2^n := Nat.div_lt_div_of_lt_of_dvd (pow_dvd_pow 2 (Nat.le_succ n)) hx
        _ = 2 := div_eq
    -- Apply IH to x % 2^n
    have hmod_bound : x % 2^n < 2^n := Nat.mod_lt x (pow_pos (by norm_num : 0 < 2) n)
    have ih_mod := ih (x % 2^n) hmod_bound
    -- Rewrite the sum over range (n+1) as sum over range n plus the nth term
    rw [Finset.sum_range_succ]
    -- Show that the sum over range n equals x % 2^n
    have sum_eq_mod : Finset.sum (Finset.range n) (fun i => if getBit x i then 2^i else 0)
                    = x % 2^n := by
      rw [ih_mod]
      apply Finset.sum_congr rfl
      intro i hi
      -- i ∈ Finset.range n, so i < n
      have hi_lt : i < n := Finset.mem_range.mp hi
      rw [← getBit_mod_two_pow hi_lt]
    rw [sum_eq_mod]
    -- Show that getBit x n = decide (x / 2^n = 1)
    have hbit_n : getBit x n = decide (x / 2^n = 1) := by
      simp only [getBit]
      -- We need: decide ((x / 2^n) % 2 = 1) = decide (x / 2^n = 1)
      -- Since x / 2^n < 2, we have x / 2^n ∈ {0, 1}
      have hcases : x / 2^n = 0 ∨ x / 2^n = 1 := Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.le_of_lt_succ hquot)
      cases hcases with
      | inl h => simp [h]  -- When x / 2^n = 0: 0 % 2 = 0 ≠ 1, and 0 ≠ 1
      | inr h => simp [h]  -- When x / 2^n = 1: 1 % 2 = 1, and 1 = 1
    -- Now use hbit_n to determine the value of x / 2^n
    cases hb : getBit x n
    · -- getBit x n = false, so x / 2^n = 0
      rw [hb] at hbit_n
      simp at hbit_n
      have hquot_eq : x / 2^n = 0 := by
        have : x / 2^n = 0 ∨ x / 2^n = 1 := Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.le_of_lt_succ hquot)
        cases this with
        | inl h => exact h
        | inr h => simp [h] at hbit_n
      simp [hquot_eq]
    · -- getBit x n = true, so x / 2^n = 1
      rw [hb] at hbit_n
      simp at hbit_n
      have hquot_eq : x / 2^n = 1 := by
        have : x / 2^n = 0 ∨ x / 2^n = 1 := Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.le_of_lt_succ hquot)
        cases this with
        | inl h => simp [h] at hbit_n
        | inr h => exact h
      simp [hquot_eq]
      ring

/--
  **Theorem**: toTruthTable and fromTruthTable are inverses (right inverse).

  This proof uses binary_representation to show that reconstructing a number from its bits
  gives back the original number.
-/
theorem toTruthTable_fromTruthTable {n : ℕ} (tt : TruthTable n) :
    toTruthTable (fromTruthTable tt) = tt := by
  apply Fin.ext
  simp only [toTruthTable, fromTruthTable]
  -- First convert decide ... = true to getBit
  have sum_conv : (Finset.univ : Finset (Fin (2^n))).sum (fun i => if decide ((tt.val / 2^i.val) % 2 = 1) = true then 2^i.val else 0)
                = (Finset.univ : Finset (Fin (2^n))).sum (fun i => if getBit tt.val i.val then 2^i.val else 0) := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [getBit, decide_eq_true_iff]
  rw [sum_conv]
  -- Convert the sum over Fin (2^n) to a sum over range (2^n)
  have sum_eq : (Finset.univ : Finset (Fin (2^n))).sum (fun i => if getBit tt.val i.val then 2^i.val else 0)
              = Finset.sum (Finset.range (2^n)) (fun k => if getBit tt.val k then 2^k else 0) := by
    calc (Finset.univ : Finset (Fin (2^n))).sum (fun i => if getBit tt.val i.val then 2^i.val else 0)
        = Finset.sum (Finset.image Fin.val Finset.univ) (fun k => if getBit tt.val k then 2^k else 0) := by
          symm
          rw [Finset.sum_image]
          intro i _ j _ h
          exact Fin.ext h
      _ = Finset.sum (Finset.range (2^n)) (fun k => if getBit tt.val k then 2^k else 0) := by
          congr 1
          ext k
          simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_range]
          constructor
          · intro ⟨i, h⟩; rw [← h]; exact i.isLt
          · intro hk; exact ⟨⟨k, hk⟩, rfl⟩
  rw [sum_eq]
  -- Now use binary_representation
  have h := binary_representation (2^n) tt.val tt.isLt
  rw [← h]
  -- The modulo doesn't change the value since tt.val < 2^(2^n)
  exact Nat.mod_eq_of_lt tt.isLt

/-- For k >= m, getBit of any x < 2^m at position k is false -/
lemma getBit_of_lt {x m k : ℕ} (hx : x < 2^m) (hk : m ≤ k) : getBit x k = false := by
  simp only [getBit]
  -- Show (x / 2^k) % 2 ≠ 1
  have : x / 2^k = 0 := by
    apply Nat.div_eq_of_lt
    calc x < 2^m := hx
         _ ≤ 2^k := pow_le_pow_right' (by norm_num) hk
  simp [this]

/--
  **Theorem 2** (Right Inverse): encode (decode x) = x for x < 2^(2^n).

  This follows directly from binary_representation. The key step is showing the sum over
  Finset.univ : Finset (Fin (2^n)) equals the sum over Finset.range (2^n), which is a
  straightforward bijection argument.
-/
theorem encode_decode {n : ℕ} (x : ℕ) (hx : x < 2^(2^n)) : @encode (2^n) (@decode (2^n) x) = x := by
  unfold encode decode getBit
  -- First convert decide ... = true to the bare condition
  conv_lhs =>
    arg 2
    ext i
    rw [show (if decide ((x / 2^i.val) % 2 = 1) = true then 2^i.val else 0) =
              (if (x / 2^i.val) % 2 = 1 then 2^i.val else 0) by simp]
  -- Convert the sum over Fin (2^(2^n)) to a sum over range (2^(2^n))
  have sum_eq : (Finset.univ : Finset (Fin (2^(2^n)))).sum (fun i => if (x / 2^i.val) % 2 = 1 then 2^i.val else 0)
              = Finset.sum (Finset.range (2^(2^n))) (fun k => if (x / 2^k) % 2 = 1 then 2^k else 0) := by
    calc (Finset.univ : Finset (Fin (2^(2^n)))).sum (fun i => if (x / 2^i.val) % 2 = 1 then 2^i.val else 0)
        = Finset.sum (Finset.image Fin.val Finset.univ) (fun k => if (x / 2^k) % 2 = 1 then 2^k else 0) := by
          symm
          rw [Finset.sum_image]
          intro i _ j _ h
          exact Fin.ext h
      _ = Finset.sum (Finset.range (2^(2^n))) (fun k => if (x / 2^k) % 2 = 1 then 2^k else 0) := by
          congr 1
          ext k
          simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_range]
          constructor
          · intro ⟨i, h⟩; rw [← h]; exact i.isLt
          · intro hk; exact ⟨⟨k, hk⟩, rfl⟩
  rw [sum_eq]
  -- Convert to getBit form
  have getBit_eq : Finset.sum (Finset.range (2^(2^n))) (fun k => if (x / 2^k) % 2 = 1 then 2^k else 0)
                 = Finset.sum (Finset.range (2^(2^n))) (fun k => if getBit x k then 2^k else 0) := by
    apply Finset.sum_congr rfl
    intro k _
    simp only [getBit, decide_eq_true_iff]
  rw [getBit_eq]
  -- Extend the sum from range (2^n) to range (2^(2^n))
  -- All terms beyond 2^n are zero since getBit x i = false for i >= 2^n when x < 2^(2^n)
  have extend_sum : Finset.sum (Finset.range (2^(2^n))) (fun k => if getBit x k then 2^k else 0)
                  = Finset.sum (Finset.range (2^n)) (fun k => if getBit x k then 2^k else 0) := by
    -- Use Finset.sum_subset to show the sum extends with zeros
    symm
    apply Finset.sum_subset
    · intro k hk
      simp only [Finset.mem_range] at hk ⊢
      calc k < 2^n := hk
           _ ≤ 2^(2^n) := by
             -- Need n ≤ 2^n
             have hn_le : n ≤ 2^n := by
               clear hx sum_eq getBit_eq k hk
               induction n with
               | zero => norm_num
               | succ n ih =>
                 calc n + 1 ≤ 2^n + 1 := Nat.add_le_add_right ih 1
                      _ ≤ 2^n + 2^n := Nat.add_le_add_left (Nat.one_le_pow n 2 (by norm_num)) (2^n)
                      _ = 2 * 2^n := by ring
                      _ = 2^(n+1) := by rw [← pow_succ']
             exact pow_le_pow_right' (by norm_num) hn_le
    · intro k hk₁ hk₂
      simp only [Finset.mem_range] at hk₁ hk₂
      -- k is in range (2^(2^n)) but not in range (2^n), so k >= 2^n
      have hk_ge : 2^n ≤ k := Nat.le_of_not_lt hk₂
      -- For such k, getBit x k = false since x < 2^(2^n)
      rw [getBit_of_lt hx hk_ge]
      simp
  rw [extend_sum]
  -- Now use binary_representation with m = 2^n
  exact (binary_representation (2^n) x hx).symm

/-! ## Asymptotic Lemmas

These lemmas are foundational bounds used in complexity-theoretic arguments,
particularly the CIKK theorem relating natural proofs to learning.
-/

/--
  Auxiliary: log n ≤ n for n ≥ 2.

  Uses the fact that k < 2^k (from Nat.lt_pow_self) and 2^{log n} ≤ n.
-/
lemma log_le_self (n : ℕ) (hn : n ≥ 2) : Nat.log 2 n ≤ n := by
  have h : Nat.log 2 n < 2^(Nat.log 2 n) := Nat.lt_pow_self (by omega : 1 < 2)
  have h2 : 2^(Nat.log 2 n) ≤ n := Nat.pow_log_le_self 2 (by omega : n ≠ 0)
  exact le_trans (le_of_lt h) h2

/-- Helper: For k ≥ 3, 2k + 1 ≤ 2^k. -/
lemma two_k_plus_one_le_two_pow (k : ℕ) (hk : k ≥ 3) : 2*k + 1 ≤ 2^k := by
  match k with
  | 0 | 1 | 2 => omega  -- k < 3
  | 3 => decide  -- 7 ≤ 8
  | 4 => decide  -- 9 ≤ 16
  | 5 => decide  -- 11 ≤ 32
  | 6 => decide  -- 13 ≤ 64
  | k + 7 =>
    -- Inductive case: 2*(k+7) + 1 ≤ 2^(k+7)
    have hk6 : k + 6 ≥ 3 := by omega
    have ih := two_k_plus_one_le_two_pow (k + 6) hk6
    -- ih: 2*(k+6) + 1 ≤ 2^(k+6)
    -- Goal: 2*(k+7) + 1 ≤ 2^(k+7) = 2 * 2^(k+6)
    have h1 : 2*(k+7) + 1 = (2*(k+6) + 1) + 2 := by ring
    have h2 : 2^(k+7) = 2 * 2^(k+6) := by rw [pow_succ]; ring
    have h3 : (2*(k+6) + 1) + 2 ≤ 2^(k+6) + 2 := Nat.add_le_add_right ih 2
    have h4 : 2^(k+6) + 2 ≤ 2 * 2^(k+6) := by
      have hpos : 2^(k+6) ≥ 2 := by
        calc 2^(k+6) ≥ 2^6 := Nat.pow_le_pow_right (by omega) (by omega)
          _ = 64 := by norm_num
          _ ≥ 2 := by omega
      omega
    omega

/-- Helper: For k ≥ 4, k^2 ≤ 2^k. Proof by direct verification for small cases
    and induction for larger values. -/
lemma sq_le_two_pow (k : ℕ) (hk : k ≥ 4) : k^2 ≤ 2^k := by
  induction k with
  | zero => omega
  | succ n ih =>
    match n with
    | 0 | 1 | 2 => omega  -- n+1 < 4
    | 3 => decide  -- 4^2 = 16 = 2^4
    | 4 => decide  -- 5^2 = 25 ≤ 32 = 2^5
    | 5 => decide  -- 6^2 = 36 ≤ 64 = 2^6
    | 6 => decide  -- 7^2 = 49 ≤ 128 = 2^7
    | n + 7 =>
      -- For n + 8 ≥ 8, use induction
      -- (n+8)^2 = (n+7)^2 + 2(n+7) + 1
      -- 2^(n+8) = 2 * 2^(n+7)
      -- By IH: (n+7)^2 ≤ 2^(n+7)
      -- Need: 2(n+7) + 1 ≤ 2^(n+7) for n ≥ 0
      have hn7 : n + 7 ≥ 4 := by omega
      have hih := ih hn7
      have hn7_ge3 : n + 7 ≥ 3 := by omega
      have hlin : 2*(n + 7) + 1 ≤ 2^(n + 7) := two_k_plus_one_le_two_pow (n + 7) hn7_ge3
      have hsum : 2^(n + 7) + 2^(n + 7) = 2^(n + 8) := by
        have : n + 8 = (n + 7) + 1 := by omega
        rw [this, pow_succ]
        ring
      have hassoc : (n + 7)^2 + 2*(n + 7) + 1 = (n + 7)^2 + (2*(n + 7) + 1) := by ring
      calc (n + 8)^2 = (n + 7)^2 + 2*(n + 7) + 1 := by ring
        _ = (n + 7)^2 + (2*(n + 7) + 1) := hassoc
        _ ≤ 2^(n + 7) + (2*(n + 7) + 1) := Nat.add_le_add_right hih _
        _ ≤ 2^(n + 7) + 2^(n + 7) := Nat.add_le_add_left hlin _
        _ = 2^(n + 8) := hsum

/-- Helper: 2^k > k*(c+1) for k ≥ c+2.
    This is key for showing 2^(m/(c+1)) > m. -/
lemma two_pow_gt_mul_c (c k : ℕ) (hk : k ≥ c + 2) : 2^k > k * (c + 1) := by
  induction k with
  | zero => omega  -- k = 0 < c + 2, contradiction
  | succ n ih =>
    match c with
    | 0 =>
      -- c = 0, need 2^(n+1) > (n+1) * 1 = n+1 for n+1 ≥ 2
      have := @Nat.lt_two_pow_self (n + 1)
      omega
    | c + 1 =>
      -- c ≥ 1, need 2^(n+1) > (n+1) * (c+2) for n+1 ≥ c+3, i.e., n ≥ c+2
      match n with
      | 0 | 1 => omega  -- n+1 < c+3 for c ≥ 1
      | 2 =>
        -- n+1 = 3, c+3 ≤ 3 means c ≤ 0, but c ≥ 1, contradiction
        omega
      | n + 3 =>
        -- n+4 ≥ c+3 means n+1 ≥ c, i.e., n ≥ c-1
        -- Goal: 2^(n+4) > (n+4) * (c+2)
        -- IH: 2^(n+3) > (n+3) * (c+2) for n+3 ≥ c+3 (i.e., n ≥ c)
        by_cases hn : n ≥ c
        · have hih := ih (by omega : n + 3 ≥ c + 1 + 2)
          -- 2^(n+4) = 2 * 2^(n+3) > 2 * (n+3) * (c+2)
          have h1 : 2^(n+4) = 2 * 2^(n+3) := by rw [pow_succ]; ring
          have h2 : 2 * (n + 3) * (c + 2) ≥ (n + 4) * (c + 2) := by
            -- 2*(n+3) = 2n+6 ≥ n+4 for n ≥ -2 ✓
            have : 2 * (n + 3) ≥ n + 4 := by omega
            exact Nat.mul_le_mul_right (c + 2) this
          have h3 : 2 * 2^(n+3) > 2 * ((n+3) * (c+2)) := Nat.mul_lt_mul_of_pos_left hih (by omega)
          have h4 : 2 * ((n+3) * (c+2)) = 2 * (n + 3) * (c + 2) := by ring
          calc 2^(n+4) = 2 * 2^(n+3) := h1
            _ > 2 * ((n+3) * (c+2)) := h3
            _ = 2 * (n + 3) * (c + 2) := h4
            _ ≥ (n + 4) * (c + 2) := h2
        · -- n < c, so n = c - 1 (since n + 4 ≥ c + 3 means n ≥ c - 1)
          -- Then n + 4 = c + 3
          have hneq : n = c - 1 := by omega
          -- Goal: 2^(n+4) > (n+4) * (c+2)
          -- Since n = c - 1, n + 4 = c + 3 (for c ≥ 1)
          have hn4 : n + 4 = c + 3 := by omega
          rw [hn4]
          -- Goal: 2^(c+3) > (c+3) * (c+2)
          -- We prove this by showing 2^(c+3) ≥ (c+3)^2 > (c+3)*(c+2)
          have hsq : (c + 3)^2 > (c + 3) * (c + 2) := by
            have h1 : (c + 3)^2 = (c + 3) * (c + 3) := sq (c + 3)
            have h2 : (c + 3) * (c + 3) > (c + 3) * (c + 2) :=
              Nat.mul_lt_mul_of_pos_left (by omega : c + 3 > c + 2) (by omega)
            calc (c + 3)^2 = (c + 3) * (c + 3) := h1
              _ > (c + 3) * (c + 2) := h2
          have h2pow : 2^(c + 3) ≥ (c + 3)^2 := by
            have hge4 : c + 3 ≥ 4 := by omega
            exact sq_le_two_pow (c + 3) hge4
          exact Nat.lt_of_lt_of_le hsq h2pow

/-- Helper: 2^k ≥ (k+1)*(c+1) for k ≥ c+2.
    This is used in the main proof of pow_c_le_exp_eventually. -/
lemma two_pow_ge_prod (c k : ℕ) (hk : k ≥ c + 2) : 2^k ≥ (k + 1) * (c + 1) := by
  induction k with
  | zero => omega
  | succ n ih =>
    -- Goal: 2^(n+1) ≥ (n+2) * (c+1) for n+1 ≥ c+2, i.e., n ≥ c+1
    match c with
    | 0 =>
      -- 2^(n+1) ≥ (n+2) * 1 = n+2 for n ≥ 1
      have h := @Nat.lt_two_pow_self (n + 1)
      omega
    | 1 =>
      -- 2^(n+1) ≥ (n+2) * 2 = 2n+4 for n ≥ 2
      match n with
      | 0 | 1 => omega  -- n+1 < 3
      | 2 => decide  -- 2^3 = 8 ≥ 8 = 4*2
      | 3 => decide  -- 2^4 = 16 ≥ 10 = 5*2
      | 4 => decide  -- 2^5 = 32 ≥ 12 = 6*2
      | n + 5 =>
        -- 2^(n+6) ≥ (n+7) * 2 = 2n+14
        have hih := ih (by omega : n + 5 ≥ 1 + 2)
        -- IH: 2^(n+5) ≥ (n+6) * 2
        -- 2^(n+6) = 2 * 2^(n+5) ≥ 2 * (n+6) * 2 = 4*(n+6) ≥ 2*(n+7) for n ≥ -5 ✓
        have h1 : 2 * 2^(n+5) ≥ 2 * ((n+6) * 2) := Nat.mul_le_mul_left 2 hih
        have h2 : 2 * ((n+6) * 2) = 4 * (n + 6) := by ring
        have h3 : 4 * (n + 6) ≥ 2 * (n + 7) := by omega
        calc 2^(n+6) = 2 * 2^(n+5) := by rw [pow_succ]; ring
          _ ≥ 2 * ((n+6) * 2) := h1
          _ = 4 * (n + 6) := h2
          _ ≥ 2 * (n + 7) := h3
          _ = (n + 7) * 2 := by ring
    | c + 2 =>
      -- 2^(n+1) ≥ (n+2) * (c+3) for n ≥ c+3
      match n with
      | 0 | 1 | 2 => omega  -- n+1 < c+4 for c ≥ 0
      | n + 3 =>
        -- n+4 ≥ c+4 means n ≥ c
        by_cases hn : n ≥ c + 1
        · -- Can use IH
          have hih := ih (by omega : n + 3 ≥ (c + 2) + 2)
          -- IH: 2^(n+3) ≥ (n+4) * (c+3)
          -- 2^(n+4) = 2 * 2^(n+3) ≥ 2 * (n+4) * (c+3)
          -- Need: 2 * (n+4) * (c+3) ≥ (n+5) * (c+3)
          -- i.e., 2*(n+4) ≥ n+5, i.e., n+3 ≥ 0 ✓
          have h1 : 2 * 2^(n+3) ≥ 2 * ((n+4) * (c+3)) := Nat.mul_le_mul_left 2 hih
          have h2 : 2 * (n + 4) ≥ n + 5 := by omega
          have h3 : 2 * ((n+4) * (c+3)) ≥ (n+5) * (c+3) := by
            calc 2 * ((n+4) * (c+3)) = (2 * (n+4)) * (c+3) := by ring
              _ ≥ (n+5) * (c+3) := Nat.mul_le_mul_right (c+3) h2
          calc 2^(n+4) = 2 * 2^(n+3) := by rw [pow_succ]; ring
            _ ≥ 2 * ((n+4) * (c+3)) := h1
            _ ≥ (n+5) * (c+3) := h3
        · -- n < c + 1, so n = c (since n+4 ≥ c+4 means n ≥ c)
          have hneq : n = c := by omega
          -- Goal: 2^(n+3+1) ≥ (n+3+1+1) * (c+2+1)
          -- Since n = c, this is 2^(c+4) ≥ (c+5) * (c+3)
          have hbound : (n + 3 + 1 + 1) * (c + 2 + 1) ≤ (n + 4)^2 := by
            -- Using n = c: (n+5)(c+3) = (c+5)(c+3) = c^2 + 8c + 15
            -- vs (n+4)^2 = (c+4)^2 = c^2 + 8c + 16
            have h1 : (n + 3 + 1 + 1) * (c + 2 + 1) = n^2 + 8*n + 15 := by
              have : c = n := hneq.symm
              subst this
              ring
            have h2 : (n + 4)^2 = n^2 + 8*n + 16 := by ring
            omega
          have hsq : (n + 4)^2 ≤ 2^(n + 4) := by
            have hge4 : n + 4 ≥ 4 := by omega
            exact sq_le_two_pow (n + 4) hge4
          have heq : n + 3 + 1 = n + 4 := by omega
          calc 2^(n + 3 + 1) = 2^(n + 4) := by rw [heq]
            _ ≥ (n + 4)^2 := hsq
            _ ≥ (n + 3 + 1 + 1) * (c + 2 + 1) := hbound

/-- Helper: 2^(c+2) ≥ 4*(c+1) -/
lemma two_pow_ge_four_mul (c : ℕ) : 2^(c + 2) ≥ 4 * (c + 1) := by
  match c with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | 3 => decide
  | c + 4 =>
    -- For c + 4, we have 2^(c+6) ≥ 4*(c+5)
    -- 2^6 = 64 ≥ 20 = 4*5, and exponential grows faster
    have h1 : 4 * (c + 5) ≤ 2^(c + 6) := by
      have hbase : 4 * 5 ≤ 2^6 := by decide
      have hgrow : 4 * (c + 5) ≤ 2^(c + 4) * 4 := by
        have : c + 5 ≤ 2^(c + 4) := by
          have := @Nat.lt_two_pow_self (c + 4)
          omega
        omega
      calc 4 * (c + 5) ≤ 2^(c + 4) * 4 := hgrow
        _ = 4 * 2^(c + 4) := by ring
        _ ≤ 2^2 * 2^(c + 4) := by norm_num
        _ = 2^(c + 6) := by rw [← pow_add]; ring_nf
    exact h1

/-- Helper: 2^(c+2) ≥ (c+1)^2 -/
lemma two_pow_ge_sq (c : ℕ) : 2^(c + 2) ≥ (c + 1)^2 := by
  match c with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | 3 => decide
  | c + 4 =>
    -- For c + 4, we have 2^(c+6) ≥ (c+5)^2
    -- 2^6 = 64 ≥ 25 = 5^2, and exponential grows faster
    have h1 : (c + 5)^2 ≤ 2^(c + 6) := by
      -- Use sq_le_two_pow for c + 5 ≥ 5 > 4
      have hge : c + 5 ≥ 4 := by omega
      have hsq := sq_le_two_pow (c + 5) hge
      calc (c + 5)^2 ≤ 2^(c + 5) := hsq
        _ ≤ 2^(c + 6) := Nat.pow_le_pow_right (by omega) (by omega)
    exact h1

/--
  **Exponential dominates polynomial**: m^c ≤ 2^m for large m.

  This is a fundamental asymptotic bound. For any fixed c ≥ 0:
  - c = 0: 1 ≤ 2^m for all m ✓
  - c = 1: m ≤ 2^m for all m ✓ (special case of Nat.lt_pow_self)
  - c ≥ 2: m^c ≤ 2^m for m ≥ some threshold depending on c

  The proof uses induction on c. The key insight is that 2^m grows faster
  than any polynomial m^c.
-/
lemma pow_c_le_exp_eventually (c : ℕ) : ∃ m₀ : ℕ, ∀ m ≥ m₀, m^c ≤ 2^m := by
  -- Use threshold 2^(c+1) which ensures m^c ≤ 2^m
  use 2^(c + 1)
  intro m hm
  induction c with
  | zero =>
    simp only [pow_zero]
    exact Nat.one_le_pow m 2 (by omega)
  | succ c _ih =>
    -- Need: m^(c+1) ≤ 2^m for m ≥ 2^(c+2)
    have hm_large : m ≥ 2^(c + 2) := hm
    have hm_ge_4 : m ≥ 4 := by
      calc m ≥ 2^(c + 2) := hm
        _ ≥ 2^2 := Nat.pow_le_pow_right (by omega) (by omega)
        _ = 4 := by norm_num

    -- m/(c+1) ≥ 4
    have h_div_bound : m / (c + 1) ≥ 4 := by
      have h1 := two_pow_ge_four_mul c
      calc m / (c + 1) ≥ 2^(c + 2) / (c + 1) := Nat.div_le_div_right hm_large
        _ ≥ (4 * (c + 1)) / (c + 1) := Nat.div_le_div_right h1
        _ = 4 := by rw [Nat.mul_comm]; exact Nat.mul_div_cancel_left 4 (by omega)

    -- 2^(m/(c+1)) ≥ (m/(c+1))^2
    have hpow_big : 2^(m/(c+1)) ≥ (m/(c+1))^2 := sq_le_two_pow (m/(c+1)) h_div_bound

    -- m/(c+1) ≥ c+1
    have h_div_ge_c : m / (c + 1) ≥ c + 1 := by
      have h1 := two_pow_ge_sq c
      calc m / (c + 1) ≥ 2^(c + 2) / (c + 1) := Nat.div_le_div_right hm_large
        _ ≥ (c + 1)^2 / (c + 1) := Nat.div_le_div_right h1
        _ = c + 1 := by rw [sq, Nat.mul_div_cancel_left _ (by omega)]

    -- (m/(c+1))^2 ≥ (c+1) * (m/(c+1))
    have hpow_ge_prod : (m/(c+1))^2 ≥ (c + 1) * (m/(c+1)) := by
      rw [sq]
      exact Nat.mul_le_mul_right (m/(c+1)) h_div_ge_c

    -- (c+1) * (m/(c+1)) ≥ m - c
    have hprod_ge : (c + 1) * (m/(c+1)) ≥ m - c := by
      have hdiv := Nat.div_add_mod m (c+1)
      have hmod : m % (c+1) ≤ c := Nat.lt_succ_iff.mp (Nat.mod_lt m (by omega))
      omega

    -- 2^(m/(c+1)) ≥ m
    -- Strategy: Use Nat.log to show m/(c+1) > log₂(m), hence 2^(m/(c+1)) > m
    have h_pow_ge_m : 2^(m/(c+1)) ≥ m := by
      -- Let k = Nat.log 2 m, so 2^k ≤ m < 2^(k+1)
      let k := Nat.log 2 m
      have hm_pos : m ≠ 0 := by omega
      have hk_lower : 2^k ≤ m := Nat.pow_log_le_self 2 hm_pos
      have hk_upper : m < 2^(k+1) := Nat.lt_pow_succ_log_self (by omega : 1 < 2) m
      -- Since m ≥ 2^(c+2), we have k ≥ c+2
      have hk_ge : k ≥ c + 2 := by
        have : 2^(c+2) < 2^(k+1) := Nat.lt_of_le_of_lt hm_large hk_upper
        by_contra hgt
        push_neg at hgt
        have hle : k + 1 ≤ c + 2 := hgt
        have : 2^(k+1) ≤ 2^(c+2) := Nat.pow_le_pow_right (by omega) hle
        omega
      -- Use two_pow_ge_prod: 2^k ≥ (k+1)*(c+1) for k ≥ c+2
      have hstrong : 2^k ≥ (k + 1) * (c + 1) := two_pow_ge_prod c k hk_ge
      -- Now 2^k / (c+1) ≥ k + 1
      have hc1_pos : c + 1 > 0 := by omega
      have hdiv_ge : 2^k / (c + 1) ≥ k + 1 := (Nat.le_div_iff_mul_le hc1_pos).mpr hstrong
      -- Hence m/(c+1) ≥ 2^k/(c+1) ≥ k + 1
      have h1 : m / (c + 1) ≥ 2^k / (c + 1) := Nat.div_le_div_right hk_lower
      have hdiv_ge_k1 : m / (c + 1) ≥ k + 1 := Nat.le_trans hdiv_ge h1
      -- Therefore 2^(m/(c+1)) ≥ 2^(k+1) > m
      have hpow_ge : 2^(m/(c+1)) ≥ 2^(k+1) := Nat.pow_le_pow_right (by omega) hdiv_ge_k1
      exact Nat.le_of_lt (Nat.lt_of_lt_of_le hk_upper hpow_ge)

    -- Finally: m^(c+1) ≤ 2^m
    have hmul_comm : (c+1) * (m/(c+1)) = (m/(c+1)) * (c+1) := Nat.mul_comm _ _
    calc m^(c+1) ≤ (2^(m/(c+1)))^(c+1) := Nat.pow_le_pow_left h_pow_ge_m (c+1)
      _ = 2^((m/(c+1)) * (c+1)) := by rw [← pow_mul]
      _ = 2^((c+1) * (m/(c+1))) := by rw [hmul_comm]
      _ ≤ 2^m := Nat.pow_le_pow_right (by omega) (Nat.mul_div_le m (c+1))

/--
  **Quasi-polynomial is subexponential**: (log n)^c ≤ n for n ≥ some n₀.

  This is the key asymptotic bound for CIKK complexity analysis.
  It follows from: log n < 2^{log n} ≤ n and m^c ≤ 2^m for large m.
-/
lemma quasipoly_le_exp (c : ℕ) : ∃ n₀ : ℕ, ∀ n ≥ n₀, (Nat.log 2 n)^c ≤ n := by
  obtain ⟨m₀, hm₀⟩ := pow_c_le_exp_eventually c
  -- Take n₀ = max (2^m₀) 2
  use max (2^m₀) 2
  intro n hn
  have hn2 : n ≥ 2 := le_trans (le_max_right _ _) hn
  let m := Nat.log 2 n
  -- n ≥ 2^m₀ implies m = log n ≥ m₀
  have hm : m ≥ m₀ := by
    have hn0 : n ≥ 2^m₀ := le_trans (le_max_left _ _) hn
    have hlog_pow : Nat.log 2 (2^m₀) = m₀ := Nat.log_pow (by omega : 1 < 2) m₀
    calc m = Nat.log 2 n := rfl
      _ ≥ Nat.log 2 (2^m₀) := Nat.log_mono_right hn0
      _ = m₀ := hlog_pow
  calc (Nat.log 2 n)^c = m^c := rfl
    _ ≤ 2^m := hm₀ m hm
    _ ≤ n := Nat.pow_log_le_self 2 (by omega : n ≠ 0)

/--
  Sum of quasi-poly and exponential is dominated by exponential (eventually).

  If f(n) ≤ 2^{(log n)^c} and g(n) = 2^n, then for large enough n:
  f(n) + g(n) ≤ 2 * 2^n = 2^{n+1}.

  The threshold depends on c.
-/
lemma quasipoly_plus_exp_le (c : ℕ) : ∃ n₀ : ℕ, ∀ n ≥ n₀,
    2^((Nat.log 2 n)^c) + 2^n ≤ 2^(n + 1) := by
  -- Get the threshold where (log n)^c ≤ n
  obtain ⟨n₀, hn₀⟩ := quasipoly_le_exp c
  use n₀
  intro n hn
  -- 2^{(log n)^c} ≤ 2^n for n ≥ n₀, and 2^n + 2^n = 2^{n+1}
  have h1 : 2^((Nat.log 2 n)^c) ≤ 2^n := by
    apply Nat.pow_le_pow_right (by omega : 2 ≥ 1)
    exact hn₀ n hn
  have h2 : 2^n + 2^n = 2^(n + 1) := by
    rw [pow_succ]
    ring
  calc 2^((Nat.log 2 n)^c) + 2^n
      ≤ 2^n + 2^n := Nat.add_le_add_right h1 _
    _ = 2^(n + 1) := h2

/--
  2^{n+1} is polynomial in 2^n.

  Specifically, 2^{n+1} = 2 * 2^n ≤ (2^n)^2 for n ≥ 1.
-/
lemma exp_succ_poly_in_exp (n : ℕ) (hn : n ≥ 1) :
    2^(n + 1) ≤ (2^n)^2 := by
  rw [pow_succ, sq]
  -- Need: 2^n * 2 ≤ 2^n * 2^n
  have h : 2 ≤ 2^n := by
    calc 2 = 2^1 := by ring
      _ ≤ 2^n := Nat.pow_le_pow_right (by omega) hn
  exact Nat.mul_le_mul_left (2^n) h

end ComplexityBarriers
