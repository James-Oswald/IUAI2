
import Mathlib

--The type of possibly infinite binary strings

def BinStr : Type := Stream'.Seq Bool

@[simp]
def BinStr.isFinite (b : BinStr) : Prop := b.Terminates

def BinStr.len (b : BinStr) (H : b.isFinite) : Nat := b.length H

def FinBinStrSet : Set BinStr := {b : BinStr | b.isFinite}

notation "𝔹*" => FinBinStrSet

def FinBinStrSetN (n : Nat) : Set BinStr :=
  {b : BinStr | b.isFinite ∧ ((H : b.isFinite) -> b.len H = n)}

prefix:max "𝔹^" => FinBinStrSetN

#check 𝔹^3

-- Some simple properties on finite binary strings

example : 𝔹^3 ⊆ 𝔹* := by
    simp only [FinBinStrSetN, BinStr.isFinite, FinBinStrSet, Set.setOf_subset_setOf, and_imp]
    intro a H _
    exact H

example : ∀n, 𝔹^n ⊆ 𝔹* := by
    intro n
    simp only [FinBinStrSetN, BinStr.isFinite, FinBinStrSet, Set.setOf_subset_setOf, and_imp]
    intro a H _
    exact H

example : (⋃ (n : Nat), 𝔹^n) = 𝔹* := by
    simp [FinBinStrSet, FinBinStrSetN]
    apply Set.ext
    intro x
    simp_all only [Set.mem_iUnion, Set.mem_setOf_eq, exists_and_left, and_iff_left_iff_imp,
      forall_true_left, exists_eq', implies_true]


-- The length of the binary representation of n
@[simp]
def l (n : Nat) : Nat :=
    (Nat.log2 n) + 1

-- The ith binary digit of n
@[simp]
def Bi (n i : Nat) : Nat :=
    (n ⌊/⌋ 2^((l n) - i)) % 2

-- Bi only returns 0 or 1
lemma Bi_01 (n i : Nat) : Bi n i ≤ 1 := by
    simp only [Bi]
    have H := @Nat.mod_lt (n ⌊/⌋ 2 ^ (l n - i) % 2) 2
        (by simp only [gt_iff_lt, Nat.ofNat_pos])
    omega

-- The first digit of every binary number representation is 1
lemma Bi_one_one (n : Nat) (H : n > 0) : Bi n 1 = 1 := by
    simp_all [Bi, l]
    have H3 := @Nat.log2_self_le n (by omega)
    sorry

def Bu (n : Nat) : List Nat :=
    List.range (l n + 1) |>.tail |>.map (Bi n ·)

-- The binary representation of n contains only 0s and 1s
lemma Bu_01 (n : Nat) : ∀e ∈ Bu n, e ≤ 1 := by
    intro e he
    simp_all only [
      Bu, Bi, l,
      Nat.floorDiv_eq_div, List.tail_range,
      add_tsub_cancel_right, List.mem_map,
      List.mem_range'_1]
    omega

-- The binary representation of n
def B (n : Nat) : BinStr :=


-- Function that produces the binary representation of n
def cbu (n : Nat) : List Nat :=
    Bu (n + 1) |>.tail

-- The binary representation of n contains only 0s and 1s
lemma cbu_01 (n : Nat) : ∀e ∈ cbu n, e ≤ 1 := by
    intro e H
    simp only [cbu] at H
    apply Bu_01 (n + 1)
    exact List.mem_of_mem_tail H

-- The canonical bijection between binary strings and natural numbers
def cb (n : Nat) : BinString :=
    ⟨cbu n, cbu_01 n⟩

abbrev v : Nat := 6
#eval l v
#eval Bi v 1
#eval B v
#eval cb v



theorem canonicalBijection : Function.Bijective cb := by
    constructor
    . case left =>
      simp [Function.Injective]
      intro a b
      sorry
    . case right =>
      sorry
