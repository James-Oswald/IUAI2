
import Mathlib.Data.Set.Defs
import IUAI2.c21.BinStr


/--
Sets of binary strings
-/


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

lemma : ∀n, 𝔹^n ⊆ 𝔹* := by
    intro n
    simp only [FinBinStrSetN, BinStr.isFinite, FinBinStrSet, Set.setOf_subset_setOf, and_imp]
    intro a H _
    exact H

lemma : (⋃ (n : Nat), 𝔹^n) = 𝔹* := by
    simp [FinBinStrSet, FinBinStrSetN]
    apply Set.ext
    intro x
    simp_all only [Set.mem_iUnion, Set.mem_setOf_eq, exists_and_left, and_iff_left_iff_imp,
      forall_true_left, exists_eq', implies_true]
