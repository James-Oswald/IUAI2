
import IUAI2.c21.PrefixCodes

-- 1. [C07] (ith order prefix code for 11111) Compute the zeroth-, first- and second-
-- order prefix codes for the binary string 11111.

#eval (E 0 (b#11111))
#eval (E 1 (b#11111))
#eval (E 2 (b#11111))

example: (E 0 (b#11111)) = b#111111111111111111111111111111111111111111111111111111111111110 := by
  rfl

example: (E 1 (b#11111)) = b#11111011111 := by
  simp_all only [E, BinStr.to_nat, Nat.to_b0, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    nat_to_l1.eq_3, Nat.succ_eq_add_one, Nat.reduceDiv, nat_to_l1.eq_2, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append, l1_to_nat.eq_2, l1_to_nat, mul_one, Nat.reduceMul, Nat.add_one_sub_one,
    List.reduceReplicate, List.flatten_cons, List.flatten_nil, List.append_nil]

example: (E 2 (b#11111)) = b#1101011111 := by
  simp_all only [E, BinStr.to_nat, Nat.to_b0, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    nat_to_l1.eq_3, Nat.succ_eq_add_one, Nat.reduceDiv, nat_to_l1.eq_2, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append, l1_to_nat.eq_3, l1_to_nat, mul_one, Nat.add_one_sub_one, List.reduceReplicate,
    List.flatten_cons, List.flatten_nil, List.append_nil]

-- 2. [C10] (Counting prefix-free sets) Prove that the number of prefix-free sets for a
-- binary alphabet is uncountable.

example : Uncountable { S : Set 𝔹* // prefix_free S } := by
  sorry

-- 3. [C12] (Unique decodability) Given strings x,y ∈ B∗, which of the following are
-- uniquely decodable? xy, xy, x′y, xy′, ¯x¯y, x′y′. In each case, provide a proof or a
-- counterexample.



-- TODO: Formally define Uniquely Decodable in PrefixCodes.lean


-- 4. [C15] (ith order codes are prefix-free) Prove that the family of codes E_i (2.1.4)
-- are prefix-free for all i ∈ Nat.

example (i : ℕ) : prefix_free {E i j | j : 𝔹*} := by
  -- follows directly from Lemma 2.1.6
  exact (PrefixCode_E_i i).prefix_free

-- 5. [C10] (Sequence to real number) Given the function f defined in (2.1.8), find
-- the pre-image f −1(1/3), and prove that f is a surjection.

-- 6. [C07] (Cylinder set inclusions) Prove that Γy ⊆ Γx if and only if x ⊑ y.

-- 7. [C20] (Complete prefix codes can have holes) Construct a complete prefix
-- code P (Definition 2.5.19) for which S
-- · x∈P Γx̸ = X ∞. Show that equality holds iff P is
-- finite. Construct a complete prefix code P such that X ∞ \S
-- · x∈P Γx is uncountable. Is
-- it possible to construct a complete prefix code P such that X ∞ \S
-- · x∈P Γx is of positive
-- measure?
