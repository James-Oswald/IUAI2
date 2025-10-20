-- import Mathlib.Data.Set.Basic
-- import Mathlib.Data.Set.Lattice
-- import Mathlib.Order.Interval.Set.Defs
-- import Mathlib.Data.Real.Basic
-- import Mathlib.Data.Finite.Defs
-- import Mathlib.Data.Set.Finite.Basic

import Mathlib


-- Utility Lemmas
lemma iUnion_split {α} (s : ℕ → Set α) :
  (⋃ n, s n) = s 0 ∪ (⋃ n, s (n + 1)) := by
  symm
  apply sup_iSup_nat_succ s

lemma iUnion_split_2 {α} (s : ℕ → Set α) :
  (⋃ n, s n) = s 0 ∪ s 1 ∪ (⋃ n, s (n + 2)) := by
  rw [iUnion_split, iUnion_split]
  grind only [= Set.mem_union, cases Or]

lemma tsum_split {f : ℕ -> Real} {H : Summable f}:
  (∑' i, f i) = f 0 + (∑' n, f (n + 1)) := by
  apply Summable.tsum_eq_zero_add
  exact H

lemma tsum_split_2 {f : ℕ -> Real} {H : Summable f} :
  (∑' i, f i) = f 0 + f 1 + (∑' i, f (i + 2)) := by
  have H := (Summable.sum_add_tsum_nat_add 2 H)
  have H' : Finset.range 2 = {0, 1} := by rfl
  rw [H', Finset.sum_pair] at H
  symm
  exact H
  simp only [ne_eq, zero_ne_one, not_false_eq_true]


section SigmaAlgebra
-- The type of events
variable {Ωt : Type}

-- The carrying type of a σ-algebra
variable (F : Set (Set Ωt))

-- Pairwise disjoint
abbrev pd (A B : Set Ωt) : Prop := A ∩ B = ∅

-- countable sequence Pairwise disjoint
abbrev cpd (A : Nat -> Set Ωt) : Prop := ∀ i j, i ≠ j -> pd (A i) (A j)

abbrev inF (A : Nat -> Set Ωt) : Prop := ∀ i, A i ∈ F

-- Definition 2.2.1 (σ-algebra)
-- Given a set Ω (whose elements are called outcomes), a
-- collection F of subsets of Ω is called a σ-algebra if it satisfies the following axioms:
-- (i) Contains the empty set: ∅ ∈ F.
-- (ii) Closed under countable union: If A1,A2,... ∈ F, then U^∞_n=1 A_n ∈ F.
-- (iii) Closed under complement: If A ∈ F, then Ω\A =: Aᶜ ∈ F.
class SigmaAlgebra : Prop where
  F_empty : ∅ ∈ F
  closed_countable_union (A : Nat -> Set Ωt) : inF F A -> (⋃ i, A i) ∈ F
  closed_comp : ∀ A ∈ F, Aᶜ ∈ F

lemma SigmaAlgebra.F_univ [SigmaAlgebra F] : Set.univ ∈ F := by
  rw [<-Set.compl_empty]
  apply SigmaAlgebra.closed_comp
  exact SigmaAlgebra.F_empty

--Note that a σ-algebra F is also closed under countable intersection, due to De Morgan’s
-- law ⋂^∞_n=1 A_n = (U^∞_n=1 A^c_n)^c.
lemma SigmaAlgebra.closed_countable_inter [SigmaAlgebra F] (A : Nat -> Set Ωt) :
(∀i, A i ∈ F) -> (⋂ i, A i) ∈ F:= by
  intros A
  rw [Set.iInter_eq_compl_iUnion_compl]
  apply SigmaAlgebra.closed_comp
  apply SigmaAlgebra.closed_countable_union
  intro i
  apply SigmaAlgebra.closed_comp
  exact A i

lemma SigmaAlgebra.closed_union [SigmaAlgebra F]
(A B : Set Ωt) (H1: A ∈ F) (H2 : B ∈ F):
A ∪ B ∈ F := by
  let f : Nat -> Set Ωt
    | 0 => A | 1 => B | _ => ∅
  have H := @SigmaAlgebra.closed_countable_union _ F _ f
  have H.inF : inF F f := by
    simp [inF]
    intro i
    simp [f]
    split
    exact H1
    exact H2
    apply SigmaAlgebra.F_empty
  replace H := H H.inF
  rw [iUnion_split_2] at H
  simp only [Set.iUnion_empty, Set.union_empty, f] at H
  exact H

lemma SigmaAlgebra.closed_inter [SigmaAlgebra F]
(A B : Set Ωt) (H1: A ∈ F) (H2 : B ∈ F):
A ∩ B ∈ F := by
  rw [Set.inter_eq_compl_compl_union_compl]
  apply SigmaAlgebra.closed_comp
  apply SigmaAlgebra.closed_union
  apply SigmaAlgebra.closed_comp
  exact H1
  apply SigmaAlgebra.closed_comp
  exact H2

lemma SigmaAlgebra.closed_diff [SigmaAlgebra F]
(A B : Set Ωt) (H1: A ∈ F) (H2 : B ∈ F):
A \ B ∈ F := by
  rw [Set.diff_eq]
  apply SigmaAlgebra.closed_inter
  exact H1
  apply SigmaAlgebra.closed_comp
  exact H2

end SigmaAlgebra

-- Definition 2.2.2 (Measurable space) A measurable space is a pair (Ω,F) where F
-- is a σ-algebra on Ω.
structure MeasureSpace where
  Ωt : Type
  F : Set (Set Ωt)
  σ_algebra: SigmaAlgebra F

-- Omega as a set
def MeasureSpace.Ω (M : MeasureSpace) : Set M.Ωt := Set.univ

class ProbabilityMeasure {M : MeasureSpace} (P : Set M.Ωt -> ℝ) where
  normalization: P M.Ω = 1
  countable_add (A : Nat -> Set M.Ωt) :
    cpd A ->
    inF M.F A ->
    Summable (P ∘ A) ->
    P (⋃ i, A i) = (∑' i, P (A i))
  -- Possibly redundant, probably forced by normalization
  -- excess : ∀ A ∉ M.F, P A = 0

-- class SemiProbabilityMeasure {M : MeasureSpace} (P : Set M.Ωt -> Real) where
--   normalization: P M.Ω ≤ 1
--   countable_add (A : Nat -> M.F) : P (⋃ i, A i) = (∑' i, P (A i))

-- class SemiMeasure {M : MeasureSpace} (P : Set M.Ωt -> Real) where
--   normalization: P M.Ω ≤ 1
--   countable_add (A : Nat -> M.F) : P (⋃ i, A i) ≤ (∑' i, P (A i))

structure ProbSpace extends MeasureSpace where
  P : Set Ωt -> Real
  pm : ProbabilityMeasure P

variable {p : ProbSpace}
variable (A : Set p.Ωt) (AinF : A ∈ p.F)
variable (B : Set p.Ωt) (BinF : B ∈ p.F)

-- TODO: probably should be inlined
lemma ProbSpace.p_ite {α : Type} (p : ProbSpace) {P : α -> Prop} [DecidablePred P] {A B : Set p.Ωt} (a : α):
  p.P (if _ :  P a then A else B) = if P a then p.P A else p.P B := by
  by_cases h : P a
  . simp [h]
  . simp [h]

lemma ProbSpace.p_empty_zero (p : ProbSpace) : p.P ∅ = 0 := by
  let f : Nat -> Set p.Ωt := λ _ => ∅
  have H1: cpd f := by
    simp [cpd];
    grind only [= Set.mem_empty_iff_false, = Set.mem_inter_iff]
  have H2: inF p.F f := by
    simp [inF];
    intro i
    apply p.σ_algebra.F_empty
  have H3 : Summable (p.P ∘ f) := by
    have: HasSum (p.P ∘ f) 0 := by
      have: ∀ b ∉ (∅ : Finset Nat), (p.P ∘ f) b = 0 := by
        intros b H
        simp [f]
        exact p.p_empty_zero
      have := hasSum_sum_of_ne_finset_zero this
      rw [Finset.sum_empty] at this
      exact this
    exact this.summable
  have h := p.pm.countable_add f H1 H2 H3
  simp_all only [forall_const, Set.iUnion_empty, tsum_const, Nat.card_eq_zero_of_infinite, zero_nsmul, f]

lemma ProbSpace.fin_add (p : ProbSpace)
(A : Finset (Set p.Ωt)) (H1 : ∀ a ∈ A, a ∈ p.F) (H2 : ∀ a ∈ A, ∀ b ∈ A, a ≠ b -> pd a b) :
  p.P (⋃ a ∈ A, a) = (∑ a ∈ A, p.P a) := by

  sorry
  -- -- Proof Sketch: construct a sequence up to the cardinality of the finset, mapping each index to the corresponding
  -- -- element in the finset, and all other indices to the empty set. Prove that this sequence is pairwise disjoint,
  -- -- its elements are in the sigma-algebra, and that the series of their probabilities is summable. With this,
  -- -- we have countable additivity. Finally, we can show that the union and sum over the finset is equal to the union
  -- -- and sum over the sequence respectively, giving us finite additivity.
  -- let f (i : Nat): Set p.Ωt := if h : i < A.toList.length then A.toList.get ⟨i, h⟩ else ∅
  -- have cpd_f : cpd f := by
  --   simp only [cpd, ne_eq];
  --   intros i j H
  --   by_cases hi : i < A.card
  --   --have : (f i) ∈ A := Finset.mem_toList.mp (List.get_mem A.toList ⟨i, by simp [hi]⟩)
  --   sorry
  --   sorry
  -- have in_f : inF p.F f := by
  --   simp [inF]
  --   intro i
  --   by_cases hi : i < A.card
  --   . simp [f, hi]
  --     apply H1
  --     apply Finset.mem_toList.mp (List.get_mem A.toList ⟨i, by simp [hi]⟩)
  --   . simp [f, hi]
  --     apply p.σ_algebra.F_empty
  -- have summable_f : Summable (p.P ∘ f) := by
  --   have: HasSum (p.P ∘ f) (∑ (i : Fin A.card), (p.P ∘ f) i) := by
  --     have: ∀ b ∉ Finset.range A.card, (p.P ∘ f) b = 0 := by
  --       intros b H
  --       simp [f]
  --       have hb : ¬ b < A.card := by
  --         intro h; apply H; simp [h]
  --       simp [hb]
  --       exact p.p_empty_zero
  --     have := hasSum_sum_of_ne_finset_zero this
  --     rw [Finset.sum_range] at this
  --     exact this
  --   exact this.summable
  -- have H := p.pm.countable_add f cpd_f in_f summable_f
  -- have : ∑' i : Nat, p.P (f i) = ∑' i : Nat, (p.P ∘ f) i := by rfl
  -- have H2: (∑ a ∈ A, p.P a) = (∑' i : Nat, p.P (f i)) := by
  --   rw [this, <-Summable.sum_add_tsum_nat_add (A.card) summable_f]
  --   simp only [Finset.length_toList, List.get_eq_getElem, Function.comp_apply, add_lt_iff_neg_right,
  --     not_lt_zero', ↓reduceDIte, tsum_const, Nat.card_eq_zero_of_infinite, zero_nsmul, add_zero, f]
  --   --rw [<-map_sum p.P _ A.toList]
  --   clear * - f
  --   simp only [Finset.sum_range, Fin.is_lt, ↓reduceDIte]
  --   sorry

  -- --have := Summable.sum_add_tsum_nat_add A.card summable_f
  -- rw [<-H2] at H
  -- sorry


lemma ProbSpace.dual_add (p : ProbSpace)
(A B : Set p.Ωt) (H1 : A ∈ p.F) (H2 : B ∈ p.F) (H3 : pd A B) :
p.P (A ∪ B) = p.P A + p.P B := by
  -- Proof Sketch: Define a sequence of sets f such that f(0) = A, f(1) = B, and f(n) = ∅ for n > 1.
  -- Prove that this sequence is pairwise disjoint, its elements are in the sigma-algebra, and that the series
  -- of their probabilities is summable. With this, we have countable additivity. By separating out the first two terms
  -- of the union and the sum, we can show double additivity.
  let f : Nat -> Set p.Ωt
    | 0 => A | 1 => B | _ => ∅
  have H4: cpd f := by
    simp only [cpd, ne_eq];
    grind only [= Set.mem_empty_iff_false, = Set.mem_inter_iff]
  have H5: inF p.F f := by
    simp [inF]
    intro i
    simp only [f]
    split
    exact H1
    exact H2
    apply p.σ_algebra.F_empty
  have H6 : Summable (p.P ∘ f) := by
    have: HasSum (p.P ∘ f) (p.P A + p.P B) := by
      have: ∀ b ∉ ({0, 1} : Finset Nat), (p.P ∘ f) b = 0 := by
        intros b H
        cases b
        . contradiction
        . case succ n' =>
            cases n'
            . contradiction
            . simp [f]; exact p.p_empty_zero
      have := hasSum_sum_of_ne_finset_zero this
      rw [Finset.sum_pair] at this
      exact this
      simp only [ne_eq, zero_ne_one, not_false_eq_true]
    exact this.summable
  have H7 := p.pm.countable_add f H4 H5 H6
  rw [iUnion_split_2, @tsum_split_2] at H7
  simp [f] at H7
  exact H7
  exact H6

example {p : ProbSpace} (A B : Set p.Ωt) (H1 : A ∈ p.F) (H2 : B ∈ p.F) :
p.P (A ∪ B) = p.P A + p.P B - p.P (A ∩ B) := by
  let a1 : Set p.Ωt := A \ B
  let a2 : Set p.Ωt := B \ A
  let a3 : Set p.Ωt := A ∩ B
  have d12 : pd a1 a2 := by
    grind only [= Set.mem_empty_iff_false, = Set.mem_inter_iff, = Set.mem_diff]
  have d13 : pd a1 a3 := by
    grind only [= Set.mem_empty_iff_false, = Set.mem_inter_iff, = Set.mem_diff]
  have d23 : pd a2 a3 := by
    grind only [= Set.mem_empty_iff_false, = Set.mem_inter_iff, = Set.mem_diff]
  sorry
