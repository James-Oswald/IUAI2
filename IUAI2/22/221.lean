-- import Mathlib.Data.Set.Basic
-- import Mathlib.Data.Set.Lattice
-- import Mathlib.Order.Interval.Set.Defs
-- import Mathlib.Data.Real.Basic
-- import Mathlib.Data.Finite.Defs
-- import Mathlib.Data.Set.Finite.Basic

import Mathlib

-- The type of events
variable {Ωt : Type}

-- The carrying type of a σ-algebra
variable (F : Set (Set Ωt))


abbrev pd (A B : Set Ωt) : Prop := A ∩ B = ∅
-- Pairwise disjoint sequence of outcomes
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

-- Definition 2.2.2 (Measurable space) A measurable space is a pair (Ω,F) where F
-- is a σ-algebra on Ω.
structure MeasureSpace where
  Ωt : Type
  F : Set (Set Ωt)
  σ_algebra: SigmaAlgebra F

-- Omega as a set
def MeasureSpace.Ω (M : MeasureSpace) : Set M.Ωt := Set.univ

class ProbabilityMeasure {M : MeasureSpace} (P : Set M.Ωt -> ℝ) where
  excess : ∀ A ∉ M.F, P A = 0 -- Domain hacking because im annoyed
  normalization: P M.Ω = 1
  countable_add (A : Nat -> Set M.Ωt)
    (PD : cpd A) (H : ∀ i, A i ∈ M.F) :
    P (⋃ i, A i) = (∑' i, P (A i))

-- class SemiProbabilityMeasure {M : MeasureSpace} (P : Set M.Ωt -> Real) where
--   normalization: P M.Ω ≤ 1
--   countable_add (A : Nat -> M.F) : P (⋃ i, A i) = (∑' i, P (A i))

-- class SemiMeasure {M : MeasureSpace} (P : Set M.Ωt -> Real) where
--   normalization: P M.Ω ≤ 1
--   countable_add (A : Nat -> M.F) : P (⋃ i, A i) ≤ (∑' i, P (A i))

structure ProbSpace extends MeasureSpace where
  P : Set Ωt -> Real
  pm : ProbabilityMeasure P

lemma ProbSpace.fin_add {p : ProbSpace}
(A B : Set p.Ωt) (H1 : A ∈ p.F) (H2 : B ∈ p.F) (H3 : pd A B) :
p.P (A ∪ B) = p.P A + p.P B := by
  let f : Nat -> Set p.Ωt
    | 0 => A | 1 => B | _ => ∅
  have H4: cpd f := by
    simp [cpd];
    grind only [= Set.mem_empty_iff_false, = Set.mem_inter_iff]
  have H5: inF p.F f := by
    simp [inF]
    intro i
    simp [f]
    split
    exact H1
    exact H2
    apply p.σ_algebra.F_empty
  have H6 := p.pm.countable_add f H4 H5




example {p : ProbSpace} : p.P ∅ = 0 := by
  let f : Nat -> Set p.Ωt := λ _ => ∅
  have H1: cpd f := by
    simp [cpd];
    grind only [= Set.mem_empty_iff_false, = Set.mem_inter_iff]
  have H2: inF p.F f := by
    simp [inF];
    intro i
    apply p.σ_algebra.F_empty
  have h := p.pm.countable_add f H1 H2
  simp_all only [forall_const, Set.iUnion_empty, tsum_const, Nat.card_eq_zero_of_infinite, zero_nsmul, f]

example {p : ProbSpace} (A B : Set p.Ωt) (H1 : A ∈ p.F) (H2 : B ∈ p.F) :
p.P (A ∪ B) = p.P A + p.P B - p.P (A ∩ B) := by
  let f : Nat -> Set p.Ωt :=
    λ i => if i = 0 then A else if i = 1 then B else A ∩ B
  have H3: cpd f := by sorry
  have H4: inF p.F f := by sorry
  have h := p.pm.countable_add f H3 H4
