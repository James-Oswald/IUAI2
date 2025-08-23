-- import Mathlib.Data.Set.Basic
-- import Mathlib.Data.Set.Lattice
-- import Mathlib.Order.Interval.Set.Defs
-- import Mathlib.Data.Real.Basic
-- import Mathlib.Data.Finite.Defs
-- import Mathlib.Data.Set.Finite.Basic

import Mathlib

variable {Ω_t : Type}
variable (F : Set (Set Ω_t))

instance [Fintype Ω_t] : Fintype (Set Ω_t) := inferInstance
instance [Fintype Ω_t] : Fintype (Set (Set Ω_t)) := inferInstance

-- Definition 2.2.1 (σ-algebra)
-- Given a set Ω (whose elements are called outcomes), a
-- collection F of subsets of Ω is called a σ-algebra if it satisfies the following axioms:
-- (i) Contains the empty set: ∅ ∈ F.
-- (ii) Closed under countable union: If A1,A2,... ∈ F, then U^∞_n=1 A_n ∈ F.
-- (iii) Closed under complement: If A ∈ F, then Ω\A =: Aᶜ ∈ F.
class SigmaAlgebra : Prop where
  F_empty : (∅ : Set Ω_t) ∈ F
  closed_countable_union : ∀ (A : Nat -> F), (⋃ i, A i) ∈ F
  closed_comp : ∀ A ∈ F, Aᶜ ∈ F

-- instance [Fintype Ω_t] : Decidable (∅ ∈ F) := by
--   apply Set.decidableMemOfFintype F
-- instance {Ω_t : Type} [Fintype Ω_t] {F : Set (Set Ω_t)} [SigmaAlgebra F] :
-- Decidable (SigmaAlgebra F) := by


lemma SigmaAlgebra.F_univ [SigmaAlgebra F] : Set.univ ∈ F := by
  rw [<-Set.compl_empty]
  apply SigmaAlgebra.closed_comp
  exact SigmaAlgebra.F_empty

--Note that a σ-algebra F is also closed under countable intersection, due to De Morgan’s
-- law ⋂^∞_n=1 A_n = (U^∞_n=1 A^c_n)^c.
lemma SigmaAlgebra.closed_countable_inter [SigmaAlgebra F] :
∀ (A : Nat -> F), (⋂ i, A i) ∈ F := by
  intros A
  rw [Set.iInter_eq_compl_iUnion_compl]
  apply SigmaAlgebra.closed_comp
  let A' (i : Nat) : F := ⟨(A i)ᶜ, by
    apply SigmaAlgebra.closed_comp
    simp only [Subtype.coe_prop]⟩
  apply SigmaAlgebra.closed_countable_union A'

-- Definition 2.2.2 (Measurable space) A measurable space is a pair (Ω,F) where F
-- is a σ-algebra on Ω.
structure MeasureSpace where
  Ω_t : Type
  F : Set (Set Ω_t)
  σ_algebra: SigmaAlgebra F

-- Omega as a set
def MeasureSpace.Ω (M : MeasureSpace) : Set M.Ω_t := Set.univ
-- Omega as a set inside the sigma algebra
abbrev MeasureSpace.Ωₐ (M : MeasureSpace) : M.F := ⟨M.Ω, M.σ_algebra.F_univ⟩
abbrev MeasureSpace.Emptyₐ (M : MeasureSpace) : M.F := ⟨∅, M.σ_algebra.F_empty⟩
abbrev MeasureSpace.UA (M : MeasureSpace) (A : Nat -> M.F) : M.F :=
  ⟨(⋃ i, (A i)), by apply M.σ_algebra.closed_countable_union⟩

class ProbabilityMeasure {M : MeasureSpace} (P : M.F -> Real) where
  normalization: P M.Ωₐ = 1
  countable_add (A : Nat -> M.F) : P (M.UA A) = (∑' i, P (A i))

class SemiProbabilityMeasure {M : MeasureSpace} (P : M.F -> Real) where
  normalization: P M.Ωₐ ≤ 1
  countable_add (A : Nat -> M.F) : P (M.UA A) = (∑' i, P (A i))

class SemiMeasure {M : MeasureSpace} (P : M.F -> Real) where
  normalization: P M.Ωₐ ≤ 1
  countable_add (A : Nat -> M.F) : P (M.UA A) ≤ (∑' i, P (A i))

structure ProbSpace where
  M : MeasureSpace
  P : M.F -> Real
  pm : ProbabilityMeasure P

example {p : ProbSpace} : p.P p.M.Emptyₐ = 0 := by
  have h := p.pm.countable_add (λ _ => p.M.Emptyₐ)
  rw [MeasureSpace.UA, MeasureSpace.Emptyₐ] at h
  simp_all only [Set.iUnion_empty, tsum_const, Nat.card_eq_zero_of_infinite, zero_nsmul]

example {p : ProbSpace} (A B : p.M.F) : p.P (A ∪ B) = p.P A + p.P B := by
  have h := p.pm.countable_add (λ i => if i = 0 then A else B)
  rw [MeasureSpace.UA, Set.iUnion_singleton, Set.iUnion_singleton] at h
  simp_all only [if_pos rfl, tsum_singleton, Nat.card_eq_one_of_finite, one_nsmul]
  -- Note: This assumes that A and B are disjoint. If they are not, we need to use the inclusion-exclusion principle.
