import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Set.Finite.Basic

variable {Ω_t : Type}
variable (F : Set (Set Ω_t))

-- instance [Finite Ω_t] : Finite (Set Ω_t) := inferInstance
-- -- instance [Finite Ω_t] : Finite (Set (Set Ω_t)) := by

-- --   sorry

-- Definition 2.2.1 (σ-algebra)
-- Given a set Ω (whose elements are called outcomes), a
-- collection F of subsets of Ω is called a σ-algebra if it satisfies the following axioms:
-- (i) Contains the empty set: ∅ ∈ F.
-- (ii) Closed under countable union: If A1,A2,... ∈ F, then U^∞_n=1 A_n ∈ F.
-- (iii) Closed under complement: If A ∈ F, then Ω\A =: Aᶜ ∈ F.
class SigmaAlgebra : Prop where
  F_empty : (∅ : Set Ω_t) ∈ F
  closed_countable_union : ∀ s ⊆ F, (⋃₀ s) ∈ F
  closed_comp : ∀ A ∈ F, Aᶜ ∈ F

instance {Ω_t : Type} [Finite Ω_t] {F : Set (Set Ω_t)} [SigmaAlgebra F] : Decidable (SigmaAlgebra F)

lemma SigmaAlgebra.F_univ [SigmaAlgebra F] : Set.univ ∈ F := by
  rw [<-Set.compl_empty]
  apply SigmaAlgebra.closed_comp
  exact SigmaAlgebra.F_empty

--Note that a σ-algebra F is also closed under countable intersection, due to De Morgan’s
-- law ⋂^∞_n=1 A_n = (U^∞_n=1 A^c_n)^c.
lemma SigmaAlgebra.closed_countable_inter [SigmaAlgebra F] : ∀ s ⊆ F, (⋂₀ s) ∈ F := by
  intros s H
  rw [Set.sInter_eq_compl_sUnion_compl]
  apply SigmaAlgebra.closed_comp
  apply SigmaAlgebra.closed_countable_union
  simp [Set.subset_def]
  intro a H2
  have H3: a ∈ F := by grind only [= Set.subset_def]
  exact SigmaAlgebra.closed_comp a H3


-- Definition 2.2.2 (Measurable space) A measurable space is a pair (Ω,F) where F
-- is a σ-algebra on Ω.
structure MeasureSpace where
  Ω_t : Type
  F : Set (Set Ω_t)
  σ_algebra: SigmaAlgebra F

def MeasureSpace.Ω (M : MeasureSpace) : Set M.Ω_t := Set.univ

abbrev MeasureSpace.E (M : MeasureSpace) : Type := Subtype M.F
abbrev MeasureSpace.A (M : MeasureSpace) (A : Set M.Ω_t) (H : A ∈ M.F): M.E := ⟨A, H⟩
abbrev MeasureSpace.Ωₐ (M : MeasureSpace) : M.E := ⟨M.Ω, M.σ_algebra.F_univ⟩

abbrev UnitInterval := {x : Real // x ∈ Set.Icc (0 : Real) (1 : Real) }

class ProbabilityMeasure {M : MeasureSpace} (P : M.E -> UnitInterval) where
  normalization: P M.Ωₐ = (1 : Real)
  countable_add: P



-- structure ProbSpace where
--   M : MeasureSpace
--   P : () UnitInterval
--   Po1 : (P Set.univ (SigmaAlg.max M.Ω )) = 1


--  ProbMeasure (P : {M : MeasureSpace} -> M.A.F -> UnitInterval) where
--   normal: P
