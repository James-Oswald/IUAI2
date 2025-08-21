import Mathlib

variable {Ω_t : Type}
abbrev Ω := @Set.univ _ Ω_t
variable (F : Set (Set Ω_t))

-- Definition 2.2.1 (σ-algebra)
-- Given a set Ω (whose elements are called outcomes), a
-- collection F of subsets of Ω is called a σ-algebra if it satisfies the following axioms:
-- (i) Contains the empty set: ∅ ∈ F.
-- (ii) Closed under countable union: If A1,A2,... ∈ F, then U^∞_n=1 A_n ∈ F.
-- (iii) Closed under complement: If A ∈ F, then Ω\A =: Aᶜ ∈ F.
class SigmaAlgebra where
  F_empt : (∅ : Set Ω_t) ∈ F
  closed_coutable_union : ∀ s ⊆ F, (⋃₀ s) ∈ F
  closed_comp : ∀ A ∈ F, Aᶜ ∈ F

lemma SigmaAlgebra.F_univ [SigmaAlgebra F] : Set.univ ∈ F := by
  rw [<-Set.compl_empty]
  apply SigmaAlgebra.closed_comp
  exact SigmaAlgebra.F_empt

--Note that a σ-algebra F is also closed under countable intersection, due to De Morgan’s
-- law T∞n=1An = (S∞n=1Acn)c.
lemma SigmaAlgebra.closed_coutable_inter [SigmaAlgebra F] : ∀ s ⊆ F, (⋂₀ s) ∈ F := by
  intros s H
  rw [Set.sInter_eq_compl_sUnion_compl]
  have H : (compl '' s) ⊆ F := by grind

  --exact SigmaAlgebra.closed_coutable_union (compl '' s)


-- A sigma algebra is a type of outcomes bundled with a sigma algebra
-- structure MeasureSpace where
--   Ω : Type
--   A : SigmaAlg Ω

-- abbrev UnitInterval := {x : ℝ // x ∈ Set.Icc (0 : ℝ) (1 : ℝ) }


-- structure ProbSpace where
--   M : MeasureSpace
--   P : () UnitInterval
--   Po1 : (P Set.univ (SigmaAlg.max M.Ω )) = 1


--  ProbMeasure (P : {M : MeasureSpace} -> M.A.F -> UnitInterval) where
--   normal: P
