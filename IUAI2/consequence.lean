
-- import Mathlib.Data.Set.Basic

-- --The canonical connectives for a type
-- --Given as an arity indexed family
-- structure Language where
--   var_t : Type
--   con_t : Type
--   arity : con_t -> Nat

-- inductive Formula (l : Language)  where
-- | var : l.var_t -> Formula l
-- | con : (a : l.con_t) -> (Fin (l.arity a) -> Formula l) -> Formula l

-- -- def Formula.size {l} : Formula l -> Nat
-- -- | .var _ => 1
-- -- | .con a args => Fin.foldl

-- --A substitution is a mapping from vars to formulae
-- abbrev Subst (l : Language): Type := l.var_t -> Formula l

-- def Subst' {l} (σ : Subst l) : Formula l -> Formula l
-- | .var v => σ v
-- | .con s a => Formula.con s (Subst' σ ∘ a)

-- inductive PropFormula where
-- | atom : Nat -> PropFormula
-- | var : Nat -> PropFormula
-- | not : PropFormula -> PropFormula
-- | and : PropFormula -> PropFormula -> PropFormula

-- def bundleZero {α} (f : α) : (Fin 0 → α) -> α :=
--   λ _ => f

-- def bundleOne {α} (f : α -> α) : (Fin 1 → α) -> α :=
--   λ f1 => f (f1 0)

-- def bundleTwo {α} (f : α -> α -> α) : (Fin 2 → α) -> α :=
--   λ f2 => f (f2 0) (f2 1)

-- instance: Formula PropFormula := by cases




  -- λ(f : PropFormula) => match f with
  -- | .var n => Formula.var f
  -- | .atom n => Formula.cons 0 (bundleZero (PropFormula.atom n))
  -- | .not f => Formula.cons 1 (bundleOne PropFormula.not)
  -- | .and f1 f2 =>  Formula.cons 2 (bundleTwo PropFormula.and)


--Abstract consequence relation
-- class ASR {α} [Language α] (r : List α -> α -> Prop) where
--   c1 (X : List α) (a : α) : a ∈ X -> r X a
--   c2 (X Y : List α) (a : α) : r X a ∧ X ⊆ Y -> r Y a
--   c3 (X Y : List α) (a : α) : r X a ∧ ∀ b ∈ X, r Y b -> r Y a

-- --Finitary abstract consequence relation
-- class FASR {α} [Language α] (r : List α -> α -> Prop) extends ASR r where
--   c4 (X Y : List α) (a : α) : r X a -> ∃ Y ⊆ X, r Y a
