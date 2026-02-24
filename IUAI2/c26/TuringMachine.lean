
import Mathlib
import IUAI2.c21.BinStr

-- Hutter Textbook TM
class TM (_ : Type) where
  Q : Type
  Q_fin : Fintype Q
  Γ : Type
  Γ_fin : Fintype Γ
  A : Set Γ --Alphabet
  δ : Q × Γ -> Option (Q × Γ × Fin 2)
  -- q0 ∈ Q is the start state that the Turing machine is initialized in on the first time step.
  q0 : Q
  B : Γ
  B_not_in_A : B ∉ A
  -- The set of final / accepting states
  F : Set Q

-- The type of tapes for a TM
abbrev TM.Tape (M: Type) [TM M] : Type := Stream' M.Γ

inductive Symb where
| bit : Bool -> Symb
| blank : Symb

structure TMC where
  Q : Type
  Q_fin : Fintype Q
  δ : Q × Symb -> Option (Q × Symb × Fin 2)
  F : Set Q


-- The full state of a TM at a single timestep
structure TM.Config (M: TM) where
  state: M.Q
  tape: M.Tape
  head : Nat

--Single step the TM
def TM.step (M : TM) (C: M.Config): Option M.Config :=
  -- Read the symbol at the head
  let symbol : M.Γ := C.tape C.head
  let next : Option (M.Q × M.Γ × Fin 2) := (M.δ ⟨C.state, symbol⟩)
  if H : next.isSome then
    let ⟨nState, nSymb, dir⟩ := next.get H
    let nTape := (C.tape.take C.head) ++ₛ ((C.tape.drop C.head).cons nSymb)
    let nHead := match dir with | 0 => C.head.pred | 1 => C.head.succ
    some ⟨nState, nTape, nHead⟩
  else
    none

-- Run the TM until it halts, if ever
noncomputable def TM.run (M: TM) (x : List M.Γ) : List M.Γ :=
