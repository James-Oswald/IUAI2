
import Mathlib

structure TuringMachine where
  Q : Type
  Q_fin : Fintype Q
  A : Type
  A_fin : Fintype A
  Γ : Type
  Γ_fin : Fintype Γ
  b : Γ
  δ : Q × Γ -> Q × Γ × Fin 3
  q0 : Q
