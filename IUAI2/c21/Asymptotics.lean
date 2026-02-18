import Mathlib

@[grind =]
def leplus {α : Type*} (f g : α → ℝ) : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∀ x : α, f x ≤ g x + c

notation:50 f:51 " ≤⁺ " g:51 => leplus (fun x => (f x : ℝ)) (fun x => (g x : ℝ))

theorem leplus_nat_codomain {α : Type*} (f g : α → ℕ) : f ≤⁺ g ↔ ∃ k : ℕ, ∀ x : α, f x ≤ g x + k := by
  constructor
  · intro h
    have : f ≤⁺ g := h
    show ∃ k, ∀ x : α, f x ≤ g x + k
    have : ∃ c : ℝ, c > 0 ∧ ∀ x : α, ↑(f x) ≤ ↑(g x) + c := by rw [leplus] at h; exact h
    obtain ⟨c, hc⟩ := this
    have hc : c > 0 ∧ ∀ x : α, ↑(f x) ≤ ↑(g x) + c := hc
    use ⌈c⌉₊
    show ∀ x : α, f x ≤ g x + ⌈c⌉₊
    intro x
    show f x ≤ g x + ⌈c⌉₊
    have s1 : f x ≤ g x + c := by grind only
    have : c ≤ ⌈c⌉₊ := by exact Nat.le_ceil c
    have : f x ≤ g x + (⌈c⌉₊ : ℝ) := by linarith

    exact_mod_cast this
  · intro h
    have : ∃ k : ℕ, ∀ x : α, f x ≤ g x + k := h
    show f ≤⁺ g
    suffices ∃ c : ℝ, c > 0 ∧ ∀ x : α, ↑(f x) ≤ ↑(g x) + c by rw [← leplus.eq_def] at this; exact this
    obtain ⟨k, hk⟩ := h
    have : ∀ x : α, f x ≤ g x + k := hk
    let k' := k + 1
    use (k' : ℝ)
    suffices ∀ x : α, ↑(f x) ≤ ↑(g x) + (k' : ℝ) by grind only
    intro x
    suffices f x ≤ g x + k' by exact_mod_cast this
    have s1 : f x ≤ g x + k := this x
    have : k ≤ k' := by grind only
    have : f x ≤ g x + k' := by linarith
    exact this
