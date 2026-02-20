import Mathlib

@[grind =]
def leplus {α : Type*} (f g : α → ℝ) : Prop :=
  ∃ c > 0, ∀ x : α, f x ≤ g x + c

notation:50 f:51 " ≤⁺ " g:51 => leplus (fun x => (f x : ℝ)) (fun x => (g x : ℝ))

@[grind =, aesop safe]
def geplus {α : Type*} (f g : α → ℝ) : Prop :=
  g ≤⁺ f

notation:50 f:51 " ≥⁺ " g:51 => geplus (fun x => (f x : ℝ)) (fun x => (g x : ℝ))

@[grind =, aesop safe]
def eqplus {α : Type*} (f g : α → ℝ) : Prop :=
  f ≤⁺ g ∧ g ≤⁺ f

notation:50 f:51 " =⁺ " g:51 => eqplus (fun x => (f x : ℝ)) (fun x => (g x : ℝ))

lemma geplus_explicit {α : Type*} (f g : α → ℝ) : f ≥⁺ g ↔ (∃ c > 0, ∀ x : α, f x + c ≥ g x) := by
  rw [geplus, leplus]

lemma leplus_iff_diff_bounded_above {α : Type*} (f g : α → ℝ) :
    f ≤⁺ g ↔ ∃ c : ℝ, ∀ x : α, f x - g x ≤ c := by
  constructor
  · intro h
    have : f ≤⁺ g := h
    show ∃ c : ℝ, ∀ x : α, f x - g x ≤ c
    obtain ⟨c, hc⟩ := this
    use c
    grind only
  · intro h
    show f ≤⁺ g
    show ∃ c : ℝ, c > 0 ∧ ∀ x : α, f x ≤ g x + c
    obtain ⟨c, hc⟩ := h
    use max c 0 + 1
    grind only [max_def]

lemma eqplus_explicit {α : Type*} (f g : α → ℝ) :
    f =⁺ g ↔ (∃ c > 0, ∀ x : α, |f x - g x| ≤ c) := by
  constructor
  · intro h
    have : f =⁺ g := h
    show ∃ c > 0, ∀ x, |f x - g x| ≤ c
    have : f ≤⁺ g := h.left
    obtain ⟨c1, hc1⟩ := this
    have s1 : c1 > 0 ∧ ∀ x, f x ≤ g x + c1 := hc1
    have : g ≤⁺ f := h.right
    obtain ⟨c2, hc2⟩ := this
    have s2 : c2 > 0 ∧ ∀ x, g x ≤ f x + c2 := hc2
    let c := max c1 c2
    use c
    grind only [max_def, abs.eq_1]
  · intro h
    obtain ⟨c, hc⟩ := h
    have : c > 0 ∧ ∀ x, |f x - g x| ≤ c := hc
    show f =⁺ g
    show f ≤⁺ g ∧ g ≤⁺ f
    constructor
    · show f ≤⁺ g
      show ∃ c > 0, ∀ x, f x ≤ g x + c
      use c
      grind only [abs.eq_1, max_def]
    · show g ≤⁺ f
      show ∃ c > 0, ∀ x, g x ≤ f x + c
      use c
      grind only [abs.eq_1, max_def]

lemma leplus_nat_codomain {α : Type*} (f g : α → ℕ) :
    f ≤⁺ g ↔ ∃ k : ℕ, ∀ x : α, f x ≤ g x + k := by
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
    suffices ∃ c : ℝ, c > 0 ∧ ∀ x : α, ↑(f x) ≤ ↑(g x) + c by
      rw [← leplus.eq_def] at this; exact this
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

lemma geplus_nat_codomain {α : Type*} (f g : α → ℕ) :
    f ≥⁺ g ↔ ∃ k : ℕ, ∀ x : α, f x + k ≥ g x := by
  rw [geplus, leplus_nat_codomain]

def letimes {α : Type*} [LinearOrder α] [Nonempty α] [NoMaxOrder α] (f g : α → ℝ) :=
  ∃ (c : ℝ) (x₀ : α), ∀ x > x₀, |f x| ≤ c * |g x|

notation:50 f:51 " ≤ˣ " g:51 => letimes (fun x => (f x : ℝ)) (fun x => (g x : ℝ))

lemma letimes_iff_isBigO {α : Type*} [LinearOrder α] [Nonempty α] [NoMaxOrder α] (f g : α → ℝ) :
    letimes f g ↔ f =O[Filter.atTop] g := by
  constructor
  · intro h
    have : letimes f g := h
    show f =O[Filter.atTop] g
    obtain ⟨c, x₀, hc⟩ := this
    have hc : ∀ x > x₀, |f x| ≤ c * |g x| := hc
    obtain ⟨x₁, hx₁⟩ := exists_gt x₀
    have hx₁ : x₀ < x₁ := hx₁
    rw [Asymptotics.isBigO_iff]
    use c
    rw [Filter.eventually_atTop]
    use x₁
    intro x hx
    have hx' : x > x₀ := lt_of_lt_of_le hx₁ hx
    have := hc x hx'
    rwa [Real.norm_eq_abs, Real.norm_eq_abs]
  · intro h
    show letimes f g
    show ∃ c : ℝ, ∃ x₀ : α, ∀ x > x₀, |f x| ≤ c * |g x|
    rw [Asymptotics.isBigO_iff] at h
    obtain ⟨c, hc⟩ := h
    rw [Filter.eventually_atTop] at hc
    obtain ⟨x₀, hx₀⟩ := hc
    use c, x₀
    intro x hx
    have := hx₀ x hx.le
    rwa [Real.norm_eq_abs, Real.norm_eq_abs] at this
