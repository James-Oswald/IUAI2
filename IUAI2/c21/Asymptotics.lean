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

lemma leplus_nat_codomain {α : Type*} (f g : α → ℕ) :
    f ≤⁺ g ↔ ∃ k : ℕ, ∀ x, f x ≤ g x + k := by
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


class NatOrder (α : Type*) extends LinearOrder α where
  iso : ℕ ≃o α

namespace NatOrder

instance : NatOrder ℕ where
  iso := OrderIso.refl ℕ

instance {α : Type*} [NatOrder α] : Nonempty α :=
  ⟨NatOrder.iso 0⟩

instance {α : Type*} [NatOrder α] : NoMaxOrder α where
  exists_gt x := by
    let iso := NatOrder.iso (α := α)
    refine ⟨iso (iso.symm x + 1), ?_⟩
    have hle : iso (iso.symm x) ≤ iso (iso.symm x + 1) :=
      iso.monotone (Nat.le_succ _)
    have hne : iso (iso.symm x) ≠ iso (iso.symm x + 1) :=
      fun h => by have := iso.injective h; omega
    rw [iso.apply_symm_apply] at hle hne
    exact lt_of_le_of_ne hle hne

end NatOrder

lemma bddAbove_of_eventually_bddAbove {α : Type*} [NatOrder α] {f : α → ℝ}
    (h : ∃ c, ∀ᶠ x in Filter.atTop, f x ≤ c) : ∃ C, ∀ x, f x ≤ C := by
  obtain ⟨c, hc⟩ := h
  have ⟨x₀, hx₀⟩ : ∃ x₀, ∀ x ≥ x₀, f x ≤ c := by
    rw [Filter.eventually_atTop] at hc; exact hc
  let iso := NatOrder.iso (α := α)
  let n₀ := iso.symm x₀
  let S := (Finset.range n₀).image (fun n => f (iso n))
  let M := if h : S.Nonempty then S.max' h else 0
  use max c M
  intro x
  by_cases hx : x₀ ≤ x
  · have hfx : f x ≤ c := hx₀ x hx
    linarith [le_max_left c M]
  · have hlt : iso.symm x < n₀ := by
      have hx : x < x₀ := by push_neg at hx; exact hx
      exact iso.symm.strictMono hx
    have hmem : f x ∈ S := by
      simp only [S, Finset.mem_image, Finset.mem_range]
      exact ⟨iso.symm x, hlt, by simp⟩
    have hSne : S.Nonempty := ⟨_, hmem⟩
    have hfM : f x ≤ M := by
      simp only [M, dif_pos hSne]
      exact S.le_max' _ hmem
    linarith [le_max_right c M]

lemma leplus_iff_isBigO {α : Type*} [NatOrder α] (f g : α → ℝ) :
    leplus f g ↔ (λ x => max (f x - g x) 0) =O[Filter.atTop] λ _ => (1 : ℝ) := by
  constructor
  · intro h
    have : leplus f g := h
    obtain ⟨c, hc⟩ := h
    have : c > 0 ∧ ∀ x, f x ≤ g x + c := hc
    have : ∀ x, |max (f x - g x) 0| ≤ c := by
      grind only [leplus, abs, max_def]
    have : ∀ x, ‖max (f x - g x) 0‖ ≤ c * ‖(1 : ℝ)‖ := by
      simp only [Real.norm_eq_abs, one_mem, CStarRing.norm_of_mem_unitary, mul_one]
      exact this
    have : ∀ᶠ x in Filter.atTop, ‖max (f x - g x) 0‖ ≤ c * ‖(1 : ℝ)‖ := by
      simp_all only [gt_iff_lt, implies_true, and_self, Real.norm_eq_abs, one_mem,
        CStarRing.norm_of_mem_unitary, mul_one, Filter.eventually_atTop, ge_iff_le, exists_const]
    show (λ x => max (f x - g x) 0) =O[Filter.atTop] λ x => 1
    have : (λ x => max (f x - g x) 0) =O[Filter.atTop] λ _ => (1 : ℝ) := by
      rw [Asymptotics.isBigO_iff]; exact ⟨c, this⟩
    exact this
  · intro h
    have : (λ x => max (f x - g x) 0) =O[Filter.atTop] λ x => (1 : ℝ) := h
    have : ∃ c, ∀ᶠ x in Filter.atTop, ‖max (f x - g x) 0‖ ≤ c * ‖(1 : ℝ)‖ := by
      rw [Asymptotics.isBigO_iff] at h; exact h
    obtain ⟨c, hc⟩ := this
    have : ∀ᶠ x in Filter.atTop, max (f x - g x) 0 ≤ c := by
      filter_upwards [hc] with x hx
      have habs : |max (f x - g x) 0| ≤ c := by
        simp only [Real.norm_eq_abs, norm_one, mul_one] at hx; exact hx
      have : 0 ≤ max (f x - g x) 0 := le_max_right _ _
      have : max (f x - g x) 0 ≤ c := by
        rwa [abs_of_nonneg this] at habs
      exact this
    obtain ⟨C, hC⟩ := bddAbove_of_eventually_bddAbove ⟨c, this⟩
    have : ∀ x, f x - g x ≤ C := fun x =>
      le_trans (le_max_left _ _) (hC x)
    show leplus f g
    have : leplus f g := by rw [leplus_iff_diff_bounded_above]; exact ⟨C, this⟩
    exact this


lemma geplus_explicit {α : Type*} (f g : α → ℝ) : f ≥⁺ g ↔ (∃ c > 0, ∀ x, f x + c ≥ g x) := by
  rw [geplus, leplus]

lemma geplus_nat_codomain {α : Type*} (f g : α → ℕ) :
    f ≥⁺ g ↔ ∃ k : ℕ, ∀ x : α, f x + k ≥ g x := by
  rw [geplus, leplus_nat_codomain]

lemma eqplus_explicit {α : Type*} (f g : α → ℝ) :
    f =⁺ g ↔ (∃ c > 0, ∀ x, |f x - g x| ≤ c) := by
  constructor
  · intro h
    have : f =⁺ g := h
    show ∃ c > 0, ∀ x, |f x - g x| ≤ c
    have : f ≤⁺ g := h.left
    obtain ⟨c1, hc1⟩ := this
    have : c1 > 0 ∧ ∀ x, f x ≤ g x + c1 := hc1
    have : g ≤⁺ f := h.right
    obtain ⟨c2, hc2⟩ := this
    have : c2 > 0 ∧ ∀ x, g x ≤ f x + c2 := hc2
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

lemma eqplus_nat_codomain {α : Type*} (f g : α → ℕ) :
    f =⁺ g ↔ ∃ k : ℕ, ∀ x, |(f x : ℤ) - g x| ≤ k := by
  show f ≤⁺ g ∧ g ≤⁺ f ↔ ∃ k : ℕ, ∀ x, |(f x : ℤ) - g x| ≤ k
  constructor
  · intro h
    have : f ≤⁺ g ∧ g ≤⁺ f := h
    show ∃ k : ℕ, ∀ x, |(f x : ℤ) - g x| ≤ k
    have : ∃ k₁ : ℕ, ∀ x, f x ≤ g x + k₁ := (leplus_nat_codomain f g).mp h.left
    obtain ⟨k₁, hk₁⟩ := this
    have hk₁ : ∀ x, f x ≤ g x + k₁ := hk₁
    have : ∃ k₁ : ℕ, ∀ x, g x ≤ f x + k₁ := (leplus_nat_codomain g f).mp h.right
    obtain ⟨k₂, hk₂⟩ := this
    have hk₂ : ∀ x, g x ≤ f x + k₂ := hk₂
    use max k₁ k₂
    grind only [leplus, max_def, abs.eq_1]
  · intro h
    have : ∃ (k : ℕ), ∀ x, |(f x : ℤ) - ↑(g x)| ≤ ↑k := h
    have : ∃ (k : ℕ), k > 0 ∧ ∀ x, |(f x : ℤ) - ↑(g x)| ≤ ↑k := by
      obtain ⟨k, hk⟩ := this
      use k.succ
      grind only
    have : ∃ (c : ℝ), c > 0 ∧ ∀ x, |(f x : ℝ) - ↑(g x)| ≤ ↑c := by
      obtain ⟨k, hkpos, hk⟩ := this
      exact ⟨k, by exact_mod_cast hkpos, fun x => by have := hk x; norm_cast; grind only⟩
    have : f =⁺ g  := by exact (eqplus_explicit (λ x => (f x : ℝ)) (λ x => (g x : ℝ))).mpr this
    exact this

def letimes {α : Type*} [Nonempty α] [PartialOrder α] [NoMaxOrder α] [IsDirectedOrder α] (f g : α → ℝ) :=
  ∃ (c : ℝ) (x₀ : α), ∀ x > x₀, |f x| ≤ c * |g x|

notation:50 f:51 " ≤ˣ " g:51 => letimes (fun x => (f x : ℝ)) (fun x => (g x : ℝ))

lemma letimes_iff_isBigO {α : Type*} [Nonempty α] [PartialOrder α] [NoMaxOrder α] [IsDirectedOrder α]  (f g : α → ℝ) :
    letimes f g ↔ f =O[Filter.atTop] g := by
  constructor
  · intro h
    have : letimes f g := h
    show f =O[Filter.atTop] g
    suffices ∃ c, ∀ᶠ x in Filter.atTop, ‖f x‖ ≤ c * ‖g x‖ by
      rw [Asymptotics.isBigO_iff]; exact this
    obtain ⟨c, x₀, hc⟩ := h
    have hc : ∀ x > x₀, |f x| ≤ c * |g x| := hc
    obtain ⟨x₁, hx₁⟩ := exists_gt x₀
    have hx₁ : x₀ < x₁ := hx₁
    use c
    suffices ∃ x₁, ∀ x ≥ x₁, ‖f x‖ ≤ c * ‖g x‖ by rw [Filter.eventually_atTop]; exact this
    use x₁
    grind only [Real.norm_eq_abs]
  · intro h
    have : f =O[Filter.atTop] g := h
    show letimes f g
    show ∃ c x₀, ∀ x > x₀, |f x| ≤ c * |g x|
    have h : ∃ c, ∀ᶠ (x : α) in Filter.atTop, ‖f x‖ ≤ c * ‖g x‖ := by
      rw [Asymptotics.isBigO_iff] at h; exact h
    obtain ⟨c, hc⟩ := h
    have hc : ∃ x₀, ∀ x ≥ x₀, ‖f x‖ ≤ c * ‖g x‖ := by rw [Filter.eventually_atTop] at hc; exact hc
    obtain ⟨x₀, hx₀⟩ := hc
    use c, x₀
    grind only [Real.norm_eq_abs]
