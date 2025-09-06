example (p q r : Prop) (hp : p)
        : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  simp [hp]

open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ _ : α, r) → r := by
  simp

example (a : α) : r → (∃ _ : α, r) := by
  intro hr
  exact ⟨a, hr⟩

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := by
  apply Iff.intro
  . intro ⟨x, h⟩
    exact ⟨⟨x, h.left⟩, h.right⟩
  . intro ⟨⟨x, h⟩, r⟩
    exact ⟨x, ⟨h, r⟩⟩

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by
  apply Iff.intro
  . intro ⟨x, h⟩
    cases h with
      | inl hp => exact Or.inl ⟨x, hp⟩
      | inr hq => exact Or.inr ⟨x, hq⟩
  . intro
   | Or.inl ⟨x, hpx⟩ => exact ⟨x, Or.inl hpx⟩
   | Or.inr ⟨x, hqx⟩ => exact ⟨x, Or.inr hqx⟩

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := by
  apply Iff.intro
  . intro hpx ⟨x, hnpx⟩
    exact hnpx (hpx x)
  . intro h
    apply byContradiction
    intro hne
    have hex : ∃ x, ¬ p x := Classical.not_forall.mp hne
    contradiction


example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := by
  apply Iff.intro
  . intro ⟨x, hpx⟩ hall
    exact hall x hpx
  . intro h
    apply byContradiction
    intro hne
    have hall : ∀ x, ¬ p x := fun x hpx => hne ⟨x, hpx⟩
    contradiction

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by
  apply Iff.intro
  . intro h x hpx
    exact h ⟨x, hpx⟩
  . intro ha ⟨x, px⟩
    exact ha x px

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := by
  apply Iff.intro
  . intro h
    rw [←not_forall]
    assumption
  . intro h
    rw [not_forall]
    assumption

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := by
  apply Iff.intro
  . intro ha ⟨x, hp⟩
    exact ha x hp
  . intro h x hp
    exact h ⟨x, hp⟩

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := by
  apply Iff.intro
  . intro ⟨x, h⟩ hpx
    exact h (hpx x)
  . intro h
    by_cases hpx : ∀ x, p x
    · exact ⟨a, fun _ => h hpx⟩
    · have ⟨x, hnp⟩ := not_forall.mp hpx
      exact ⟨x, fun hp => absurd hp hnp⟩

example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := by
  apply Iff.intro
  . intro ⟨x, h⟩ hr
    exact ⟨x, h hr⟩
  . intro h
    by_cases hr : r
    . have ⟨x, px⟩ := h hr
      exact ⟨x, fun r => px⟩
    . exact ⟨a, fun r => absurd r hr⟩


variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := by
  constructor
  · intro h
    exact ⟨fun x => (h x).1, fun x => (h x).2⟩
  · intro ⟨h1, h2⟩ x
    exact ⟨h1 x, h2 x⟩

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := by
  intro hpq hp hx
  exact (hpq hx) (hp hx)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := by
  intro h hx
  cases h with
  | inl hpx => apply Or.inl (hpx hx)
  | inr hqx => apply Or.inr (hqx hx)


variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ _ : α, r) ↔ r) := by
  intro ha
  . apply Iff.intro
    . intro h
      exact h ha
    . intro hr _
      exact hr

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := by
  apply Iff.intro
  . intro h
    by_cases hr : r
    · exact Or.inr hr
    · apply Or.inl
      intro x
      cases h x with
      | inl hp => exact hp
      | inr hr' => contradiction
  . intro h x
    cases h with
    | inl hpx => exact Or.inl (hpx x)
    | inr hr => exact Or.inr hr

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := by
  apply Iff.intro
  . intro h hr hx
    exact (h hx) hr
  . intro h hx hr
    exact (h hr) hx


variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False := by
  by_cases h1 : shaves barber barber
  . have h2 : ¬(shaves barber barber) := (h barber).mp h1
    contradiction
  . have h2 : shaves barber barber := (h barber).mpr h1
    contradiction
