open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ _ : α, r) → r :=
  fun ⟨_, hx⟩ => hx

example (a : α) : r → (∃ _ : α, r) :=
  fun h : r => ⟨a, h⟩
example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
  Iff.intro
    (fun ⟨x, hx⟩ => And.intro (⟨x, hx.left⟩) (hx.right))
    (fun ⟨⟨x, px⟩, r⟩ => ⟨x, ⟨px, r⟩⟩)

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  Iff.intro
    (fun ⟨a, (h1 : p a ∨ q a)⟩ =>
      Or.elim h1
        (fun hpa : p a => Or.inl ⟨a, hpa⟩)
        (fun hqa : q a => Or.inr ⟨a, hqa⟩))
    (fun h : (∃ x, p x) ∨ (∃ x, q x) =>
      Or.elim h
        (fun ⟨a, hpa⟩ => ⟨a, (Or.inl hpa)⟩)
        (fun ⟨a, hqa⟩ => ⟨a, (Or.inr hqa)⟩))

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
  Iff.intro
    (fun h1 : ∀ x, p x =>
      fun h2 : ∃ x, ¬ p x =>
        h2.elim (fun x h3 => h3 (h1 x)))
    (fun h1 : ¬ (∃ x, ¬ p x) =>
      fun x => byContradiction
        (fun h2 : ¬ p x =>
          h1 ⟨x, h2⟩))

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
  Iff.intro
    (fun ⟨x, px⟩ => fun h1 => show False from h1 x px)
    (fun h1 : ¬ (∀ x, ¬ p x) =>
      byContradiction
        (fun h2 : ¬ (∃ x, p x) =>
          have h3 : ∀ x, ¬ p x := fun x =>
            fun h4 : p x => h2 ⟨x, h4⟩
          show False from h1 h3))

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
  Iff.intro
    (fun h1 : ¬ ∃ x, p x =>
      fun x => fun h2 : p x => h1 ⟨x, h2⟩)
    (fun h1 : ∀ x, ¬ p x =>
      fun ⟨x, px⟩ => show False from h1 x px)

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
  Iff.intro
    (fun h1 : ¬ ∀ x, p x =>
      byContradiction
        (fun h2 : ¬ ∃ x, ¬ p x =>
          have h3 : ∀ x, p x := fun x =>
            byContradiction
              (fun h4 : ¬ p x => h2 ⟨x, h4⟩)
          show False from h1 h3))
    (fun ⟨x, h3⟩ => fun h2 => show False from h3 (h2 x))

example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
  Iff.intro
  (fun h1 : (∀ x, p x → r) => fun ⟨x, px⟩ => h1 x px)
  (fun h1 : (∃ x, p x) → r => fun x px => h1 ⟨x, px⟩)

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
  Iff.intro
    (fun ⟨x, h1⟩ h2 => h1 (h2 x))
    (fun h1 =>
      byCases
        (fun h2 : ∀ x, p x => ⟨a, fun _ => h1 h2⟩)
        (fun h2 : ¬ ∀ x, p x =>
          have ⟨x, h3⟩ : ∃ x, ¬ p x := not_forall.mp h2
          ⟨x, fun h4 => False.elim (h3 h4)⟩))


example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
  Iff.intro
    (fun ⟨x, h1⟩ hr => ⟨x, h1 hr⟩)
    (fun h1 =>
      byCases
        (fun hr : r =>
          let ⟨x, hpx⟩ := h1 hr
          ⟨x, fun _ => hpx⟩)
        (fun hnr : ¬r => ⟨a, fun hr => False.elim (hnr hr)⟩))


variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  Iff.intro
    (fun h1 : ∀ x, p x ∧ q x => And.intro (fun x => (h1 x).left) (fun x => (h1 x).right))
    (fun h1 => fun x => And.intro (h1.left x) (h1.right x))

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  fun h1 h2 hx => h1 hx (h2 hx)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  fun h1 => match h1 with
    | Or.inl hpx => fun hx => Or.inl (hpx hx)
    | Or.inr hqx => fun hx => Or.inr (hqx hx)


variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ _ : α, r) ↔ r) :=
  fun ha =>
    Iff.intro
      (fun h1 => h1 ha)
      (fun hr => fun _ => hr)

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
  Iff.intro
    (fun h1 : (∀ x, p x ∨ r) =>
      if hr : r then Or.inr hr
      else Or.inl (fun x =>
        match h1 x with
        | Or.inl px => px
        | Or.inr r' => False.elim (hr r')))
    (fun h2 =>
      match h2 with
      | Or.inl hpx => fun x => Or.inl (hpx x)
      | Or.inr hr => fun _ => Or.inr hr)

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
  Iff.intro
    (fun h1 => fun hr => fun hx => h1 hx hr)
    (fun h1 => fun hx => fun hr => h1 hr hx)



variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
  byCases
    (fun h1 : shaves barber barber =>
      have h2 : ¬(shaves barber barber) := (h barber).mp h1
      h2 h1)
    (fun h1 : ¬(shaves barber barber) =>
      have h2 : shaves barber barber := (h barber).mpr h1
      h1 h2)


def even (n : Nat) : Prop := ∃ b, n = 2 * b

def prime (n : Nat) : Prop := n > 1 ∧ ∀ m, m ∣ n → m = 1 ∨ m = n

def infinitely_many_primes : Prop := ∀ b, ∃ c, prime c ∧ c > b

def Fermat_prime (n : Nat) : Prop := ∃ b, n = 2 ^ (2 ^ b) + 1

def infinitely_many_Fermat_primes : Prop := ∀ b, ∃ c, Fermat_prime c ∧ c > b

def goldbach_conjecture : Prop := ∀ n, ∃ a, ∃ b, prime a ∧ prime b ∧ n = a+b

def Goldbach_weak_conjecture : Prop := ∀ n, ∃ a, ∃ b, ∃ c, prime a ∧ prime b ∧ prime c ∧ n = a+b+c

def Fermat_last_theorem : Prop := ∀ n, ¬(∃ a, ∃ b, ∃ c, a > 0 ∧ b > 0 ∧ c > 0 ∧ n > 2 ∧ a^n + b^n = c^n)
