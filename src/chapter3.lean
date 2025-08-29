variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun h : p ∧ q => And.intro h.right h.left)
    (fun h : q ∧ p => And.intro h.right h.left)

example : p ∨ q ↔ q ∨ p :=
  Iff.intro
    (fun h : p ∨ q =>
      match h with
      | Or.inl hp => Or.inr hp
      | Or.inr hq => Or.inl hq)
    (fun h : q ∨ p =>
      match h with
      | Or.inl hq => Or.inr hq
      | Or.inr hp => Or.inl hp)

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
    (fun h : (p ∧ q) ∧ r =>
      And.intro h.left.left (And.intro h.left.right h.right))
    (fun h : p ∧ (q ∧ r) =>
      And.intro (And.intro h.left h.right.left) h.right.right)

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  Iff.intro
    (fun h : (p ∨ q) ∨ r =>
      match h with
      | Or.inl hpq =>
        match hpq with
          | Or.inl hp => Or.inl hp
          | Or.inr hq => Or.inr (Or.inl hq)
      | Or.inr hr => Or.inr (Or.inr hr))
    (fun h : p ∨ (q ∨ r) =>
      match h with
      | Or.inl hp => Or.inl (Or.inl hp)
      | Or.inr hqr =>
        match hqr with
        | Or.inl hq => Or.inl (Or.inr hq)
        | Or.inr hr => Or.inr hr)


-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
  (fun h : p ∧ (q ∨ r) =>
    match h.right with
    | Or.inl hq => Or.inl (And.intro h.left hq)
    | Or.inr hr => Or.inr (And.intro h.left hr))
  (fun h : (p ∧ q) ∨ (p ∧ r) =>
    match h with
    | Or.inl hpq => And.intro hpq.left (Or.inl hpq.right)
    | Or.inr hpr => And.intro hpr.left (Or.inr hpr.right))

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  Iff.intro
  (fun h : p ∨ (q ∧ r) =>
    match h with
    | Or.inl hp => And.intro (Or.inl hp) (Or.inl hp)
    | Or.inr hqr => And.intro (Or.inr hqr.left) (Or.inr hqr.right))
  (fun h : (p ∨ q) ∧ (p ∨ r) =>
    match h.left with
    | Or.inl hp => Or.inl hp
    | Or.inr hq => match h.right with
                   | Or.inl hp => Or.inl hp
                   | Or.inr hr => Or.inr (And.intro hq hr))

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) :=
  Iff.intro
    (fun h : p → q → r =>
      fun hpq : p ∧ q => h hpq.left hpq.right)
    (fun h : p ∧ q → r =>
      fun hp : p => fun hq : q => h (And.intro hp hq))

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  Iff.intro
    (fun (h : (p ∨ q) → r) => And.intro (fun hp => h (Or.inl hp)) (fun hq => h (Or.inr hq)))
    (fun h => fun pq => match pq with
                        | Or.inl hp => h.left hp
                        | Or.inr hq => h.right hq)
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  Iff.intro
  (fun h =>
    And.intro
      (fun hp => h (Or.inl hp))
      (fun hq => h (Or.inr hq)))
  (fun h => fun hpq =>
  match hpq with
  | Or.inl hp => h.left hp
  | Or.inr hq => h.right hq)

example : ¬p ∨ ¬q → ¬(p ∧ q) :=
  fun h => fun hpq =>
  match h with
  | Or.inl hnp => hnp hpq.left
  | Or.inr hnq => hnq hpq.right

example : ¬(p ∧ ¬p) := fun h => absurd h.left h.right

example : p ∧ ¬q → ¬(p → q) :=
  fun h hpq => h.right (hpq h.left)

example : ¬p → (p → q) := fun hnp => fun hp : p => False.elim (hnp hp)

example : (¬p ∨ q) → (p → q) :=
  fun h : ¬p ∨ q => fun hp : p =>
    match h with
    | Or.inl hnp => False.elim (hnp hp)
    | Or.inr hq => hq

example : p ∨ False ↔ p :=
  Iff.intro
  (fun h =>
    match h with
    | Or.inl hp => hp
    | Or.inr hf => False.elim hf)
  (fun hp => Or.inl hp)

example : p ∧ False ↔ False :=
  Iff.intro
  (fun h :p ∧ False  => False.elim (h.right))
  (fun hf : False => And.intro (False.elim hf) (hf))

example : (p → q) → (¬q → ¬p) := fun hpq => fun hnq hp => False.elim (hnq (hpq hp))

example : ¬(p ↔ ¬p) :=
  fun h : p ↔ ¬p  =>
    -- h.mp : p → ¬p
    -- h.mpr : ¬p → p
    -- Suppose ¬p is true
    have hp : p := h.mpr (fun hp : p => h.mp hp hp)
    -- Now h.mp hp : ¬p, so h.mp hp hp : False
    h.mp hp hp

-- Problems in classcial logic
open Classical

variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
  fun hpqr =>
    match em q with
    | Or.inl hq => Or.inl (fun _ => hq)
    | Or.inr hnq => Or.inr (fun hp =>
        match hpqr hp with
        | Or.inl hq => absurd hq hnq
        | Or.inr hr => hr)

example : ¬(p ∧ q) → ¬p ∨ ¬q :=
  fun hnpq =>
    match em p with
    | Or.inl hp =>
      match em q with
      | Or.inl hq => False.elim (hnpq (And.intro hp hq))
      | Or.inr hnq => Or.inr hnq
    | Or.inr hnp => Or.inl hnp

example : ¬(p → q) → p ∧ ¬q :=
  fun h =>
    match em p with
    | Or.inl hp =>
      -- p is true
      have hnq : ¬q := fun hq => h (fun _ => hq)
      ⟨hp, hnq⟩
    | Or.inr hnp =>
      -- p is false, so p → q holds vacuously
      have h_pq : p → q := fun hp => absurd hp hnp
      absurd h_pq h

example : (p → q) → (¬p ∨ q) :=
  fun h =>
    match em p with
    | Or.inl hp => Or.inr (h hp)
    | Or.inr hnp => Or.inl hnp

example : (¬q → ¬p) → (p → q) :=
  fun h hp =>
    match em q with
    | Or.inl hq => hq
    | Or.inr hnq => False.elim (h hnq hp)

example : p ∨ ¬p :=
  byContradiction
  (fun h : ¬(p ∨ ¬p) =>
    match em p with
    | Or.inl hp => h (Or.inl hp)
    | Or.inr hnp => h (Or.inr hnp))

example : (((p → q) → p) → p) :=
  fun hpq =>
    match em p with
    | Or.inl hp => hp
    | Or.inr hnp =>
        have hn : ¬((p → q) → p) := fun h_pq_p => hnp (h_pq_p (fun hp => False.elim (hnp hp)))
        absurd hpq hn
