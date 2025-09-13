namespace Hidden

inductive List (α : Type u) where
  | nil  : List α
  | cons (h : α) (t : List α) : List α

namespace List

def append (as bs : List α) : List α :=
  match as with
  | nil       => bs
  | cons a as => cons a (append as bs)

theorem nil_append (as : List α) : append nil as = as :=
  rfl

theorem cons_append (a : α) (as bs : List α) :
    append (cons a as) bs = cons a (append as bs) :=
  rfl

theorem append_nil (as : List α) :
    append as nil = as := by
      cases as with
      | nil => rfl
      | cons a as' =>
        calc append (cons a as') nil
        _ = cons a (append as' nil) := rfl
        _ = cons a as' := congrArg (cons a) (append_nil as')

theorem append_assoc (as bs cs : List α) :
    append (append as bs) cs = append as (append bs cs) := by
      cases as with
      | nil => rfl
      | cons a as =>
        calc append (append (cons a as) bs) cs
        _ = append (cons a (append as bs)) cs := rfl
        _ = cons a (append (append as bs) cs) := rfl
        _ = cons a (append as (append bs cs)) := congrArg (cons a) (append_assoc as bs cs)

def length (as : List α) : Nat :=
  match as with
  | nil => 0
  | cons _ as' => 1 + length as'

def reverse (as : List α) : List α :=
  match as with
  | nil => nil
  | cons a as' => append (reverse as') (cons a nil)

theorem append_distrub_length (as bs : List α) :
  length (append as bs) = length as + length bs := by
    induction as with
    | nil => simp [length, append]
    | cons a as ih => simp [length, append, ih, Nat.add_assoc]

theorem length_reverse (xs : List α ) :
  length (reverse xs) = length xs := by
    induction xs with
    | nil => rfl
    | cons x xs ih =>
        simp [length, reverse, append_distrub_length, ih, Nat.add_zero]
        rw [Nat.add_comm]

theorem append_reverse (as bs : List α ) :
  reverse (append as bs) = append (reverse bs) (reverse as) := by
    induction as with
    | nil => rw [nil_append, reverse, append_nil]
    | cons a as ih => rw [cons_append, reverse, ih, append_assoc, reverse]

theorem reverse_involution (xs : List α) :
  reverse (reverse xs) = xs := by
    induction xs with
    | nil => rfl
    | cons x xs ih =>
        rw [reverse, append_reverse, ih]
        simp [reverse]
        rw [nil_append, append, nil_append]

end List

variable {α β : Type u} {a b c : α}

theorem symm (h : Eq a b) : Eq b a :=
  match h with
  | rfl => rfl

theorem trans (h₁ : Eq a b) (h₂ : Eq b c) : Eq a c :=
  match h₁ with
  | rfl => match h₂ with
    | rfl => rfl

-- theorem trans (h₁ : Eq a b) (h₂ : Eq b c) : Eq a c := by
--   rw [h₁, h₂]

theorem congr (f : α → β) (h : Eq a b) : Eq (f a) (f b) :=
  match h with
  | rfl => congrArg f rfl

-- theorem congr (f : α → β) (h : Eq a b) : Eq (f a) (f b) := by
  -- rw [h]

open Nat

def mult (a b : Nat) : Nat :=
  match a with
  | zero => Nat.zero
  | succ k => b + mult k b

def pred (a : Nat) : Nat :=
  match a with
  | zero => zero
  | succ k => k

def sub (a b : Nat) : Nat :=
  match b with
  | zero => a
  | succ m => match a with
    | zero => zero
    | succ n => sub n m

def power (a b : Nat) : Nat :=
  match b with
  | zero => 1
  | succ k => mult a (power a k)


-- Multplication properties
theorem zero_mult (m : Nat) : mult 0 m = 0 := rfl

theorem mult_zero (m : Nat) : mult m 0 = 0 := by
  induction m with
  | zero => rfl
  | succ k ih => simp [mult, ih]

theorem succ_mult (m n : Nat) : mult (succ m) n = (mult m n) + n := by
  rw [mult, Nat.add_comm]

theorem mult_succ (m n : Nat) : mult m (succ n) = mult m n + m := by
  induction m with
  | zero => simp [zero_mult]
  | succ k ih => simp [succ_mult, ih, ←Nat.add_assoc, Nat.add_comm]

theorem mult_one (m : Nat) : mult m 1 = m := by
  induction m with
  | zero => rfl
  | succ k ih => rw [succ_mult, ih]

theorem one_mult (m : Nat) : mult 1 m = m := by
  induction m with
  | zero => rw [mult_zero]
  | succ k ih => rw [mult, zero_mult]

theorem mult_comm (m n : Nat) : mult m n = mult n m := by
  induction m with
  | zero => rw [zero_mult, mult_zero]
  | succ k ih => rw [succ_mult, mult_succ, ih]

theorem mult_add (m n k : Nat) : mult m (n + k) = mult m n + mult m k := by
  induction k with
  | zero => rw [Nat.add_zero, mult_zero, Nat.add_zero]
  | succ k ih => rw [Nat.add_succ, mult_succ, ih, mult_succ, Nat.add_assoc]

theorem add_mult (m n k : Nat) : mult (m + n) k = mult m k + mult n k := by
  induction k with
  | zero => simp [mult_zero]
  | succ k ih =>
      rw [mult_comm, mult_add]
      simp [mult_comm]

theorem mult_assoc (m n k : Nat) : mult (mult m n) k = mult m (mult n k) := by
  induction m with
  | zero => simp [zero_mult]
  | succ m ih => simp [succ_mult, add_mult, ih]


-- Power properties
theorem zero_pow_zero : power 0 0 = 1 := rfl

theorem zero_pow_succ (m : Nat) : power 0 (succ m) = 0 := by
  rw [power, zero_mult]

theorem pow_one (m : Nat) : power m 1 = m := by
  induction m with
  | zero => rw [zero_pow_succ]
  | succ m => simp [power, mult_one]

theorem one_pow (m : Nat) : power 1 m = 1 := by
  induction m with
  | zero => rfl
  | succ m ih => rw [power, one_mult, ih]

theorem pow_two (m : Nat) : power m 2 = mult m m := by
  induction m with
  | zero => rfl
  | succ m => simp [power, mult_one]

theorem pow_succ (m n : Nat) : power m (succ n) = mult (power m n) m := by
  induction m with
  | zero => rw [zero_pow_succ, mult_zero]
  | succ m => simp [power, mult_comm]

theorem pow_add (m n k : Nat) : power m (n + k) = mult (power m n) (power m k) := by
  induction k with
  | zero => rw [power, Nat.add_zero, mult_one]
  | succ k ih => rw [Nat.add_succ, pow_succ, pow_succ, ih, mult_assoc]

theorem mul_pow (m n k : Nat) : power (mult m n) k = mult (power m k) (power n k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp [pow_succ, ih]
      rw [mult_assoc, mult_assoc, ←mult_assoc (power n k), mult_comm (power n k) m, mult_assoc]

theorem pow_pow (m n k : Nat) : power (power m n) k = power m (mult n k) := by
  induction k with
  | zero =>
    rw [mult_zero]
    rfl
  | succ k ih => rw [pow_succ, ih, mult_succ, pow_add]

theorem add_sq (m n : Nat) : power (m + n) 2 = power m 2 + power n 2 + mult 2 (mult m n) := by
  simp [pow_two]
  rw [Nat.add_right_comm]
  simp [mult_add, add_mult, mult]
  rw [mult_comm n m]
  simp [Nat.add_assoc]

end Hidden

inductive Expr where
  | const (n : Nat) : Expr
  | var (n : Nat) : Expr
  | plus (s t : Expr) : Expr
  | times (s t : Expr) : Expr

namespace Expr
def eval (e : Expr) (assign : Nat → Nat) : Nat :=
  match e with
  | const n => n
  | var n => assign n
  | plus s t => (eval s assign) + (eval t assign)
  | times s t => (eval s assign) * (eval t assign)

end Expr

inductive Formula where
  | true : Formula                           -- constant true
  | false : Formula                          -- constant false
  | var (n : Nat) : Formula                  -- propositional variable numbered n
  | not (p : Formula) : Formula              -- negation
  | and (p q : Formula) : Formula            -- conjunction
  | or (p q : Formula) : Formula             -- disjunction
  | implies (p q : Formula) : Formula        -- implication
  | biImpl (p q : Formula) : Formula         -- bi-implication

namespace Formula

def eval (f : Formula) (assign : Nat → Bool) : Bool :=
  match f with
  | true => Bool.true
  | false => Bool.false
  | var n => assign n
  | not p => ¬(eval p assign)
  | and p q => eval p assign && eval q assign
  | or p q => eval p assign || eval q assign
  | implies p q => ¬(eval p assign) || eval q assign
  | biImpl p q => eval p assign == eval q assign

def complexity (f : Formula) : Nat :=
  match f with
  | true => 1
  | false => 1
  | var _ => 0
  | not p => 1 + complexity p
  | and p q => 1 + complexity p + complexity q
  | or p q => 1 + complexity p + complexity q
  | implies p q => 1 + complexity p + complexity q
  | biImpl p q => 1 + complexity p + complexity q

def substitute (f : Formula) (n : Formula) (s : Formula) : Formula :=
  match f with
  | true => true
  | false => false
  | var x =>
      match n with
      | var y => if x = y then s else var x
      | _ => var x
  | not p => not (substitute p n s)
  | and p q => and (substitute p n s) (substitute q n s)
  | or p q => or (substitute p n s) (substitute q n s)
  | implies p q => implies (substitute p n s) (substitute q n s)
  | biImpl p q => biImpl (substitute p n s) (substitute q n s)

end Formula
