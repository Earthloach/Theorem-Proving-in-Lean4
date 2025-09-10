noncomputable def myRec
  {motive : Nat → Sort u}
  (n : Nat)
  (F : (n : Nat) → ((k : Nat) → k < n → motive k) → motive n)
  : motive n :=
    WellFounded.fix Nat.lt_wfRel.wf F n

noncomputable def myWfFix
  {α : Type u} {r : α → α → Prop} (hwf : WellFounded r)
  {motive : α → Sort v}
  (F : (x : α) → ((y : α) → r y x → motive y) → motive x)
  (x : α) : motive x :=
    @Acc.rec α r (fun a _ => motive a)
      (fun x _ ih => F x (fun y h => ih y h))
      x
      (hwf.apply x)


inductive Vect (α : Type u) : Nat → Type u
  | nil  : Vect α 0
  | cons : α → {n : Nat} → Vect α n → Vect α (n + 1)

namespace Vect

def appendAux {m : Nat} (v2 : Vect α m) :
  ∀ {n : Nat}, Vect α n → Vect α (n + m)
  | 0,  nil => (Nat.zero_add m).symm ▸ v2
  | n + 1, cons x xs =>
    (Nat.add_right_comm n m 1) ▸ (cons x (appendAux v2 xs))

def append (v1 : Vect α n) (v2 : Vect α m) : Vect α (n + m) :=
  appendAux v2 v1

end Vect


inductive Expr where
  | const : Nat → Expr
  | var : Nat → Expr
  | plus : Expr → Expr → Expr
  | times : Expr → Expr → Expr
deriving Repr

open Expr

def sampleExpr : Expr :=
  plus (times (var 0) (const 7)) (times (const 2) (var 1))

def eval (v : Nat → Nat) : Expr → Nat
  | const n     => n
  | var n       => v n
  | plus e₁ e₂  => (eval v e₁) + (eval v e₂)
  | times e₁ e₂ => (eval v e₁) * (eval v e₂)

def sampleVal : Nat → Nat
  | 0 => 5
  | 1 => 6
  | _ => 0

-- Try it out. You should get 47 here.
#eval eval sampleVal sampleExpr

def simpConst : Expr → Expr
  | plus (const n₁) (const n₂)  => const (n₁ + n₂)
  | times (const n₁) (const n₂) => const (n₁ * n₂)
  | e                           => e

def fuse : Expr → Expr
  | const n => const n
  | var n => var n
  | plus e₁ e₂ => simpConst (plus (fuse e₁) (fuse e₂))
  | times e₁ e₂ => simpConst (times (fuse e₁) (fuse e₂))

theorem simpConst_eq (v : Nat → Nat)
      : ∀ e : Expr, eval v (simpConst e) = eval v e := by
        intro e
        unfold simpConst
        split <;> simp [eval]


theorem fuse_eq (v : Nat → Nat)
        : ∀ e : Expr, eval v (fuse e) = eval v e := by
          intro e
          induction e <;> simp [fuse, simpConst_eq, eval, *]
