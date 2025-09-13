instance [Inhabited α] : Inhabited (List α) where
  default := []

instance [Inhabited α] : Inhabited (Sum α β) where
  default := Sum.inl default

example : (fun x : Nat => 0 + x) = (fun x => x) := by
  conv =>
    lhs
    . intro x
      simp

example (g : Nat → Nat → Nat)
        (h₁ : ∀ x, x ≠ 0 → g x x = 1)
        (h₂ : x ≠ 0)
        : g x x + x = 1 + x := by
  conv =>
    lhs
    arg 1
    rw [h₁]
    . skip
    apply h₂
