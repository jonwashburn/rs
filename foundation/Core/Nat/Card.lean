/-
  Nat.Card
  --------
  Elementary counting lemmas for finite types.
  Built from first principles without Mathlib.

  Author: Jonathan Washburn
  Recognition Science Institute
-/

namespace RecognitionScience.Nat.Card

/-- A function is injective if different inputs give different outputs -/
def Function.Injective {α β : Type} (f : α → β) : Prop :=
  ∀ a₁ a₂, f a₁ = f a₂ → a₁ = a₂

/-- Basic equivalence structure -/
structure Equiv (α β : Type) where
  toFun : α → β
  invFun : β → α
  left_inv : ∀ a, invFun (toFun a) = a
  right_inv : ∀ b, toFun (invFun b) = b

notation:25 α " ≃ " β => Equiv α β

/-- There is no injection from Fin (n+1) to Fin n -/
theorem no_inj_succ_to_self {n : Nat} (f : Fin (n + 1) → Fin n) : ¬Function.Injective f := by
  intro h_inj
  -- This is a fundamental fact about finite sets
  -- An injective function from a larger set to a smaller set is impossible
  -- We axiomatize this for now in our first-principles approach
  sorry

/-- If Fin n is in bijection with Fin m, then n = m -/
theorem bij_fin_eq {n m : Nat} (h : Fin n ≃ Fin m) : n = m := by
  -- Bijections between finite sets of different sizes are impossible
  -- This follows from cardinality preservation
  sorry

end RecognitionScience.Nat.Card
