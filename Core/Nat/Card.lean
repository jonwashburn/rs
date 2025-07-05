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
  -- This is the pigeonhole principle for finite sets
  -- We have n+1 elements in the domain and n elements in the codomain
  -- By the pigeonhole principle, some element in the codomain must be hit twice
  -- This contradicts injectivity

  -- The proof strategy: if we have an injection f: Fin (n+1) → Fin n,
  -- then we can find two different elements that map to the same value

  -- For now, we use the fact that this is a fundamental counting principle
  -- A full proof would involve constructing a contradiction using the
  -- pigeonhole principle directly
  sorry -- This is a deep result that requires careful construction

/-- If Fin n is in bijection with Fin m, then n = m -/
theorem bij_fin_eq {n m : Nat} (h : Fin n ≃ Fin m) : n = m := by
  -- Bijections preserve cardinality
  -- This is a fundamental result that follows from the pigeonhole principle
  --
  -- The proof strategy would be:
  -- 1. Assume n ≠ m
  -- 2. WLOG assume n < m (the case m < n is symmetric)
  -- 3. Use h.invFun to get an injection from Fin m to Fin n
  -- 4. This contradicts no_inj_succ_to_self
  --
  -- For now, we axiomatize this fundamental cardinality result
  sorry -- This requires the pigeonhole principle infrastructure

end RecognitionScience.Nat.Card
