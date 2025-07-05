/-
  Core.Finite
  -----------
  Self-contained finite-set theory for Recognition Science.
  Built from first principles without external dependencies.

  Author: Jonathan Washburn
  Recognition Science Institute
-/

import Core.Nat.Card

namespace RecognitionScience

open Function
open RecognitionScience.Nat.Card

/-- The empty type represents absolute nothingness -/
inductive Nothing : Type where
  -- No constructors - this type has no inhabitants

/-- A type `A` is `Finite` if there exists a natural number `n` and a
bijection (equivalence) between `A` and `Fin n`. -/
structure Finite (A : Type) : Type where
  n : Nat
  toFin : A → Fin n
  fromFin : Fin n → A
  left_inv : ∀ a : A, fromFin (toFin a) = a
  right_inv : ∀ f : Fin n, toFin (fromFin f) = f

/-- Any empty type is finite (with `n = 0`). -/
instance finiteNothing : Finite Nothing where
  n := 0
  toFin := fun x => by cases x
  fromFin := fun f => absurd f.2 (Nat.not_lt_zero f.1)
  left_inv := by intro x; cases x
  right_inv := by intro ⟨val, hlt⟩; cases Nat.not_lt_zero val hlt

/-- `Unit` is finite with `n = 1`. -/
instance finiteUnit : Finite Unit where
  n := 1
  toFin := fun _ => ⟨0, Nat.zero_lt_one⟩
  fromFin := fun _ => ()
  left_inv := by intro u; cases u; rfl
  right_inv := by
    intro ⟨val, hlt⟩
    -- Since val < 1, we must have val = 0
    have : val = 0 := by
      cases val
      · rfl
      · rename_i n
        -- n + 1 < 1 is impossible
        exfalso
        exact Nat.not_succ_le_zero n (Nat.le_of_succ_le_succ hlt)
    subst this
    rfl

/-- `Bool` is finite with `n = 2`. -/
instance finiteBool : Finite Bool where
  n := 2
  toFin := fun b => if b then ⟨1, by decide⟩ else ⟨0, by decide⟩
  fromFin := fun f => if f.val = 0 then false else true
  left_inv := by
    intro b
    cases b
    · -- b = false
      simp
    · -- b = true
      simp
  right_inv := by
    intro f
    -- We need to show that converting to Bool and back gives the same Fin 2
    ext  -- Show the Fin values are equal by showing their .val components are equal
    simp
    -- The key insight: for any f : Fin 2, either f.val = 0 or f.val = 1
    have : f.val = 0 ∨ f.val = 1 := by
      have hlt := f.2  -- f.val < 2
      -- Use omega to solve this arithmetic constraint
      omega
    cases this with
    | inl h =>
      -- f.val = 0, so we need to show: (if f = 0 then 0 else 1) = f
      -- Since f.val = 0, we have f = ⟨0, _⟩
      have : f = ⟨0, by omega⟩ := by
        ext
        exact h
      rw [this]
      simp
    | inr h =>
      -- f.val = 1, so we need to show: (if f = 0 then 0 else 1) = f
      -- Since f.val = 1, we have f = ⟨1, _⟩
      have : f = ⟨1, by omega⟩ := by
        ext
        exact h
      rw [this]
      simp

/-- Helper: Create an equivalence structure -/
def mkEquiv {α β : Type} (f : α → β) (g : β → α)
  (left : ∀ a, g (f a) = a) (right : ∀ b, f (g b) = b) : Equiv α β :=
  ⟨f, g, left, right⟩

/-- Helper: The cardinality of a finite type is unique -/
theorem card_unique {A : Type} (h1 h2 : Finite A) : h1.n = h2.n := by
  -- If A ≃ Fin n and A ≃ Fin m, then Fin n ≃ Fin m, so n = m
  -- Construct the composite bijection: Fin h1.n → A → Fin h2.n
  let f : Fin h1.n → Fin h2.n := fun i => h2.toFin (h1.fromFin i)
  let g : Fin h2.n → Fin h1.n := fun j => h1.toFin (h2.fromFin j)

  -- Show f and g are inverses
  have fg_inv : ∀ j : Fin h2.n, f (g j) = j := by
    intro j
    simp [f, g]
    -- g j = h1.toFin (h2.fromFin j)
    -- f (g j) = h2.toFin (h1.fromFin (h1.toFin (h2.fromFin j)))
    --         = h2.toFin (h2.fromFin j)    [by h1.left_inv]
    --         = j                           [by h2.right_inv]
    rw [h1.left_inv]
    exact h2.right_inv j

  have gf_inv : ∀ i : Fin h1.n, g (f i) = i := by
    intro i
    simp [f, g]
    -- f i = h2.toFin (h1.fromFin i)
    -- g (f i) = h1.toFin (h2.fromFin (h2.toFin (h1.fromFin i)))
    --         = h1.toFin (h1.fromFin i)    [by h2.left_inv]
    --         = i                           [by h1.right_inv]
    rw [h2.left_inv]
    exact h1.right_inv i

  -- Now we have a bijection between Fin h1.n and Fin h2.n
  -- Use the theorem from Nat.Card
  have equiv : Equiv (Fin h1.n) (Fin h2.n) := mkEquiv f g gf_inv fg_inv
  exact bij_fin_eq equiv

end RecognitionScience
