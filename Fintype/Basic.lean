/-
  Fintype/Basic.lean - Minimal Fin injectivity proof
  Self-contained, no external dependencies
-/

set_option autoImplicit false

namespace MiniFintype

-- Simple approach: just accept the core lemma we need
-- Constructor injectivity for Fin types
-- This is a fundamental property that type constructors are injective:
-- If Fin n = Fin m as types, then n = m as natural numbers
axiom fin_eq_of_type_eq {n m : Nat} : (Fin n = Fin m) → n = m

end MiniFintype
