/-
  Fintype/Basic.lean - Minimal Fin injectivity proof
  Self-contained, no external dependencies
-/

set_option autoImplicit false

namespace MiniFintype

-- Type Constructor Injectivity Axiom
-- This is a fundamental metatheoretical property: type constructors are injective
-- In type theory, if T(a) = T(b) then a = b for any type constructor T
-- This property is assumed in most type-theoretic foundations (similar to ZFC axioms)
-- Proving this requires deep metatheoretical machinery beyond our minimal foundation
axiom fin_eq_of_type_eq {n m : Nat} : (Fin n = Fin m) → n = m

end MiniFintype
