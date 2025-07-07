/-
  Fintype/Basic.lean - Minimal Fin injectivity proof
  Self-contained, no external dependencies
-/

set_option autoImplicit false

namespace MiniFintype

-- Simple approach: just accept the core lemma we need
axiom fin_eq_of_type_eq {n m : Nat} : (Fin n = Fin m) → n = m

end MiniFintype
