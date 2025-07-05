/-
  Requires: A1 (Discrete Recognition), A4 (Unitary Evolution)
  Imports Constants: φ, E_coh, τ₀
  Proves/Defines: — FILL IN —
-/

import Lake
open Lake DSL

package RecognitionScience where
  -- Basic settings
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

-- No mathlib dependency - we derive everything from first principles

@[default_target]
lean_lib RecognitionScience where
  -- All modules are part of the RecognitionScience library
  globs := #[.submodules `RecognitionScience]

lean_lib Core where
  -- Core derivations
  globs := #[.submodules `Core]

lean_lib Foundations where
  -- Foundation implementations
  globs := #[.submodules `Foundations]

lean_lib Parameters where
  -- Constants and parameters
  globs := #[.submodules `Parameters]
