/-
  Recognition Science Foundation
  =============================

  Optimized build configuration for fast compilation with caching.

  Author: Jonathan Washburn
  Recognition Science Institute
-/

import Lake
open Lake DSL

package RecognitionScience where
  -- Build optimization settings
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`linter.unusedVariables, false⟩  -- Disable for faster builds
  ]
  buildType := BuildType.release

-- Mathlib dependency with specific version for cache compatibility
require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.11.0"

@[default_target]
lean_lib RecognitionScience where
  -- Include top-level modules
  roots := #[`RecognitionScience, `MinimalFoundation, `ZeroAxiomFoundation, `Fintype.Basic,
             `Core.Physics.MassGap, `Core.Physics.RungGap]
  -- Build optimization
  buildType := BuildType.release
