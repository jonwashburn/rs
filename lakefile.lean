/-
  Recognition Science Foundation
  =============================

  Self-contained mathematical foundation with zero external dependencies.
  Built entirely from first principles.

  Author: Jonathan Washburn
  Recognition Science Institute
-/

import Lake
open Lake DSL

package RecognitionScience where
  -- Basic settings for clean compilation
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]
  buildType := BuildType.release

-- No external dependencies - self-contained with local FinCardinality implementation

@[default_target]
lean_lib RecognitionScience where
  -- Include top-level modules
  roots := #[`RecognitionScience, `MinimalFoundation, `Fintype.Basic]
