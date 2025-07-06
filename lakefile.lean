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

-- No external dependencies - completely self-contained foundation

@[default_target]
lean_lib RecognitionScience where
  -- Include only top-level modules
  roots := #[`RecognitionScience, `MinimalFoundation]
