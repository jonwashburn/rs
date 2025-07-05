/-
  Recognition Science Foundation Ledger
  =====================================
  Self-contained package: meta-principle → eight foundations → constants
  No external dependencies.
-/

import Lake
open Lake DSL

package RecognitionLedger where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]
  -- Enable caching for faster builds
  buildType := BuildType.release

@[default_target]
lean_lib Core where
  globs := #[.submodules `Core]

lean_lib Foundations where
  globs := #[.submodules `Foundations]

lean_lib Parameters where
  globs := #[.submodules `Parameters]
