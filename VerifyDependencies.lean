/-
  Dependency Verification Executable
  =================================

  Standalone script to verify the dependency structure of the foundation.
  Can be run from CI or command line.

  Usage: lake env lean --run VerifyDependencies.lean
-/

import Core.DependencyVerification

open RecognitionScience.Core.DependencyVerification

def main : IO Unit := do
  IO.println "=== Recognition Science Foundation Verification ==="
  IO.println ""

  -- Run all verification functions
  ci_verify_dependencies
  IO.println ""
  ci_dependency_report

  IO.println ""
  IO.println "=== ALL VERIFICATIONS COMPLETED SUCCESSFULLY ==="
