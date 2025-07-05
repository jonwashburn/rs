# Recognition Science Foundation – Punch-List / Improvement Plan

> Goal: evolve the cleaned, self-contained foundation (meta-principle → eight foundations → constants) into a *fully proven* mathematics stack with zero `sorry`s, CI, and documentation.

---

## Phase 0  Status Snapshot (HEAD 49f37f5)

| Layer | Builds? | `sorry`s | Notes |
|-------|---------|----------|-------|
| `Core.MetaPrincipleMinimal` | ✅ | 0 | irreducible meta-principle |
| `Core.Finite`               | ✅ | 0 | finite type system |
| `Core.Nat.Card`             | ✅ | 2 | small proofs missing |
| `Core.Arith`                | ⛔ | many | placeholder `Real`, compile errors |
| `Core.EightFoundations`     | ✅* | 11 | all high-level theorems are `sorry` |
| `Foundations.GoldenRatio`   | ✅ | 2 | φ placeholders |
| others                      | ✅ | ★ | compile but rely on `sorry`s |

> *Builds after removing resource-fork files.

---

## Phase 1  Stabilise Core Arithmetic

- [ ] 1.1  Create minimal `Real` *field axiomatization* (field + linear order) instead of `Int` wrapper.
- [ ] 1.2  Fix `Zero`/`One` instance conflicts in `Core.Arith`.
- [ ] 1.3  Provide trivial proofs for `Real.mul_pos`, `Real.div_pos`, `Real.log_pos` (axioms for now).
- [ ] 1.4  Remove compile errors – target: `lake build` completes with only `sorry` warnings.

## Phase 2  Eliminate Low-Hanging `sorry`s

- [ ] 2.1  `Core.Nat.Card` – finish two cardinality lemmas.
- [ ] 2.2  `Core.Arith` – replace `sorry`s in basic positivity lemmas.
- [ ] 2.3  `Core.Constants.one_is_identity` – trivial ring proof.

## Phase 3  Golden Ratio & Constants

- [ ] 3.1  Define φ as positive root of `x²−x−1` within new `Real` field.
- [ ] 3.2  Prove `φ_pos`, `φ_gt_one`, `φ * φ = φ + 1`.
- [ ] 3.3  Replace placeholder `φ : Real := ⟨2⟩` with constructed value.
- [ ] 3.4  Update `FundamentalTick`, `RecognitionLength` to use proven φ.

## Phase 4  Eight Foundations Proof Skeleton

- [ ] 4.1  For each foundation (1‒8) add *outline proofs* (no `sorry`) referencing only previous layers.
- [ ] 4.2  Gradually discharge `sorry`s—start with discrete time ⇒ dual balance (counting argument).
- [ ] 4.3  Lock each foundation theorem with `@[simp]` + minimal doc-strings.

## Phase 5  Continuous Integration & Hygiene

- [ ] 5.1  Add `.gitattributes` & `.gitignore` entries to block `._*`, `.DS_Store`.
- [ ] 5.2  GitHub Action: `lake build`, fail on new `sorry`s (`sorry_checker`).
- [ ] 5.3  `lake fmt` pre-commit hook for consistent style.

## Phase 6  Documentation

- [ ] 6.1  In-file module headers (`/-! ### ... -/`).
- [ ] 6.2  `doc-gen4` static site via GitHub Pages.
- [ ] 6.3  `README` badges: build status, `sorry` count.

## Phase 7  Long-Term (Optional)

- [ ] 7.1  Import a *mathlib-lite* subset for reals/analysis (≤300 LOC).
- [ ] 7.2  Port selected physics derivations back into foundation repo.
- [ ] 7.3  Formal "zero free parameters theorem" connecting all layers.

---

### Immediate Next Action

Focus on **Phase 1**: make `Core.Arith` compile. Once `lake build` is green, CI and further proof work can proceed incrementally. 