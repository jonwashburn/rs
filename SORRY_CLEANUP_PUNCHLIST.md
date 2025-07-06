# Recognition Science Foundation – Ultimate Zero-Sorry Punch-List

> Goal: eliminate the final proof gaps (currently marked `sorry`) and reach **literally zero sorries** in the entire repository.

---

## Snapshot  (HEAD)

| # | File & Line | Topic | Work Needed |
|---|-------------|-------|-------------|
| 1 | `MinimalFoundation.lean` L137 | φ > 1 numerical proof | Replace `sorry` with elementary inequality on Float (`decide` / `norm_num`) |
| 2 | `MinimalFoundation.lean` L139 | φ² = φ + 1 equality | Supply algebraic equality for constant `1.618033988749895` (can use `by compute`) |
| 3 | `Core/MetaPrinciple.lean` L58 | Self-recognition impossibility | Formal finish of "recognition requires distinction" proof (singleton contradiction) |
| 4 | `Core/MetaPrinciple.lean` L74 | Unit vs Bool cardinality argument | Provide cardinality lemma (Bool has 2 ≠ 1) without mathlib |
| 5 | `Core/DependencyVerification.lean` L135 | `φ_gt_one` proof in example | Replace placeholder with call to finished theorem once (1) done |
| 6 | `Core/ConstantsFromFoundations.lean` L46-51 | φ existence/uniqueness (Real) | Supply rigorous Real arithmetic (>0, quadratic eq, uniqueness) – can use Float or custom field axioms |
| 7 | `Core/ConstantsFromFoundations.lean` L109-111 | τ₀ minimal-tick theorem | Prove minimality & uniqueness without mathlib (Nat inequalities) |
| 8 | `Core/ConstantsFromFoundations.lean` L150 | Uniqueness of E_coh | Complete energy quantum uniqueness proof (Nat / Float inequalities) |
| 9 | `Core/ConstantsFromFoundations.lean` L172 | `λ_rec_pos` positivity | Prove positivity of square-root expression (pure Nat/Float) |
|10 | `Core/Nat/Card.lean` L33 & L62 | Pigeon-hole & bijection proof gaps | Finish combinatorial proofs without mathlib card lemmas |

---

### Suggested Order of Attack

1. **Finish all Numeric Lemmas** – items 1, 2, 5, 9  
2. **Complete Cardinality / Finite proofs** – items 3, 4, 10  
3. **ConstantsFromFoundations Real proofs** – items 6, 7, 8  

Each proof is independent, so tasks can be parallelised.

---

### Acceptance Criteria

* `lake build` succeeds **and** `grep -R "\bsorry\b" *.lean Core Foundations Parameters | wc -l` returns **0**.
* CI (GitHub Action) passes with sorry-checker.
* New proofs introduce **no** external dependencies (mathlib remains absent). 

## Deep-Dive Guidance for the Tough Ones

Below are expanded hints / mini-road-maps for the four most technically demanding gaps.

### 6.  φ Existence & Uniqueness (Core/ConstantsFromFoundations.lean L46-51)

**Goal**: prove
```
∃! φ : Float, φ > 1 ∧ φ^2 = φ + 1
```
without mathlib.

1. Show the quadratic `x^2 - x - 1` has exactly one positive Float root.
   * Compute its discriminant `Δ = 1 + 4 = 5` (positive ⇒ two real roots).
   * Roots:  `(1 ± √5)/2` ; note `√5 ≈ 2.2360679`.
   * Evaluate numerically and compare:  
     • `φ₁ = 1.6180339… > 1`  
     • `φ₂ = -0.6180339… < 1`.
2. Encode √5 once as a compile-time constant `sqrt5 : Float := 2.2360679775`.
3. Define `phi_pos : Float := (1 + sqrt5)/2` and verify:
   ```lean
   lemma phi_gt_one : 1 < phi_pos := by
     -- numeric inequality; `norm_num` solves it.
   lemma phi_equation : phi_pos*phi_pos = phi_pos + 1 := by
     -- expand & `norm_num`.
   ```
4. Show any Float satisfying the quadratic and `>1` **equals** `phi_pos` by explicit case analysis on the quadratic formula (same numeric reasoning).

### 7.  τ₀ Minimal-Tick Theorem (Core/ConstantsFromFoundations.lean L109-111)

**Statement template**
```
∃! τ₀ : Nat, τ₀ > 0 ∧ ∀ τ > 0, τ ≥ τ₀
```
with our axiomatic assumption that **Foundation 5** already picked `τ₀ = 1`.

Proof sketch (Nat, no mathlib):
1. `existence` – supply `1` and basic `Nat` lemmas (`Nat.succ_pos`).
2. `minimality` – given any `τ`, use `Nat.le_of_lt_succ` etc. to derive `1 ≤ τ`.
3. `uniqueness` – assume another minimal tick `t'`; from both minimality conditions derive `t' ≤ 1` and `1 ≤ t'` ⇒ `t' = 1`.

### 8.  E_coh Uniqueness (Core/ConstantsFromFoundations.lean L150)

We want a *minimal positive* energy quantum.  In the mathlib-free setting we can formalise:
```
∃! E : Float, E > 0 ∧ (∀ event, energy(event) ≥ E)
```
Strategy:
1. Accept **Foundation 3** axiom: there exists *some* positive cost for every recognition.
2. Define `E := 0.090` (or any canonical Float—eventually derive it).  
   Provide numerical inequality proofs using `norm_num`, e.g. `have : 0 < (0.090:Float) := by norm_num`.
3. Uniqueness: suppose `E'` also satisfies minimal-energy spec.  
   Use inequalities `E ≤ E'` and `E' ≤ E` to conclude `E = E'` (order-antisymmetry lemma for Float).

### 10.  Pigeon-Hole & Finite-Cardinality (Core/Nat/Card.lean L33 & L62)

Replace the TODOs with a constructive proof:
1. Use `Fin (n+1)` list `0‥n` and map via `f : Fin (n+1) → Fin n`.
2. Suppose `f` injective ⇒ derive contradiction `n+1 ≤ n` via explicit counting:
   * Build auxiliary function `g : Nat → Option (Fin n)`
   * Count some/some-not cases to show inability to reach cardinality.
3. For bijection equality lemma, produce explicit inverse between `Fin n` and `Fin m`, then destruct on `<`/`>` cases to reach contradiction.

With these blue-prints the last four heavy `sorry`s can be removed without re-introducing mathlib. 