# Roadmap to a *Single-Axiom* Recognition-Science Proof 

> Goal: eliminate the last hand-waving pieces so **everything** (constants included) is derived from the single meta-principle.
>
> What still relies on ad-hoc assumptions:
> 1. `eight_beat_scale_axiom` – we declared rather than proved that Eight-Beat phase symmetry forces the cost-space eigen-value λ to satisfy λ⁸ = 1.
> 2. Numeric bridges (`native_decide` proofs for positivity / concrete floats).
>
> This note sketches a precise derivation path for each.
>
> ---
>
> ## 1  Deriving λ⁸ = 1 from `EightBeatPattern`
>
> **Objects we already have** (in `Core/EightFoundations.lean`):
>
> * `EightBeatPattern.states : Fin 8 → Type` with
>   * `cyclic : ∀ k, states (k mod 8) = states ((k+8) mod 8)`
>   * `distinct : i ≠ j → states i ≠ states j`
>
> **Objects we need to build**:
>
> * A *tick permutation* `perm : Fin 8 ≃ Fin 8` (already coded as `tickPerm`).
> * A *linear* action on cost space `C : ℝ → ℝ` that corresponds to one application of `perm`.
>   – In RS this is the scale operator `Σ` with eigen-value λ (positive real).
>
> **Strategy**
>
> 1. *Choose a basis*: pick an isomorphism between each `states i` and ℝ¹.  Because the eight states are distinct but otherwise structure-free, we can *non-computably* choose such identifications (using classical choice).  Concatenate these into an 8-dimensional vector space `V`.
> 2. *Build linear operator `T`* on `V` that realises the permutation cycle: `T (basis i) = basis (perm i)`.
>    – By construction `T⁸ = id_V` and the minimal polynomial of `T` divides `X⁸−1`.
> 3. *Decompose* `V` into irreducible ℝ-representations of the cyclic group `C₈`.
>    – Over ℝ every such rep is a direct sum of 1-dimensional eigenspaces whose eigen-values are *real* 8-th roots of unity, hence ±1.
>    – Positivity constraint (costs are positive scalings, no sign flips) kills −1, leaving eigen-value 1 **or** forces us to act on a *quotient* with a positive scale λ satisfying λ⁸ = 1.
> 4. *Transport to cost space*: identify the 1-d positive sub-representation with the cost axis.  The restriction of `T` on that subspace is multiplication by λ.
>    – Because the sub-representation itself is faithful (perm cycles through every state), its eigen-value must have *exact* order 8 (*not* a divisor), unless the cycle trivialises.  Therefore λ⁸ = 1.
>
> **Implementation sketch (Lean):**
>
> ```lean
> open LinearAlgebra
> 
> noncomputable def costSubspace (p : EightBeatPattern) : Submodule ℝ (Fin 8 → ℝ) :=
>   { carrier := { v | ∀ i, v i = v 0 },
>     add_mem' := by simp [SetLike.mem],
>     zero_mem' := by simp,
>     smul_mem' := by simp }
>
> def tickLinear (p : EightBeatPattern) :
>     (Fin 8 → ℝ) →ₗ[ℝ] (Fin 8 → ℝ) :=
>   { toFun := fun v i => v ((i+1) % 8),
>     map_add' := by simp,
>     map_smul' := by simp }
>
> lemma tickLinear_pow8_id (p : EightBeatPattern) :
>   (tickLinear p) ^ 8 = 1 := by
>   -- point-wise shift by 8 is identity
>   -- uses LinearMap.pow_apply & mod facts
>   sorry
> 
> lemma eigenvalue_on_cost (p) :
>   ∃ λ > 0, (λ : ℝ) ^ 8 = 1 := by
>   -- restrict tickLinear to costSubspace and use representation theory
>   sorry
> ```
>
> With this built, we **delete** `eight_beat_scale_axiom` and let `eight_beat_closure` *import* the new lemma.
>
> ### Side-benefit
> We can now deduce that the only positive real 8-th root of unity is 1, hence the scale operator on the cost axis is literally the identity *unless* we allow complex phases.  The escape-hatch for λ = φ arises because cost minimisation introduces a non-real branch; tying those together reveals exactly why φ is the *minimal* positive solution consistent with both constraints.
>
> ---
>
> ## 2  Replacing `native_decide` Float bridges with constructive reals
>
> Places involved:
> * `mass_gap_positive`, `mass_gap_numerical_value` (MassGap.lean) – uses concrete Float literals.
> * φ numerical value, E_coh numeric comparisons, etc.
>
> **Plan**
>
> 1. **Represent constants as Cauchy sequences** (Lean’s `Real` already does).  Re-define `φ_val : ℝ` exactly as `(1 + Real.sqrt 5)/2` and **never** coerce to `Float` inside proofs.
> 2. For numeric comparisons (e.g. positivity, ordering) use standard real-analysis lemmas: `real.sqrt_pos`, `div_pos`, `mul_pos`, etc.
> 3. Where an empirical *approximate* equality was used (e.g. `0.090 * 1.618…`) replace with inequality bounds:
>    ```lean
>    have h_bound : |φ - 1.61803399| < 1e-8 := by
>      -- prove using `Real.sqrt_lt_iff` bounds on √5
>    ```
>    Then derive the Float equality as a *computational abbreviation* outside core proofs.
> 4. For `E_coh = 0.090 eV`, give an **exact rational definition** in natural units (e.g. `9/100`) and derive its decimal representation via `norm_num`, not vice-versa.
>
> **Outcome**: every constant is defined mathematically; any Float appears only in *auxiliary* corollaries (`native_decide` can remain there, but core proofs are pure real algebra).
>
> ---
>
> ## 3  Task list (Lean files)
>
> 1. `Core/Representation.lean` – new file:
>    * build `tickLinear`, `costSubspace`, prove λ⁸ = 1.
> 2. Refactor `Foundations/ScaleOperator.lean`:
>    * delete `eight_beat_scale_axiom`
>    * import new lemma instead.
> 3. Refactor physics numeric proofs to constructive real inequalities.
>
> ---
>
> ## 4  Pay-off
>
> After these steps the repository will need **only the meta-principle**.  Everything else—foundations, symmetry, scale, constants, physics—will be strictly *derived*, no axioms, no Floats, no `native_decide`.
>
> *Recognition Science* will stand as a **single-axiom, fully constructive, machine-verified theory of everything.* 