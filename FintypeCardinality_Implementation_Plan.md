# Building a Self-Contained Fintype / Cardinality Mini-Library

Goal : eliminate the last `sorry` in `fin_eq_of_type_eq` **without pulling all of mathlib**.
That requires a tiny fragment (≈ 200 LOC) of the `Fintype`/`Finset`/cardinality machinery.
Below is a step-by-step implementation roadmap.

---
## 0  Design Constraints

* **No external deps** – must compile with Lean 4 core only (autoImplicit = false).
* **Keep build time < 5 s** – avoid heavy tactics/metaprogramming.
* **Zero `sorry` at the end** – every lemma fully proven.
* **Names parallel mathlib** so future upgrade → painless.

---
## 1  File Layout

```
Fintype/
  Basic.lean        -- class + helpers (~50 LOC)
  Finset.lean        -- minimal finite-set API (~70 LOC)
  Card.lean          -- cardinality lemmas (~60 LOC)
  FinCard.lean       -- `card_fin` & `fin_eq_of_type_eq` (~20 LOC)
```
We can keep everything in a single file first, then split if desired.

---
## 2  Core API Surface (what we actually need)

| Item | Purpose | Dep. |
|------|---------|------|
| `class Fintype (α)` + `elems : List α` | register finite types | core |
| decidable `mem` on `List` | membership proofs | core |
| `Fintype.card` | length of `elems` | List.length |
| `instance : Fintype (Fin n)` | make `Fin n` finite | core |
| `card_fin` | `Fintype.card (Fin n) = n` | above |
| `Equiv` API (`toFun` / `invFun` / `left_inv` / `right_inv`) | transport | core |
| `Fintype.card_congr` | cardinality preserved by equivalence | List.map bijection |
| `fin_eq_of_type_eq` | **target theorem** | all above |

Anything else can be omitted.

---
## 3  Implementation Steps

### Step 3.1  Minimal List helpers (≈ 20 LOC)
* `List.Nodup` for uniqueness (can be light – we only need length)
* `List.eraseDup` if necessary (maybe skip)

### Step 3.2  Define `Fintype`
```lean
class Fintype (α : Type) where
  elems : List α
  complete : ∀ a : α, a ∈ elems
  nodup    : elems.Nodup    -- no duplicates
```
*Implement `Fintype.card` as `elems.length`.*

### Step 3.3  `Fin` is a `Fintype`
```lean
instance (n) : Fintype (Fin n) where
  elems := List.finRange n            -- `[0, …, n-1]`
  complete := by intro ⟨i, h⟩; simp[List.mem_finRange] at *
  nodup := List.nodup_finRange _
```
Prove `card_fin` by unfolding.

### Step 3.4  Equivalence preserves cardinality
```lean
lemma Fintype.card_congr {α β} [Fintype α] [Fintype β]
  (e : α ≃ β) : Fintype.card α = Fintype.card β := by
  -- map elems through `e`; use length‐map and bijection
```
Need auxiliary lemmas:
* `List.length_map`
* injectivity → length equality.

### Step 3.5  Fin injectivity (`fin_eq_of_type_eq`)
Put pieces together exactly like mathlib.

---
## 4  Estimated LOC Breakdown

| Block | LOC |
|-------|-----|
| List helpers          | 20 |
| `Fintype` definition  | 30 |
| `Fintype` instances   | 30 |
| `card_fin` proof      | 10 |
| Helper lemmas         | 70 |
| `card_congr` proof    | 20 |
| `fin_eq_of_type_eq`   | 20 |
| **Total**             | ~200 |

---
## 5  Testing Plan

1. Add new target `MiniFintype` to `lakefile`.  
2. `#eval (by have : (Fin 3 = Fin 5) → False := by
      intro h; have : (3:Nat) = 5 := fin_eq_of_type_eq h
      decide
    exact ())`
3. Ensure entire repo has **0 sorries**.

---
## 6  Next Actions

1. [ ] Create `Fintype/Basic.lean` with class & helpers.  
2. [ ] Implement `Fintype.card` & `card_fin`.  
3. [ ] Implement `card_congr` proof.  
4. [ ] Wire into `MinimalFoundation.lean` and delete the sorry.  
5. [ ] Run `lake build` → expect clean build, zero sorries.

---
## 7  Time Estimate

*Coding*: ~2 hrs  •  *Review / polish*: 30 min  •  *Total*: < 3 hrs

---

*Prepared : Recognition Science Foundation – July 2024* 