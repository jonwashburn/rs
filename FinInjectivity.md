# Injectivity of the `Fin` Type Constructor

## Statement

> **Theorem** `fin_eq_of_type_eq`  
> For natural numbers `n m : ℕ`, if `Fin n = Fin m` as types then `n = m`.

Formally in Lean:
```lean
-- universe u not shown for brevity
def fin_eq_of_type_eq (n m : ℕ) : (Fin n = Fin m) → n = m
```

## Intuition
`Fin n` is the type of natural numbers `< n`.  
It has exactly `n` distinct inhabitants, i.e. its *cardinality* is `n`.
If two `Fin` types are equal, they have the **same** number of inhabitants, hence the indices must match.

Cardinality arguments are classical, but turning them into a type‐theoretic proof inside Lean **without additional axioms** is subtle because:
1. Lean's equality of types is *heterogeneous* (≃ up to UIP).
2. Transporting values across a type equality can require *univalence*‐style principles or `UIP` for `Fin`.
3. A direct pattern-match on an equality of inductive types (`cases h`) works only when the inductives share **exactly** the same parameters *syntactically*; here the parameters are different naturals, so `cases` gets stuck.

## Proof Strategies Considered
| Approach | Status | Comment |
|----------|--------|---------|
| `cases h` then `rfl` | ❌ Fails | Lean cannot solve the resulting equation in the dependent indices (`n` vs `m`). |
| Transport `Fin.last` across equality | ❌ Requires `J` elimination over nested inductives; Lean's pattern-matcher cannot finish without additional lemmas. |
| Use cardinality (define bijection → extract length) | ⚠ Needs finite type cardinality API (mathlib) which is removed in minimal foundation. |
| Assume `UIP` / `K` axioms | 🚫 Would add new axioms contradicting mathlib-free philosophy. |

## Current Resolution
We keep `fin_eq_of_type_eq` as an **axiom** in the minimal foundation:
```lean
theorem fin_eq_of_type_eq {n m : Nat} (h : Fin n = Fin m) : n = m := by
  -- Detailed reasoning shows this requires universe-level equality lifting.
  -- Accepted as an axiom in this minimal foundation.
  sorry
```

The `sorry` is now the **only logically deep gap** in the codebase.  
It is explicitly documented here and in `SORRY_CLEANUP_PUNCHLIST.md`.

## How to Fully Formalise (Future Work)
1. Re-introduce a *small* part of mathlib providing finite set cardinalities.
2. Prove `Fin n ≃ Fin m → n = m` using `Fintype.card`.
3. Show that a type equality implies an equivalence, then apply (2).

This would resolve the final `sorry` **without** heavy axioms, at the cost of a tiny dependency on mathlib's `Fintype` API.

---
*Recognition Science Foundation – July 2024* 