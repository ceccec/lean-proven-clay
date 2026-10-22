# lean-proven-clay

A Lean 4 artifact distinguishing **window-shaped** propositions (finite, `decide`-able — the shape of every ℤ/9 theorem in the millennium-solutions deposit) from **Clay-shaped** propositions (infinite-quantifier, not settleable by any finite enumeration).

**Zero sorries.** Every proof is closed by `decide`, induction, or an explicit algebraic construction.

## Prerequisites

- [Lean 4.35.0](https://lean-lang.org/) — install via [elan](https://github.com/leanprover/elan)
- [Mathlib v4.35.0](https://github.com/leanprover/mathlib4)

```bash
# Install elan (Lean version manager)
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh

# Clone and enter the project
git clone https://github.com/ceccec/lean-proven-clay.git
cd lean-proven-clay

# Lean toolchain is pinned via lean-toolchain — elan picks it up automatically
```

## Build & verify

```bash
# Fetch Mathlib cache (speeds up build significantly)
lake exe cache get

# Build the project
lake build

# Verify the artifact compiles with zero sorries
lake env lean ClayShape.lean
```

If `lake env lean ClayShape.lean` exits with no output, the file compiles clean — zero errors, zero warnings, zero sorries.

## Project structure

```
├── ClayShape.lean          # The full zero-sorry artifact
├── lakefile.toml           # Mathlib v4.35.0 pinned
├── lean-toolchain          # leanprover/lean4:v4.35.0
└── .github/workflows/ci.yml # CI: lake env lean ClayShape.lean on push
```

## What's proved

| Theorem | Proof method |
|---|---|
| `window_clay_disjoint` | Construction |
| `tensComplement_true` | `decide` |
| `z9_all_windows` | `decide` |
| `evalPoly_eq_aeval` | `simp` (definitional alignment) |
| `evalPoly_conj` | Induction on polynomial structure |
| `evalPoly_pow` | Induction on k |
| `ZeroLocus_eq_zeroLocus` | `simp` via alignment |
| `zeroLocus_radical_eq` | `Ideal.subset_radical` + `pow_eq_zero_iff` |
| `zeroLocus_conjugation_invariant` | `evalPoly_conj` + `simp` |
| `galois_connection` | `evalPoly_eq_aeval` + Mathlib's Nullstellensatz |
| `radical_zeroLocus_conjugation_invariant` | Chained: radical + conjugation |
| `pEqualsNP_implies_NP_closed_under_complement` | Algebraic construction |
| `trinity_decomposition` | `decide` |
| `orbit_alternates_trinities` | `decide` |
| `regrid_tradeoff` | `decide` |
| `fold_boundary` | `decide` |
| `all_angles_compose` | Composition of proved pieces |

## What's axiomatized (not proved)

| Axiom | Why |
|---|---|
| `PTIME`, `NP` | Full definitions live in `descriptive-complexity` (separate dependency) |
| `P_closed_under_complement` | Standard complexity-theory fact; not re-proved here |

## What's deliberately excluded

| Theorem | Why excluded |
|---|---|
| `baker_gill_solovay` | Requires formalizing oracle TMs, PSPACE, diagonalization — research project |
| `relativization_barrier` | Requires formalizing "relativizing proof technique" — research project |
| `pNotNP_implies_NP_not_closed_under_complement` | Logical error (contrapositive is vacuous) — deleted |

## CI

[![CI](https://github.com/ceccec/lean-proven-clay/actions/workflows/ci.yml/badge.svg)](https://github.com/ceccec/lean-proven-clay/actions/workflows/ci.yml)

CI runs `lake env lean ClayShape.lean` on every push — if it passes, the artifact compiles with zero sorries.

## License

CC BY-NC-ND 4.0
