# Combinatorics Module Guide

This folder contains finite combinatorics infrastructure reused by Wick/Feynman
expansions.

## Files

- `PerfectMatchings.lean`
  - Defines `Pairing r` (perfect matchings on `Fin r`).
  - Provides explicit even-cardinality witnesses (`halfSplitPairing`).
  - Develops partner/incident-pair API and cardinality-parity consequences
    (existence on even sets, emptiness on odd sets).

## Role in the project

- Supplies the pairing backbone for `Phi4/FeynmanGraphs.lean` and Wick
  expansion statements.
- Centralizes finite-set pairing facts so graph and moment files can reuse
  them directly instead of duplicating local ad hoc arguments.

## Frontier note

- These lemmas are intended as reusable mathematical infrastructure (not
  forwarding wrappers). New additions should expose real combinatorial content.
