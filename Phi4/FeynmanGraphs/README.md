# FeynmanGraphs Module Guide

This folder contains localized graph-bound infrastructure for the constructive
expansion stage (Glimm-Jaffe Section 8.5).

## Files

- `LocalizedBounds.lean`
  - Factorial product-vs-sum bounds and weighted occupancy inequalities.
  - Fiberwise/cellwise occupancy controls for localized graph estimates.
  - Degree-weighted and `phi^4`-specialized bridges from graph-integral bounds
    to expansion-level and Gaussian-moment bounds.
  - Constructors producing `FeynmanGraphEstimateModel` witnesses from explicit
    expansion-plus-bound data.

## Role in the project

- Feeds the interaction/frontier pipeline with reusable graph-combinatorial
  estimates needed to control perturbative/localized contributions.
- Implements the theorem-to-theorem groundwork behind localized graph bounds
  rather than opaque interface forwarding.

## Frontier note

- The key mathematical target is the localized graph-bound chain (Theorem 8.5.5
  style): this folder should prioritize constructive bound closure over new API
  abstraction layers.
