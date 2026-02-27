# Codex -> Claude: Focused Upstream Blocker Workpack

Date: 2026-02-27
Repo: `/Users/xiyin/Phi4`

## Primary Goal (Authoritative)

Formalize the Glimm-Jaffe `phi^4_2` continuum pipeline:
1. infinite-volume Schwinger construction,
2. OS axioms,
3. OS -> Wightman reconstruction.

## Non-Negotiable Constraints

- No axioms/placeholders/weakened theorem statements.
- Keep architecture and imports stable unless strictly necessary.
- A simplified definition is a wrong definition.
- Prefer reusable bridge lemmas over one-off term hacks.

## Current Active Blocker

- Queue item: `ComplexLieGroups/Connectedness.lean`
- Declaration: `iterated_eow_permutation_extension`
- Status: `in_progress` (owner `codex`)

### Target Declaration

```
private theorem iterated_eow_permutation_extension ...
```

at approximately line 2173 in:

`/Users/xiyin/Phi4/.lake/packages/OSReconstruction/OSReconstruction/ComplexLieGroups/Connectedness.lean`

## Local Findings (Important)

1. There is already a powerful helper:
   - `permutation_extension_from_invariance` (same file, around line 2029)
   - It constructs the exact `(U_σ, F_σ)` extension package from an invariance
     hypothesis `hperm`.
2. The hard obstruction is obtaining `hperm` for arbitrary `σ` from local swap
   data (`hF_local`) without circular dependence.
3. Current cycle:
   - `eow_chain_adj_swap` uses `iterated_eow_permutation_extension`,
   - `F_permutation_invariance` uses `eow_chain_adj_swap`,
   - so `iterated_eow_permutation_extension` cannot be discharged by invoking
     current `F_permutation_invariance` as-is.
4. Gemini consultation suggested subgroup/generation route and warned the
   unrestricted statement may be false for `d = 1`; this is unverified and must
   not be adopted blindly.

## Requested Work

Provide 2-3 concrete, code-level solution paths for closing
`iterated_eow_permutation_extension`, ranked by feasibility, with explicit
attention to breaking the cycle above.

For the top path, include exact steps:

1. which intermediate lemmas to add (names + statements),
2. where they should be placed in `Connectedness.lean`,
3. how they avoid circular use of `iterated_eow_permutation_extension`,
4. likely type mismatches and term-shape pitfalls (especially around
   permutation composition order and `complexLorentzAction` commutation).

If the current theorem statement is genuinely too strong, provide:

1. a minimal, concrete counterexample strategy,
2. a strictly intermediate corrected lemma that is provable now and useful
   downstream,
3. and a migration strategy that does not introduce placeholders.

## Validation Target

Run and report:

1. `lake build OSReconstruction.ComplexLieGroups.Connectedness`
2. `rg -n "sorry" /Users/xiyin/Phi4/.lake/packages/OSReconstruction/OSReconstruction/ComplexLieGroups/Connectedness.lean`

## Report Format

1. Attempt summary.
2. Added/modified declarations (exact names).
3. Compile results.
4. Remaining blocker (if any) with exact failing goal shape.
