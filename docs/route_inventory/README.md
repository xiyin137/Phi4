# Nonempty Route Inventory

This directory tracks deterministic route-bloat inventory for
`theorem .*_nonempty_of_` constructors.

Generate/update:

- `scripts/nonempty_route_inventory.sh --emit docs/route_inventory/nonempty_inventory.tsv`

Input source:

- `docs/frontier_obligations/frontier.tsv`

Output schema (`nonempty_inventory.tsv`):

- `name`: theorem name
- `file`: declaration file
- `line`: declaration line
- `callers`: in-repo caller count (declaration excluded)
- `classification`: deterministic triage label
  - `PLUMBING`: zero-caller constructor matching route-plumbing naming patterns
  - `CONTENTFUL`: retained by default (used route or nontrivial candidate)
