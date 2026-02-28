## External Consultation Policy (Gemini CLI)

When blocked, use local Gemini CLI by default.

1. Trigger
- If stuck after 2 distinct failed proof/code attempts in test/scratch files, or clearly stalled on one subgoal, consult Gemini.

2. Safety
- Never send secrets, tokens, private keys, or unrelated proprietary text.
- Share only minimal context needed to solve the blocker.

3. Method
- Use non-interactive mode:
  - `gemini -p "<prompt>"`
- Ask for concrete, checkable steps (not high-level commentary).

4. Verification
- Treat Gemini output as untrusted until independently verified by local compile/tests.
- Do not copy blindly into working files.
- Always test in test/scratch files first, then port to working files only after compile success.

5. Reporting
- Briefly record:
  - what was asked,
  - what suggestion was adopted/rejected,
  - what local checks passed/failed.
Use this exact Gemini consultation prompt template:

You are assisting with a focused coding/proof blocker.

Task:
- Primary goal: <GOAL>
- Current blocker: <BLOCKER>

Repository context:
- Language/toolchain: <LANG/TOOLCHAIN>
- File(s): <FILE_PATHS>
- Target declaration: <DECL_NAME + FULL STATEMENT>

Current local context:
- Relevant hypotheses/locals:
<PASTE MINIMAL CONTEXT>

What already failed:
1) <ATTEMPT_1 + error/result>
2) <ATTEMPT_2 + error/result>

Constraints:
- No axioms/placeholders/weakened theorem statements.
- Keep existing architecture and imports unless necessary.
- Prefer reusable infrastructure lemmas over brittle one-off hacks.

Request:
1) Propose 2–3 concrete solution paths, ranked by feasibility.
2) For the top path, give exact code-level steps.
3) Point out likely type mismatches or missing bridge lemmas.
4) If statement looks false/underdetermined, provide a minimal counterexample strategy or corrected intermediate lemma.
5) Keep output actionable and concise.

## Theorem Clarity Policy

- Avoid wrappers by default. Prefer direct, mathematically meaningful theorem
  statements over interface-forwarding aliases.
- Simplification lemmas are encouraged when they:
  1) remove repeated proof blocks,
  2) control recursive-definition unfolding, or
  3) provide reusable technical bridges with nontrivial proof content.
- If a wrapper is temporarily necessary for compatibility, it must:
  1) delegate to an assumption-explicit core theorem,
  2) be clearly marked as a compatibility shim, and
  3) be scheduled for removal once downstream callers migrate.
- Wrapper-for-wrapper layering is disallowed.

## No Assumption Smuggling Policy

- Do not hide substantive hypotheses behind typeclass inference or broad
  bundles when the theorem can state them explicitly.
- Every frontier theorem should expose the real mathematical inputs needed for
  the result (for example: measurability, convergence, bounds), not only a
  convenient model-class façade.
- Refactors that increase abstraction are acceptable only when they reduce, not
  increase, hidden assumptions.
- “No wrapper” and “no assumption smuggling” take precedence over local API
  convenience.

## Definition Fidelity Policy

- A simplified definition is a wrong definition.
- Do not replace mathematically correct target definitions with easier surrogates.
- If a weaker notion is needed for staging, introduce it as an explicitly named
  intermediate/interface artifact, never as the canonical definition.
