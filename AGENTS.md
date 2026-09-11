# AGENTS.md

Lean 4 + Mathlib project (elan/lake). Single library `LeanTest`; entrypoint `LeanTest.lean` re-exports `LeanTest/Basic.lean`.

## Toolchain

- Pinned in `lean-toolchain`: `leanprover/lean4:v4.34.0-rc2`. Must match mathlib rev `v4.34.0-rc2` in `lakefile.toml`. Never bump one without the other; prefer the `Update Dependencies` workflow / `lake update`.
- Requires elan + lake. Deps live in `.lake/packages` (gitignored); `lake-manifest.json` is committed.

## Commands

- First build / after dep change: `lake exe cache get` (downloads prebuilt Mathlib oleans; without it a full build takes very long), then `lake build`.
- Normal check: `lake build` (builds `defaultTargets = ["LeanTest"]`).
- Single file: `lake env lean LeanTest/Basic.lean` — use for fast iteration instead of full build.
- CI (`.github/workflows/lean_action_ci.yml`) just runs `leanprover/lean-action` build + docgen; reproduce locally with `lake build`.

## Conventions

- `lakefile.toml` sets `relaxedAutoImplicit = false` — all `variable`s must be declared explicitly.
- `weak.linter.mathlibStandardSet = true` — keep code warning-free under the Mathlib linter set.
- New files under `LeanTest/` must be imported (transitively) from `LeanTest.lean`, otherwise `lake build` won't check them.
- Docstrings use `/-- ... -/`; `@[inherit_doc]` on the `⊑`/`⊏` notations refers to `IsSegment`/`IsPropSegment`.
