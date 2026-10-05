---
name: lean4-mathlib
description: Use when writing, editing, or debugging Lean 4 / Mathlib (.lean) files in this repo or any elan+lake project - covers build commands, Mathlib linter requirements, namespace gotchas, and Mathlib API differences in Lean v4.34.0-rc2.
---

# Lean 4 + Mathlib (v4.34.0-rc2)

Verified against `leanprover/lean4:v4.34.0-rc2` + mathlib `v4.34.0-rc2`.

## Build / verify

- Iterate on a single file with `lake env lean <path>.lean` — much faster than `lake build`.
- Full check: `lake build`.
- Before the first build or after a dep change: `lake exe cache get`, otherwise Mathlib
  compiles from source and takes a very long time.
- New files under the library dir are only type-checked if reachable from the library root
  (`LeanTest.lean` here). An unwired file silently never gets built.

## Mathlib linter requirements

`lakefile.toml` sets `weak.linter.mathlibStandardSet = true`, so these are enforced as
warnings on every build. Fix them in code; do **not** silence them with `set_option`.

- **File must end with a trailing newline.** A missing final `\n` is a linter error.
  After writing a file, confirm with `tail -c 1 <file> | od -An -c`.
- Copyright header, exactly this shape:
  ```lean
  /-
  Copyright (c) 2026 <Author>. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: <Author>
  -/
  ```
  The authors line must start with `Authors: `, contain at least one name, have no double
  spaces, no ` and ` (use `,`), and no trailing period.
- A module docstring `/-! ... -/` must be the **first command after the imports**
  (before `variable`, `open`, `section`, or any declaration).
- Use `<|` instead of `$` for piping.
- No missing spaces around binders/punctuation (`∀ x`, `(c : ↑(g C)) : c ≤ f`).

## Lean 4 gotchas that cost time

- **Mathlib namespaces are not where you expect.** Before assuming a name, grep the source:
  ```
  grep -rn "theorem <name>" .lake/packages/mathlib/Mathlib/
  ```
  Examples: `even_iff_exists_two_mul` is in the **root** namespace, but `Nat.even_or_odd`,
  `Nat.not_odd_iff_even`, `Nat.odd_pow_iff` are under `Nat`.
- **`Nat.mul_left_cancel` requires `0 < n`** (it is the *ordered* cancellation lemma). For
  plain cancellation either let `simp` do it (`simpa using h`) or use `mul_left_cancel₀`.
- **Structure field defaults are not constructor arguments.** In `structure Foo where
  den : Nat := 1`, the default is metadata for the structure-*instance* elaborator
  (`{ .. }` / `⟨..⟩` notation, `where`-constructors). `Foo.mk` still demands every field.
  Proof fields with `by decide` defaults cannot be skipped positionally at all.
- **Core `mk*` functions can be outside the type's namespace.** `Rat.mkRat` in
  `Init/Data/Rat/Basic.lean` is declared before `namespace Rat`, so it is `Lean.mkRat`.
- That file is `prelude`, so its contents are available with no import at all.
- `Nat.pow_eq_zero : a ^ n = 0 ↔ a = 0 ∧ n ≠ 0` is the ℕ way to get `a ^ n = 0 → a = 0`.

## Module existence

Import paths change between Mathlib versions; a path can be gone even when the toolchain
matches. Check before importing:

```
ls .lake/packages/mathlib/Mathlib/<Path>.lean
```

Known: `Mathlib.Tactic.Omega` does **not** exist — import `Mathlib.Tactic` (whole) for
`omega`. `Mathlib.Order.Parity` is gone; parity lives in `Mathlib.Algebra.Ring.Parity`
(with the base in `Mathlib.Algebra.Group.Even`).

## Tactics

- Prefer `omega` for linear arithmetic over naturals/integers (including `2 * x` terms) and
  `ring` for normalizing a small monoid equation. Both are much cleaner than manual
  `mul_comm` / `Nat.mul_two` rewrites.
- Keep the proof text in the file's own language (Spanish in this repo) and phrase theorems
  with `/-- -/` docstrings.