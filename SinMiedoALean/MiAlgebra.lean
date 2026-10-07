/-
Copyright (c) 2026 Pedro Sánchez Terraf. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pedro Sánchez Terraf
-/
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Set.Defs

/-!
# Álgebra abstracta básica

Definiciones y resultados básicos de álgebra abstracta
-/

section PositiveCone

variable {R : Type*} [Ring R]

/--
Un *cono positivo* en un anillo: un subconjunto que contiene al cero, es
cerrado por suma y por producto, y contiene a cada elemento o a su opuesto.
-/
class IsPositiveCone (Pos : Set R) : Prop where
  /-- El cero pertenece al cono. -/
  mem_zero : (0 : R) ∈ Pos
  /-- El cono es cerrado por suma. -/
  add_mem : ∀ {a b : R}, a ∈ Pos → b ∈ Pos → a + b ∈ Pos
  /-- El cono es cerrado por producto. -/
  mul_mem : ∀ {a b : R}, a ∈ Pos → b ∈ Pos → a * b ∈ Pos
  /-- Cada elemento o su opuesto pertenece al cono. -/
  mem_or_neg_mem : ∀ x : R, x ∈ Pos ∨ -x ∈ Pos

variable {Pos : Set R} [IsPositiveCone Pos]

end PositiveCone
