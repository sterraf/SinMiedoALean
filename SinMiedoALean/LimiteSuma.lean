/-
Copyright (c) 2026 Pedro Sánchez Terraf. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pedro Sánchez Terraf
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-!
# Límite de una suma

Definición ε-δ del límite en un punto de ℝ y demostración de que
"el límite de la suma es la suma de los límites".
-/

namespace AnalisisBasico

/-- Límite de `f` en `a` igual a `L`: para todo `ε > 0` existe `δ > 0` tal que
si `0 < |x - a| < δ` entonces `|f x - L| < ε`. -/
def Limite (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ, 0 < |x - a| ∧ |x - a| < δ → |f x - L| < ε

/-- El límite de la suma es la suma de los límites. -/
theorem LimiteSuma (f g : ℝ → ℝ) (a L M : ℝ)
    (hf : Limite f a L) (hg : Limite g a M) :
    Limite (fun x => f x + g x) a (L + M) := by
  intro ε hε
  have hε2 : 0 < ε / 2 := by
    exact half_pos hε
  obtain ⟨δ1, hδ1_pos, hδ1⟩ := hf (ε / 2) hε2
  obtain ⟨δ2, hδ2_pos, hδ2⟩ := hg (ε / 2) hε2
  use min δ1 δ2
  constructor
  · exact lt_min hδ1_pos hδ2_pos
  · intro x hx
    calc
      |(f x + g x) - (L + M)| = |(f x - L) + (g x - M)| := by rw [add_sub_add_comm]
      _ ≤ |f x - L| + |g x - M| := abs_add_le (f x - L) (g x - M)
      _ < ε / 2 + ε / 2 := by
        apply add_lt_add
        · exact hδ1 x ⟨hx.1, hx.2.trans_le (min_le_left _ _)⟩
        · exact hδ2 x ⟨hx.1, hx.2.trans_le (min_le_right _ _)⟩
      _ = ε := by ring

end AnalisisBasico
