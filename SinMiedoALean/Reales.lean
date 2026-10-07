import Mathlib.Tactic

-- Ejemplo de https://leanprover-community.github.io/contribute/style.html#whitespace-and-delimiters
example {x y : ℝ} (hxy : x ≤ y) (h : ∀ ε > 0, y - ε ≤ x) : x = y :=
  le_antisymm hxy <| le_of_forall_pos_le_add <| by
    intro ε hε
    have := h ε hε
    linarith
