/-
Copyright (c) 2026 Pedro Sánchez Terraf. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pedro Sánchez Terraf
-/

import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-!
# La irracionalidad de √2

**Enunciado** (copiado de `SinMiedoALean/RaizDeDos.lean`):

`√2` es irracional, es decir, no existen naturales `m` y `n` con `n ≠ 0` tales que
`m ^ 2 = 2 * n ^ 2`.

La demostración clásica es un **descenso infinito**: si hay una solución, hay otra
solución estrictamente menor; en `ℕ` eso es imposible.

La prueba se parte en tres lemas, cada uno con una idea sola:

1. `RaizDeDos.even_sq_iff` — un cuadrado es par si y sólo si su base es par.
2. `RaizDeDos.exists_smaller_solution` — el descenso: toda solución produce otra menor.
3. `RaizDeDos.no_descent` — en `ℕ` no hay descenso infinito.

No se cita ningún resultado de Mathlib sobre `√2`.
-/

namespace RaizDeDos

variable {m n : ℕ}

/-- Un cuadrado es par si y sólo si su base es par. -/
theorem even_sq_iff {a : ℕ} : Even (a ^ 2) ↔ Even a := by
  rw [← Nat.not_odd_iff_even, Nat.odd_pow_iff (e := 2) (by omega), ← Nat.not_odd_iff_even]

/-- Si `2 * n ^ 2 = m ^ 2`, entonces `m ^ 2` es par (es `n ^ 2 + n ^ 2`), y por tanto
`m` es par. -/
theorem even_m_of_two_mul_sq (h : 2 * n ^ 2 = m ^ 2) : Even m :=
  even_sq_iff.mp ⟨n ^ 2, by omega⟩

/-- **El descenso.** De una solución `(m, n)` con `n > 0` obtenemos otra solución
`(r, s)` con `s > 0` y `r < m`.

Los pasos son: `m` es par, digamos `m = 2 * r`; al sustituir y cancelar un `2` queda
`n ^ 2 = 2 * r ^ 2`; entonces `n` es par, digamos `n = 2 * s`; al sustituir y cancelar
un `2` queda `2 * s ^ 2 = r ^ 2`. Y como `m = 2 * r`, tenemos `r < m`. -/
theorem exists_smaller_solution (hn : 0 < n) (h : 2 * n ^ 2 = m ^ 2) :
    ∃ r s, 0 < s ∧ 2 * s ^ 2 = r ^ 2 ∧ r < m := by
  -- `m` es par: escribimos `m = 2 * r`.
  obtain ⟨r, hr⟩ := even_iff_exists_two_mul.mp (even_m_of_two_mul_sq h)
  -- Sustituyendo `m = 2 * r` y cancelando el factor `2` común:
  have hnr : n ^ 2 = 2 * r ^ 2 := by
    have h2 : 2 * n ^ 2 = 2 * (2 * r ^ 2) := by
      calc 2 * n ^ 2 = m ^ 2 := h
        _ = (2 * r) ^ 2 := by rw [hr]
        _ = 2 * (2 * r ^ 2) := by ring
    simpa using h2
  -- `n ^ 2 = 2 * r ^ 2` dice que `n` es par: escribimos `n = 2 * s`.
  obtain ⟨s, hs⟩ := even_iff_exists_two_mul.mp
    (even_sq_iff.mp (show Even (n ^ 2) from ⟨r ^ 2, by omega⟩))
  -- Sustituyendo `n = 2 * s` y cancelando el factor `2` común:
  have hsr : 2 * s ^ 2 = r ^ 2 := by
    have h2 : 2 * (2 * s ^ 2) = 2 * r ^ 2 := by
      calc 2 * (2 * s ^ 2) = (2 * s) ^ 2 := by ring
        _ = n ^ 2 := by rw [hs]
        _ = 2 * r ^ 2 := hnr
    simpa using h2
  refine ⟨r, s, ?_, hsr, ?_⟩
  · -- `0 < s`, porque `n = 2 * s` y `n > 0`.
    omega
  · -- `r < m = 2 * r`, porque `r > 0`.
    have hr_pos : 0 < r := by
      rcases Nat.eq_zero_or_pos r with rfl | hr'
      · have hn0 : n ^ 2 = 0 := by rw [hnr]; simp
        have : n = 0 := Nat.pow_eq_zero.mp hn0 |>.1
        omega
      · exact hr'
    rw [hr]
    omega

end RaizDeDos

/-- **No hay descenso infinito.** Si toda solución de un predicado `P` produce otra
solución estrictamente menor, entonces `P` no tiene soluciones. -/
theorem no_descent {P : ℕ → Prop} (hstep : ∀ m, P m → ∃ r, r < m ∧ P r) :
    ∀ m, ¬ P m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    obtain ⟨r, hrm, hr⟩ := hstep m hm
    exact ih r hrm hr

/-- **El enunciado.** `√2` es irracional. -/
theorem sqrt_two_irrational : ¬ ∃ m n, 0 < n ∧ 2 * n ^ 2 = m ^ 2 := by
  intro ⟨m, n, hn, hmn⟩
  have hstep : ∀ k, (∃ n, 0 < n ∧ 2 * n ^ 2 = k ^ 2) →
      ∃ r, r < k ∧ ∃ n, 0 < n ∧ 2 * n ^ 2 = r ^ 2 := by
    intro k hk
    obtain ⟨n, hn', hkn⟩ := hk
    obtain ⟨r, s, hs, hsr, hrm⟩ := RaizDeDos.exists_smaller_solution hn' hkn
    exact ⟨r, hrm, s, hs, hsr⟩
  exact no_descent hstep m ⟨n, hn, hmn⟩

/-!
## Cómo mejoraría la prueba cambiando el enunciado

El enunciado actual obliga a trabajar en `ℕ`, y `0 < n` aparece en el medio de la
conjunción, así que hay que arrastrar la positividad a cada paso.

Con `Int` el enunciado se vuelve `¬ ∃ m n : ℤ, m ^ 2 = 2 * n ^ 2`, sin hipótesis de
positividad:

* No hace falta probar `0 < s` ni `r > 0`: la positividad ya no está en juego.
* La paridad se demuestra de una sola vez, con `Int.even_or_odd` o con
  `2 ∣ m ^ 2 → 2 ∣ m`, sin `omega` sobre naturales.
* El "`r < m`" sigue necesitando un paso, pero se puede formular directamente como
  "existe una solución con `|m|` menor", usando `Nat.lt_of_lt_of_le` y `Int.natAbs`.

Aun así el descenso infinito sigue siendo el corazón de la prueba: `ℤ` no evita el
descenso, sólo lo hace más limpio de escribir.
-/
