/-
Copyright (c) 2026 Pedro Sánchez Terraf. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pedro Sánchez Terraf
-/

import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Basic
import Mathlib.Order.WellFounded
import Mathlib.Order.RelClasses
import Mathlib.Algebra.Ring.Parity

/-!
# Trabajo básico con naturales

Hacemos algunas cuentas muy básicas. Probamos que raíz de 2 es (ir)racional (?).

SIN usar IA pero usando GOFAI.
-/

-- Tácticas: `exact?`, `rfl`
example : 16 = 4^2 := by
  exact?

-- Tácticas: `sorry`, `tauto`, `existsi`
lemma sqrt_two_rational : ∃ m n, 2 * n ^ 2 = m ^ 2 := sorry

/-
Buscando resultados con [LeanFinder](https://huggingface.co/spaces/delta-lab-ai/Lean-Finder)
o con [LeanSearch](https://leansearch.net/)
-/
-- Dedicado a P. Groisman
lemma sqrt_two_irrational : ¬∃ m n, 0 < n ∧ 2 * n ^ 2 = m ^ 2 := by
  -- fields de las classes para hacer andar esto.
  have wf_nat := instWellFoundedLTNat.wf
  by_contra h
  let set_of_ms := { m | ∃ n, 0 < n ∧ 2 * n ^ 2 = m ^ 2 }
  -- la hip de existencia es exactamente la de ser no vacío
  have has_min_m := WellFounded.has_min wf_nat set_of_ms h
  obtain ⟨m, hm⟩ := has_min_m
  let set_of_ns := { n | 0 < n ∧ 2 * n ^ 2 = m ^ 2 }
  have has_min_n := WellFounded.has_min wf_nat set_of_ns hm.1
  obtain ⟨n, hn⟩ := has_min_n
  have minimal_ex : 0 < n ∧ 2 * n ^ 2 = m ^ 2 := by
    exact hn.1
  have m_sqr_even : Even (m^2) := by
    -- even_iff_exists_two_mul
    rw [mul_comm, Nat.mul_two] at minimal_ex
    rw [Even]
    exact Exists.intro (n ^ 2) (id (Eq.symm minimal_ex.2))
  have m_even : Even m := by
    have even_prod: Even (m * m) := by
      rw [← Nat.pow_two]
      exact m_sqr_even
    rw [Nat.even_mul] at even_prod
    tauto
  obtain ⟨r, hr⟩ := even_iff_exists_two_mul.1 m_even
  -- have four_mul: 2 * n ^ 2 = 2 * (2 * r ^ 2) := by
  --   rw [hr, mul_pow] at minimal_ex
  --   rw [pow_two 2, mul_assoc] at minimal_ex
  --   exact minimal_ex
  have first_reduct: n ^ 2 = 2 * r ^ 2 := by
    rw [hr, mul_pow] at minimal_ex
    rw [pow_two 2, mul_assoc] at minimal_ex
    simp only [mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false] at minimal_ex
    exact minimal_ex.2
  have n_sqr_even : Even (n^2) := by
    -- even_iff_exists_two_mul
    rw [mul_comm, Nat.mul_two] at first_reduct
    rw [Even]
    exact Exists.intro (r ^ 2) (id (first_reduct))
  have n_even : Even n := by
    have even_prod: Even (n * n) := by
      rw [← Nat.pow_two]
      exact n_sqr_even
    rw [Nat.even_mul] at even_prod
    tauto
  obtain ⟨s, hs⟩ := even_iff_exists_two_mul.1 n_even
  -- have four_mul': 2 * (2 * s ^ 2) = 2 * r ^ 2 := by
  --   rw [hs] at first_reduct
  have smaller_example: 2 * s ^ 2 = r ^ 2 := by
    rw [hs, mul_pow] at first_reduct
    rw [pow_two 2, mul_assoc] at first_reduct
    simp only [mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false] at first_reduct
    exact first_reduct
  have r_gt_zero : r > 0 := by
    refine Nat.zero_lt_of_ne_zero ?_
    by_contra h
    have m_zero : m = 0 := by linarith
    have n_sqr_zero : 2 * n^2 = 0 := by simp [m_zero, minimal_ex]
    have : n^2 = 0 := two_nsmul_eq_zero.mp n_sqr_zero
    have n_zero : n = 0 := eq_zero_of_pow_eq_zero this
    linarith
  have r_lt : r < m := by
    rw [hr] ; rewrite (occs := .pos [1]) [← one_mul r]
    refine Nat.mul_lt_mul_of_pos_right ?_ ?_
    · simp
    · exact r_gt_zero
  have s_lt : s < n := by linarith
  have zero_lt_s : 0 < s := by linarith
  have r_example : r ∈ set_of_ms := by
    constructor
    · constructor
      · exact zero_lt_s
      · exact Nat.add_right_cancel (congrFun (congrArg HAdd.hAdd smaller_example) m)
  tauto
