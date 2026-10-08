import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Ring

def doble n := 2 * n
/- El guión bajo como "hueco" me da una pista de qué tengo que poner -/
-- def doble n := 2 * _
/- Pero así no anda: -/
-- def doble n := n * _

#eval doble 5

#eval doble (doble 4)

#eval (4, 6).fst

def sqr : ℕ → ℕ
  | 0 => 0
  | n + 1 => sqr n + 2 * n + 1

#eval sqr 1

#eval sqr 2

#check sqr

def triang_cod n m := (n + m) * ((n + m) + 1) / 2 + m

#eval triang_cod 3 1

#check triang_cod

/--
Dada una forma de codificar pares, codificar ternas.
-/
def cod_terna (f : ℕ → ℕ → ℕ) k l m := f k (f l m)

-- falla, ¿por qué?
-- def resto n m := n - m

example : sqr 0 = 0 := rfl

example : sqr 1 = 1 := rfl

example : sqr 2 = 4 := rfl

example : sqr 10 = 100 := rfl

example k : sqr k = k ^ 2 := by
  induction k
  case zero =>
    rfl
  case succ n hn =>
    rw [sqr]
    rw [pow_two] at *
    rw [hn] -- antes me puse a distribuir aquí...
    ring

/-
Claudio says:
-/
@[simp] theorem sqr_zero : sqr 0 = 0 := rfl
@[simp] theorem sqr_add_one (n : ℕ) : sqr (n + 1) = sqr n + 2 * n + 1 := rfl

theorem sqr_eq (n : ℕ) : sqr n = n ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [sqr_add_one, ih]; ring
