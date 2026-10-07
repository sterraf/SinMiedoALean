import Init.Data.Rat.Basic
import Mathlib.Data.Rat.Init -- Setea la notación `ℚ`

/-
Ejemplo extraído del curso de formalización de [Miguel Pagano](mailto:miguel.pagano@unc.edu.ar)
en [YouTube](https://youtu.be/bYq0VLfmWlk?si=ALSVHEAMaIuiwuCV&t=5397)

Tácticas: `exact?`, `rw?`

- [tácticas en el curso](https://youtu.be/AME_NV5bUbo?si=MQAYDb-lBfQlLbj_&t=4624)
- [variantes de `rw`](https://www.youtube.com/watch?v=-IOTWHPuIJc&t=3920s), hasta el minuto 1:55:30.
--/
example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  calc
    (x + y) * (x + y) = (x + y) * x + (x + y) * y := sorry
    _ = x * x + y * x + (x + y) * y := sorry
    _ = x * x + y * x + x * y + y * y := sorry -- ojo!

--    _ = x * x + y * x + x * y + y * y := sorry

/-
## Qué dijo Claudio luego de escanear esto:

> Outside an exercise like this, Mathlib practice would be to skip the `calc` entirely
> and close the goal with `ring` (which needs `import Mathlib.Tactic.Ring`). Here,
> though, the `calc` presumably *is* the point, so I kept it.
-/

/-
Ejemplos de [estructuras](https://youtu.be/PzpP3n-4nFI?si=tBFwTf9uZLDZD5VE&t=20)
-/
section MisEnterosBase

structure MisEnterosBase where
  minuendo : Nat
  sustraendo : Nat

def MisEnterosBase.fromNat (n : Nat) : MisEnterosBase := ⟨n, 0⟩

#eval MisEnterosBase.fromNat 10

-- Falla porque no sabe qué tipo tiene `⟨10, 5⟩`:
-- #eval ⟨10, 5⟩.minuendo

def MisEnterosBase.mismo_entero (k l : MisEnterosBase) : Prop :=
  k.minuendo + l.sustraendo = l.minuendo + k.sustraendo

open MisEnterosBase

def MisEnteros := Quot mismo_entero -- La ayuda dice "mejor usá `Quotient`"

def MisEnteros.fromNat (n : Nat) : MisEnteros := Quot.mk mismo_entero ⟨n, 0⟩

#check Quot.sound

example : MisEnteros.fromNat 10 = Quot.mk mismo_entero ⟨42, 32⟩ := sorry

end MisEnterosBase

#check MisEnteros

/-
Código nativo de Lean: cómo están definidos los enteros.
-/
#check Int
-- #check ℤ -- No definido (aún!) Corregir imports

/-
Los racionales en Lean.
-/
example : ℚ := Rat.divInt 10 (-1)
example : ℚ := Rat.normalize (-10)
example : ℚ := mkRat (-10) 1

#eval (mkRat (-10) 5)
#eval (mkRat (-10) 4).den
-- #eval .den (mkRat (-10) 4) -- Error!
#eval Rat.den (mkRat (-10) 4)

-- Coerciones
#check (1 + 1)
#check (1 + 1 : Int)
#check (1 + 1 : Int) + 1
