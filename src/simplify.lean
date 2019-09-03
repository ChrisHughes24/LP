import simplex

open matrix fintype finset function pequiv partition tableau
variables {m n : ℕ}

local notation `rvec` : 2000 n := matrix (fin 1) (fin n) ℚ
local notation `cvec` : 2000 m := matrix (fin m) (fin 1) ℚ
local infix ` ⬝ `:70 := matrix.mul
local postfix `ᵀ` : 1500 := transpose

@[derive _root_.decidable_eq] inductive undo : Type
| unrestrict : ℕ → undo
| revive     : ℕ → undo
| delete     : ℕ → undo

instance : has_repr undo :=
⟨λ u, undo.cases_on u
  (λ n, "unrestrict " ++ repr n)
  (λ n, "revive " ++ repr n)
  (λ n, "delete " ++ repr n)⟩

open undo

structure stableau (m n : ℕ) extends tableau m n :=
(feasible : to_tableau.feasible)
(dead : finset (fin (m + n)))
(undo_stack : list undo)

#print tableau
namespace stableau

def simplex (w : tableau m n → bool) (obj : fin m) (T : stableau m n) :
  stableau m n × termination :=
let s := T.to_tableau.simplex w obj T.feasible in
prod.mk
  { feasible := feasible_simplex,
    dead := T.dead,

   ..s.1 }
  s.2




end stableau
