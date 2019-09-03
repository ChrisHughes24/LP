import data.matrix data.rat.basic linear_algebra.basis data.fintype tactic.omega
import algebra.associated
import linear_algebra.determinant .misc

noncomputable theory
universes u v w

open matrix fintype finset function
variables {m n k : Type u} [fintype m] [fintype n] [fintype k]
variables [decidable_eq m] [decidable_eq n] [decidable_eq k]
variables {one : Type u} [unique one]
variables (A M : matrix m n ℚ)

variables (b : matrix m one ℚ) (c x : matrix n one ℚ)

local notation M `⬝` N := M.mul N
local postfix `ᵀ` : 1500 := transpose

def is_feasible : Prop := 0 ≤ x ∧ A ⬝ x = b

instance decidable_le : decidable_rel ((≤) : matrix m n ℚ → matrix m n ℚ → Prop) :=
λ M N, show decidable (∀ i j, M i j ≤ N i j), by apply_instance

instance : decidable (is_feasible A b x) :=
by dunfold is_feasible; apply_instance

def is_optimal : Prop :=
is_feasible A b x ∧ ∀ y, is_feasible A b y → cᵀ ⬝ y ≤ cᵀ ⬝ x

def basis (B : m → n) : matrix m m ℚ := minor A id B

def non_basis (B : m → n) : matrix m {b // b ∉ univ.image B}  ℚ :=
minor A id subtype.val

def c_basis (B : m → n) : matrix m one ℚ := minor c B id

def c_non_basis (B : m → n) : matrix {b // b ∉ univ.image B} one ℚ :=
minor c subtype.val id

--#print non_basis
def reduced_cost (B : m → n) : Prop :=
is_invertible (basis A B) ∧
(c_non_basis c B)ᵀ ⬝ non_basis _ B = 0



lemma is_optimal_of_check_reduced_cost (x : cvec n) (B : finset (fin n)) :
  check_reduced_cost A c x B ∧ is_feasible A b x → is_optimal A b c x := sorry

set_option profiler true

def ex.A : matrix (fin 2) (fin 4) ℚ :=
λ i j, (list.nth_le [[1,0,1,0], [1,2,0,1]] i sorry).nth_le j sorry

def ex.B : finset (fin 4) := {2,3}

def ex.c : cvec 4 := λ i _, (list.nth_le [1,1,0,0] i sorry)

def ex.b : cvec 2 := λ i _, (list.nth_le [2,4] i sorry)

def ex.x : cvec 4 := λ i _, (list.nth_le [0,0,2,4] i sorry)


--#reduce (is_feasible ex.A ex.b ex.x : bool)

--set_option trace.class_instances true
--#reduce (check_reduced_cost ex.A ex.c ex.x ex.B : bool)

def ex2.A : matrix (fin 2) (fin 4) ℚ :=
  λ i j, (list.nth_le [[1,0,1,0], [1,2,0,1]] i sorry).nth_le j sorry

def ex2.B : finset (fin 4) := {0,1}

def ex2.c : cvec 4 := λ i _, (list.nth_le [1,1,0,0] i sorry)

def ex2.b : cvec 2 := λ i _, (list.nth_le [2,4] i sorry)

def ex2.x : cvec 4 := λ i _, (list.nth_le [2,1,0,0] i sorry)


#eval (is_feasible ex2.A ex2.b ex2.x : bool)

#eval (check_reduced_cost ex2.A ex2.c ex2.x ex2.B : bool)
