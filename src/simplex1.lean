import data.matrix data.rat.basic linear_algebra.basis data.fintype tactic.omega
import algebra.associated
import linear_algebra.determinant

open matrix fintype finset

variables {m n : ℕ}
variables (A : matrix (fin m) (fin n) ℚ)

local notation `rvec` n := matrix (fin 1) (fin n) ℚ
local notation `cvec` m := matrix (fin m) (fin 1) ℚ

-- def column (j : fin n) : cvec m := λ i _, A i j

-- def row (i : fin m) : rvec n := λ _ j, A i j

variables (b : cvec m) (c : cvec n)

--instance : partial_order (matrix (fin m) (fin n) ℚ) := pi.partial_order

constant matrix.has_inv : has_inv (matrix (fin n) (fin n) ℚ)

local notation M `⬝` N := M.mul N
local postfix `ᵀ` : 1500 := transpose

instance : partial_order (matrix (fin m ) (fin n) ℚ) := pi.partial_order

def is_feasible (x : cvec n) : Prop :=
0 ≤ x ∧ A ⬝ x = b

instance decidable_le : decidable_rel ((≤) : matrix (fin m) (fin n) ℚ → matrix (fin m) (fin n) ℚ → Prop) :=
λ M N, show decidable (∀ i j, M i j ≤ N i j), by apply_instance

instance (x : cvec n) : decidable (is_feasible A b x) :=
by dunfold is_feasible; apply_instance

def is_optimal (x : cvec n) : Prop :=
is_feasible A b x ∧ ∀ y, is_feasible A b y → cᵀ ⬝ y ≤ cᵀ ⬝ x

def is_invertible (M : matrix (fin m) (fin n) ℚ) : Prop :=
∃ h : m = n, by rw h at M; exact det M ≠ 0

instance is_invertible.decidable : decidable_pred (@is_invertible m n) :=
λ _, by unfold is_invertible; apply_instance

def comatrix (M : matrix (fin n) (fin n) ℚ) : matrix (fin n) (fin n) ℚ :=
begin
  cases n,
  { exact fin.elim0 },
  { exact λ i j, det (minor M
    (λ i' : fin n, if i'.1 < i.1 then i'.cast_le sorry
      else i'.succ)
    (λ j' : fin n, if j'.1 < j.1 then j'.cast_le sorry
      else j'.succ)) }
end

def inverse (M : matrix (fin m) (fin n) ℚ) : matrix (fin n) (fin m) ℚ :=
if h : m = n then by subst h; exact (det M)⁻¹ • (comatrix M)ᵀ else 0

def check_reduced_cost (x : cvec n) (B : finset (fin n)) : Prop :=
let permB : matrix (fin n) (fin B.card) ℚ :=
  minor 1 id (λ i, (finset.sort (≤) B).nth_le i.1 (by simpa using i.2)) in
let N : finset (fin n) := univ.filter (∉ B) in
let permN : matrix (fin n) (fin N.card) ℚ :=
  minor 1 id (λ i, (finset.sort (≤) N).nth_le i.1 (by simpa using i.2)) in
let basis := A ⬝ permB in
let non_basis := A ⬝ permN in
let ctN := cᵀ ⬝ permN in
let ctB := cᵀ ⬝ permB in
xᵀ ⬝ permN = 0 ∧ is_invertible basis ∧ ctN - ctB ⬝ inverse basis ⬝ non_basis ≤ 0

instance (x : cvec n) (B : finset (fin n)) : decidable (check_reduced_cost A c x B) :=
by dunfold check_reduced_cost; apply_instance

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
