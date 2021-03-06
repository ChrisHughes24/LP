import data.matrix data.rat.basic linear_algebra.basis data.fintype
import linear_algebra.determinant .misc order.pilex order.lexicographic .list_sup
import data.list.min_max .fin_find

open matrix fintype finset

variables {m n : ℕ}
variables (A : matrix (fin m) (fin n) ℚ)

local notation `rvec`:2000 n := matrix (fin 1) (fin n) ℚ
local notation `cvec`:2000 m := matrix (fin m) (fin 1) ℚ

-- def column (j : fin n) : cvec m := λ i _, A i j

-- def row (i : fin m) : rvec n := λ _ j, A i j

variables (b : cvec m) (c : cvec n)

def cvec.ordered_comm_group : ordered_comm_group (cvec n) :=
matrix.ordered_comm_group

local attribute [instance] cvec.ordered_comm_group

def cvec.decidable_le : decidable_rel ((≤) : (cvec n) → (cvec n) → Prop) :=
matrix.decidable_le

local attribute [instance] cvec.decidable_le

--instance : partial_order (matrix (fin m) (fin n) ℚ) := pi.partial_order

constant matrix.has_inv : has_inv (matrix (fin n) (fin n) ℚ)

local notation M `⬝` N := M.mul N
local postfix `ᵀ` : 1500 := transpose

def is_feasible (x : cvec n) : Prop :=
0 ≤ x ∧ A ⬝ x = b

instance (x : cvec n) : decidable (is_feasible A b x) :=
by dunfold is_feasible; apply_instance

def is_optimal (x : cvec n) : Prop :=
is_feasible A b x ∧ ∀ y, is_feasible A b y → cᵀ ⬝ y ≤ cᵀ ⬝ x

def is_invertible' (M : matrix (fin m) (fin n) ℚ) : Prop :=
∃ h : m = n, by rw h at M; exact det M ≠ 0

instance is_invertible'.decidable : decidable_pred (@is_invertible' m n) :=
λ _, by unfold is_invertible'; apply_instance

def comatrix (M : matrix (fin n) (fin n) ℚ) : matrix (fin n) (fin n) ℚ :=
begin
  cases n,
  { exact fin.elim0 },
  { exact λ i j, (-1) ^ (i + j : ℕ) * det (minor M
    (λ i' : fin n, if i'.1 < i.1 then i'.cast_le sorry
      else i'.succ)
    (λ j' : fin n, if j'.1 < j.1 then j'.cast_le sorry
      else j'.succ)) }
end

def inverse (M : matrix (fin m) (fin n) ℚ) : matrix (fin n) (fin m) ℚ :=
if h : m = n then by subst h; exact (det M)⁻¹ • (comatrix M)ᵀ else 0

def rvec.to_list {n : ℕ} (x : rvec n) : list ℚ :=
(vector.of_fn (x 0)).1

def lex_rvec : linear_order (rvec m) :=
@pilex.linear_order _ _ _ (is_well_order.wf _)
  (λ _, pilex.linear_order (is_well_order.wf _))

def lex_rvec_decidable_linear_order : decidable_linear_order (rvec m) :=
{ decidable_le := λ x y, decidable_of_iff
    (list.lex (<) (rvec.to_list x) (rvec.to_list y) ∨ x = y) sorry,
  ..lex_rvec }

local attribute [instance] lex_rvec_decidable_linear_order

def lex_ordered_comm_group_rvec : ordered_comm_group (rvec m) :=
@pilex.ordered_comm_group _ _ _ (λ _, pilex.ordered_comm_group)

-- local attribute [instance] lex_ordered_comm_group_rvec
--   lex_rvec_decidable_linear_order

def pert_rat (m : ℕ) : Type := ℚ × rvec m

instance : decidable_eq (pert_rat m) := by unfold pert_rat; apply_instance

instance : add_comm_group (pert_rat m) := prod.add_comm_group

instance : module ℚ (pert_rat m) := prod.module

instance : decidable_linear_order (pert_rat m) :=
by letI := @lex_rvec_decidable_linear_order m; exact
{ decidable_le := @prod.lex.decidable _ _ _ _ _ _ _
    (lex_rvec_decidable_linear_order).decidable_le,
  ..lex_linear_order }

instance pert_rat.decidable_le (i j : pert_rat m) : decidable (i ≤ j) :=
@decidable_linear_order.decidable_le _ pert_rat.decidable_linear_order i j

instance has_repr_fin_fun {n : ℕ} {α : Type*} [has_repr α] : has_repr (fin n → α) :=
⟨λ f, repr (vector.of_fn f).to_list⟩

instance {m n} : has_repr (matrix (fin m) (fin n) ℚ) := has_repr_fin_fun

instance : has_repr (pert_rat m) := prod.has_repr

def pivot (A : matrix (fin m) (fin n) ℚ) (c : rvec n) (b : cvec m)
  (B : array m (fin n))
  (NB : array (n - m) (fin n))
  (i : fin (n - m)) (j : fin m) :
  array m (fin n) × -- basis
  array (n - m) (fin n) × -- non basis
  matrix (fin m) (fin (n - m)) ℚ × -- A_bar
  (rvec m) × -- c_B
  (rvec (n - m)) × --c_N
  (cvec m) × --b_bar
  matrix (fin m) (fin m) ℚ -- pert
  :=
let NBi : fin n := NB.read i in
let Bj : fin n := B.read j in
let NB' := NB.write i Bj in
let B' := B.write j NBi in
let A_B'_inverse := inverse (minor A id B'.read) in
⟨B',
  NB',
  A_B'_inverse ⬝ minor A id NB'.read,
  minor c id B'.read,
  minor c id NB'.read,
  A_B'_inverse ⬝ b,
  A_B'_inverse⟩

lemma true_well_founded {α : Type*} :
  well_founded (λ (_ _ : α), true) := sorry

def simplex [inhabited (fin m)] (A : matrix (fin m) (fin n) ℚ)
  (c : rvec n) (b : cvec m) :
  Π (B : array m (fin n))
  (NB : array (n - m) (fin n))
  (A_bar : matrix (fin m) (fin (n - m)) ℚ)
  (c_B : rvec m) (c_N : rvec (n - m)) (b_bar : cvec m)
  (pert : (matrix (fin m) (fin m) ℚ))
  (pivots : ℕ),
  ℕ × option
  (array m (fin n) × -- basis
  array (n - m) (fin n) × -- non basis
  matrix (fin m) (fin (n - m)) ℚ × -- A_bar
  (rvec m) × -- c_B
  (rvec (n - m)) × --c_N
  (cvec m) × --b_bar
  matrix (fin m) (fin m) ℚ) -- pert)
| B NB A_bar c_B c_N b_bar pert pivots :=
let reduced_cost := c_N - c_B ⬝ A_bar in
let i' := (list.fin_range (n - m)).find (λ i, 0 < column reduced_cost (fin 1) i) in
match i' with
| none := (pivots, some (B, NB, A_bar, c_B, c_N, b_bar, pert))
| some i :=
  let ratio_pert : fin m → pert_rat m := λ j : fin m,
    (A_bar j i)⁻¹ • (b_bar j 0, row' pert (fin 1) j) in
  let l := (list.fin_range m).filter (λ j, 0 < ratio_pert j) in
  match l with
  | [] := (pivots + 1, none)
  | (a::l) :=
  let j : fin m := list.argmin ratio_pert (a :: l) in
  let ⟨B', NB', A_bar', c_B', c_N', b_bar', pert'⟩ :=
    pivot A c b B NB i j in
  have wf : true, from trivial,
  simplex B' NB' A_bar' c_B' c_N' b_bar' pert' (pivots + 1)
  end
end
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, true_well_founded⟩],
  dec_tac := tactic.assumption}

instance read_dec_pred (a : array m (fin n)) (i : fin n) :
  decidable_pred (λ (k : fin m), array.read a k = i) := by apply_instance

instance array.mem_decidable {α : Type*} [decidable_eq α] (x : array m α) :
  decidable_pred (λ a : α, @array.mem m α a x) :=
by dunfold array.mem; apply_instance

def find_optimal_solution_from_starting_basis [inhabited (fin m)] (A : matrix (fin m) (fin n) ℚ)
  (c : rvec n) (b : cvec m) (B : array m (fin n)) : ℕ × option (cvec n) :=
let NB : array (n - m) (fin n) :=
  vector.to_array ⟨(list.fin_range n).filter (λ i, ¬ B.mem i), sorry⟩ in
let A_B := minor A id B.read in
let A_N := minor A id NB.read in
let pert := inverse A_B in
let A_bar := pert ⬝ A_N in
let c_B := minor c id B.read in
let c_N := minor c id NB.read in
let b_bar := pert ⬝ b in
match simplex A c b B NB A_bar c_B c_N b_bar pert 0 with
| (pivots, none) := (pivots, none)
| (pivots, some ⟨B', NB', A_bar', c_B', c_N', b_bar', pert'⟩) := prod.mk pivots $
some (λ i _,
  match @fin.find _ (λ k, B'.read k = i) (read_dec_pred _ _) with
  | none := 0
  | some k := b_bar' k 0
  end)
end

/- test code -/

instance {m : ℕ} : inhabited (fin m.succ) := ⟨0⟩

def list.to_matrix (m :ℕ) (n : ℕ) (l : list (list ℚ)) : matrix (fin m) (fin n) ℚ :=
λ i j, (l.nth_le i sorry).nth_le j sorry

def found_solution_is_feasible [inhabited (fin m)] (A : matrix (fin m) (fin n) ℚ)
  (c : rvec n) (b : cvec m) (B : array m (fin n)) : bool :=
match find_optimal_solution_from_starting_basis A c b B with
| (_, none) := tt
| (_, some x) := (A ⬝ x = b ∧ 0 ≤ x : bool)
end

def is_optimal_bool [inhabited (fin m)] (A : matrix (fin m) (fin n) ℚ)
  (c : rvec n) (b : cvec m) (B : array m (fin n)) : bool :=
let NB : array (n - m) (fin n) :=
  vector.to_array ⟨(list.fin_range n).filter (λ i, ¬ B.mem i), sorry⟩ in
let A_B := minor A id B.read in
let A_N := minor A id NB.read in
let pert := inverse A_B in
let A_bar := pert ⬝ A_N in
let c_B := minor c id B.read in
let c_N := minor c id NB.read in
let b_bar := pert ⬝ b in
match simplex A c b B NB A_N c_B c_N b_bar pert 0 with
| (_, none) := tt
| (_, some ⟨B', NB', A_bar', c_B', c_N', b_bar', pert'⟩) := c_N' - c_B' ⬝ A_bar' ≤ 0
end

def is_feasible_basis [inhabited (fin m)] (A : matrix (fin m) (fin n) ℚ)
  (c : rvec n) (b : cvec m) (B : array m (fin n)) : Prop :=
let A_B := minor A id B.read in
let NB : array (n - m) (fin n) :=
  vector.to_array ⟨(list.fin_range n).filter (λ i, ¬ B.mem i), sorry⟩ in
let A_N := minor A id NB.read in
let pert := inverse A_B in
let A_bar := pert ⬝ A_N in
let c_B := minor c id B.read in
let c_N := minor c id NB.read in
let b_bar := pert ⬝ b in
let x : cvec n := λ i _, match @fin.find _ (λ k, B.read k = i) (read_dec_pred _ _) with
  | none := 0
  | some k := b_bar k 0
  end in
(0 : cvec n) ≤ x ∧ A ⬝ x = b ∧ det A_B ≠ 0

def finishing_basis [inhabited (fin m)] (A : matrix (fin m) (fin n) ℚ)
  (c : rvec n) (b : cvec m) (B : array m (fin n)) : option (array m (fin n)) :=
let NB : array (n - m) (fin n) :=
  vector.to_array ⟨(list.fin_range n).filter (λ i, ¬ B.mem i), sorry⟩ in
let A_B := minor A id B.read in
let A_N := minor A id NB.read in
let pert := inverse A_B in
let A_bar := pert ⬝ A_N in
let c_B := minor c id B.read in
let c_N := minor c id NB.read in
let b_bar := pert ⬝ b in
option.map prod.fst (simplex A c b B NB A_N c_B c_N b_bar pert 0).2

def test  [inhabited (fin m)] (A : matrix (fin m) (fin n) ℚ)
  (c : rvec n) (b : cvec m) (B : array m (fin n)) :=
let NB : array (n - m) (fin n) :=
  vector.to_array ⟨(list.fin_range n).filter (λ i, ¬ B.mem i), sorry⟩ in
let A_B := minor A id B.read in
let A_N := minor A id NB.read in
let pert := inverse A_B in
let A_bar := pert ⬝ A_N in
let c_B := minor c id B.read in
let c_N := minor c id NB.read in
let b_bar := pert ⬝ b in
let reduced_cost := c_N - c_B ⬝ A_bar in
let b_pert : fin m → pert_rat m := λ j : fin m,
     (A_bar j ⟨0, sorry⟩)⁻¹ • (b_bar j 0, row' pert (fin 1) j) in
let reduced_cost := c_N - c_B ⬝ A_bar in
let i' := (list.fin_range (n - m)).find (λ i, 0 < column reduced_cost (fin 1) i) in
match i' with
| none := sorry
| some i :=
  let ratio_pert : fin m → pert_rat m := λ j : fin m,
     (A_bar j i)⁻¹ • (b_bar j 0, row' pert (fin 1) j) in
  let l := (list.fin_range m).filter (λ j, 0 < ratio_pert j) in ratio_pert end
--simplex A c b B NB A_N c_B c_N b_bar pert

def objective_function_value (c : rvec n) (x : cvec n) := c ⬝ x


-- (list.fin_range (n - m)).find (λ i, 0 < column reduced_cost (fin 1) i)

-- pivot A c b B NB

instance [inhabited (fin m)] (A : matrix (fin m) (fin n) ℚ)
  (c : rvec n) (b : cvec m) (B : array m (fin n)) :
  decidable (is_feasible_basis A c b B) :=
by dunfold is_feasible_basis; apply_instance


def X'  : pert_rat 2 := (0, X)
--#eval X
#eval X'
#eval  (0 = X' : bool)

-- def ex.A := list.to_matrix 3 4 [[12,-1,1,1],
--                      [1,1.45,1,0],
--                      [1,2,0,1]]

-- def ex.c : rvec 4 := λ _ i, (list.nth_le [1, 1.2, 1, 1.3] i sorry)
-- --#eval ex.c
-- def ex.b : cvec 3 := (λ i _, (list.nth_le [2, 2, 4] i sorry))
-- --#eval ex.b
-- def ex.B : array 3 (fin 4) := list.to_array [0, 1, 3]

-- def ex.NB : array 1 (fin 4) := list.to_array [2]

-- def ex.A := list.to_matrix 2 5 [[1,1,0,1,0], [0,1,-1,0,1]]

-- def ex.b : cvec 2 := (λ i _, (list.nth_le [8,0] i sorry))
-- --#eval ex.b
-- def ex.c : rvec 5 := λ _ i, (list.nth_le [1, 1, 1, 0, 0] i sorry)
-- --#eval ex.c
-- def ex.B : array 2 (fin 5) := list.to_array [3,4]

def ex.A := list.to_matrix 3 7 [[1/4, - 8, -  1, 9, 1, 0, 0],
                                [1/2, -12, -1/2, 3, 0, 1, 0],
                                [  0,   0,    1, 0, 0, 0, 1]]

def ex.b : cvec 3 := (λ i _, list.nth_le [0,0,1] i sorry)
--#eval ex.b
def ex.c : rvec 7 := λ _ i, (list.nth_le [3/4, -20, 1/2, -6, 0, 0, 0] i sorry)
--#eval ex.c
def ex.B : array 3 (fin 7) := list.to_array [4,5,6]

-- #eval (found_solution_is_feasible ex.A ex.c ex.b ex.B)

#eval (find_optimal_solution_from_starting_basis ex.A ex.c ex.b ex.B)
--set_option trace.fun_info true
#eval (is_optimal_bool ex.A ex.c ex.b ex.B)

-- (some [[2064/445]])
-- (some [[6401/1895]])
#eval (is_feasible_basis ex.A ex.c ex.b ex.B : bool)
-- #eval (show matrix _ _ ℚ, from minor ex.A id ex.B.read) *
--   inverse (show matrix _ _ ℚ, from minor ex.A id ex.B.read )
-- #eval ((1 : matrix (fin 1) (fin 1) ℚ) - (minor ex.c id ex.B.read) ⬝
--   inverse (minor ex.A id ex.B.read) ⬝
--   (minor ex.A id ex.NB.read))

#eval finishing_basis ex.A ex.c ex.b ex.B

#eval test ex.A ex.c ex.b ex.B

#eval (let x : cvec 4 := λ i _, list.nth_le [0, 80/89, 62/89, 196/89] i sorry in
  let A := list.to_matrix 3 4 [[12, -1, 1, 1],
                     [1, 1.45, 1, 0],
                     [1, 2, 0, 1]]
                     in A ⬝ x
 )
