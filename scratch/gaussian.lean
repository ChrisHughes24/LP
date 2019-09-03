import data.matrix .matrix_pequiv tactic.linarith data.zmod.basic

variables {α : Type*}

open equiv pequiv matrix

local infix ` ⬝ `:70 := matrix.mul
local postfix `ᵀ` : 1500 := transpose

namespace pequiv

def diagonal_ul (m n r : ℕ) : fin m ≃. fin n :=
{ to_fun := λ i, if hi : i.1 < r ∧ i.1 < n then some ⟨i.1, hi.2⟩ else none,
  inv_fun := λ j, if hj : j.1 < r ∧ j.1 < m then some ⟨j.1, hj.2⟩ else none,
  inv := λ ⟨i, hi⟩ ⟨j, hj⟩, begin
    clear_aux_decl,
    dsimp,
    split_ifs,
    { simp [eq_comm] },
    { simp, intros h, simp [*, -not_lt] at * },
    { simp, intro h, simp [*, -not_lt] at * },
    { simp }
  end }

lemma symm_diagonal_ul (m n r : ℕ) : (diagonal_ul m n r).symm =
  diagonal_ul n m r := rfl

def equiv.anti_diagonal (n : ℕ) : fin n ≃ fin n :=
{ to_fun := λ i, ⟨n - (i.1 + 1), nat.sub_lt (lt_of_le_of_lt (nat.zero_le _) i.2) (nat.succ_pos _)⟩,
  inv_fun := λ i, ⟨n - (i.1 + 1), nat.sub_lt (lt_of_le_of_lt (nat.zero_le _) i.2) (nat.succ_pos _)⟩,
  left_inv := λ ⟨i, hi⟩, fin.eq_of_veq $
    by dsimp; rw [nat.sub_add_eq_add_sub hi, nat.succ_sub_succ, nat.sub_sub_self (le_of_lt hi)],
  right_inv := λ ⟨i, hi⟩, fin.eq_of_veq $
    by dsimp; rw [nat.sub_add_eq_add_sub hi, nat.succ_sub_succ, nat.sub_sub_self (le_of_lt hi)] }

def diagonal_dr (m n r : ℕ) : fin m ≃. fin n :=
((equiv.anti_diagonal m).to_pequiv.trans (diagonal_ul m n r)).trans
  (equiv.anti_diagonal n).to_pequiv

end pequiv

/-- pick a matrix element that matches a given property or return none in case of no match. -/
def pick (p : α → Prop) [decidable_pred p] {m n : ℕ} (A : matrix (fin m) (fin n) α) :
  option (fin m × fin n) :=
if h : ∃ (ij : fin m × fin n), p (A ij.1 ij.2) then some (encodable.choose h) else none

open pequiv

def Gaussian_elimination [discrete_field α] : Π {m n}, matrix (fin m) (fin n) α →
   (matrix (fin m) (fin m) α × matrix (fin n) (fin n) α × ℕ)
| (x+1) (y+1) A :=
  match pick (λ el : α, el ≠ 0) A with
  | none        := (1, 1, 0)
  | some (i, j) :=
    let B := (swap 0 i).to_pequiv.to_matrix ⬝ A ⬝
      (swap 0 j).to_pequiv.to_matrix in
    let ur := (diagonal_ul 1 (x+1) 1).to_matrix ⬝ B ⬝
      (diagonal_dr (y+1) y y).to_matrix in
    let dl := (A i j)⁻¹ • (diagonal_dr x (x+1) x).to_matrix ⬝ B ⬝
      (diagonal_ul (y+1) 1 1).to_matrix in
    let dr := (diagonal_dr x (x+1) x).to_matrix ⬝ B ⬝
      (diagonal_dr (y+1) y y).to_matrix in
    let ⟨L, U, r⟩ := Gaussian_elimination (dr - dl ⬝ ur) in
    --L
    ((swap 0 i).to_pequiv.to_matrix ⬝
      ((single 0 0).to_matrix +
      (diagonal_dr (x+1) x x).to_matrix ⬝
      (dl ⬝ (diagonal_ul 1 (x+1) 1).to_matrix +
        L ⬝ (diagonal_dr x (x+1) x).to_matrix)),
    --U
    (A i j • (single 0 0).to_matrix +
        ((diagonal_dr _ _ y).to_matrix ⬝ U +
         (diagonal_ul _ _ y).to_matrix ⬝ ur) ⬝
        (diagonal_dr y (y+1) y).to_matrix)
      ⬝ (swap 0 j).to_pequiv.to_matrix,
    --r
    r+1)
  end
| x y A := ((1 : matrix (fin x) (fin x) α),
  (1 : matrix (fin y) (fin y) α),
  0)

instance C {p : ℕ} (hp : nat.prime p) : has_repr (zmodp p hp) := fin.has_repr _

instance matrix.has_repr_fin_fun {n : ℕ} {α : Type*} [has_repr α] : has_repr (fin n → α) :=
⟨λ f, repr (vector.of_fn f).to_list⟩

instance {m n} {α : Type*} [has_repr α]: has_repr (matrix (fin m) (fin n) α) := 
matrix.has_repr_fin_fun

def list.to_matrix (m :ℕ) (n : ℕ) (l : list (list ℚ)) : 
  matrix (fin m) (fin n) ℚ :=
λ i j, (l.nth_le i sorry).nth_le j sorry

#eval ((diagonal_ul 5 4 3).to_matrix : matrix _ _ ℚ)

def M := list.to_matrix 2 4 [[1,2,1,0], [4,5,0,1]]

#eval let S := Gaussian_elimination M in S.1 ⬝ (list.to_matrix 2 4 [[1,0,0,0], [0,1,0,0]]) ⬝ 
S.2.1 
