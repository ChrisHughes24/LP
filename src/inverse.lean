import data.matrix data.rat.basic linear_algebra.determinant
variable {n : ℕ}

open matrix

local infix ` ⬝ `:70 := matrix.mul
local postfix `ᵀ` : 1500 := matrix.transpose

def comatrix (M : matrix (fin n) (fin n) ℚ) : matrix (fin n) (fin n) ℚ :=
begin
  cases n,
  { exact fin.elim0 },
  { exact λ i j, (-1) ^ (i + j : ℕ) * det (minor M
      (λ i' : fin n, if i'.1 < i.1 then i'.cast_succ else i'.succ)
      (λ j' : fin n, if j'.1 < j.1 then j'.cast_succ else j'.succ)) }
end

def list.to_matrix (m :ℕ) (n : ℕ) (l : list (list ℚ)) : matrix (fin m) (fin n) ℚ :=
λ i j, (l.nth_le i sorry).nth_le j sorry


instance has_repr_fin_fun {n : ℕ} {α : Type*} [has_repr α] : has_repr (fin n → α) :=
⟨λ f, repr (vector.of_fn f).to_list⟩

instance {m n} : has_repr (matrix (fin m) (fin n) ℚ) := has_repr_fin_fun

def inverse (M : matrix (fin n) (fin n) ℚ) : matrix (fin n) (fin n) ℚ :=
(det M)⁻¹ • (comatrix M)ᵀ 

lemma mul_inverse : Π n, (M : matrix (fin n) (fin n) ℚ) : M ⬝ inverse M = 1 :=
begin


end

def M := list.to_matrix 3 3 [[1,2,3],[1,2,0],[0,1,0]]

#eval M ⬝ inverse M