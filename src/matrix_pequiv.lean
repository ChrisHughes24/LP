import data.matrix .pequiv

namespace pequiv
open matrix

universes u v x w

variables {k l m n o p : Type u}
variables [fintype k] [fintype l] [fintype m] [fintype n] [fintype o] [fintype p]
variables [decidable_eq k] [decidable_eq l] [decidable_eq m] [decidable_eq n]
  [decidable_eq o] [decidable_eq p]
variables {R : Type v} [ring R]

local infix ` ⬝ `:70 := matrix.mul
local postfix `ᵀ` : 1500 := transpose

def to_matrix (f : pequiv m n) : matrix m n R
| i j := if j ∈ f i then 1 else 0

lemma to_matrix_symm (f : pequiv m n) : (f.symm.to_matrix : matrix n m R) = f.to_matrixᵀ :=
by ext; simp only [transpose, mem_iff_mem f, to_matrix]; congr

lemma to_matrix_refl : ((pequiv.refl n).to_matrix : matrix n n R) = 1 :=
by ext; simp [to_matrix, one_val]; congr

lemma to_matrix_trans (f : pequiv m n) (g : pequiv n o) :
  ((f.trans g).to_matrix : matrix m o R) = f.to_matrix ⬝ g.to_matrix :=
begin
  ext i j,
  dsimp [to_matrix, matrix.mul, pequiv.trans],
  cases h : f i with i',
  { simp [h] },
  { rw finset.sum_eq_single i';
    simp [h, eq_comm] {contextual := tt} }
end

end pequiv