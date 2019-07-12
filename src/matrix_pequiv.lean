import data.matrix .pequiv

namespace pequiv
open matrix

universes u v x w

variables {k l m n o p : Type u}
variables [fintype k] [fintype l] [fintype m] [fintype n] [fintype o] [fintype p]
variables [decidable_eq k] [decidable_eq l] [decidable_eq m] [decidable_eq n]
  [decidable_eq o] [decidable_eq p]
variables {R : Type v}

local infix ` ⬝ `:70 := matrix.mul
local postfix `ᵀ` : 1500 := transpose

def to_matrix [has_one R] [has_zero R] (f : pequiv m n) : matrix m n R
| i j := if j ∈ f i then 1 else 0

lemma to_matrix_symm [has_one R] [has_zero R] (f : pequiv m n) : (f.symm.to_matrix : matrix n m R) = f.to_matrixᵀ :=
by ext; simp only [transpose, mem_iff_mem f, to_matrix]; congr

@[simp] lemma to_matrix_refl [has_one R] [has_zero R] : ((pequiv.refl n).to_matrix : matrix n n R) = 1 :=
by ext; simp [to_matrix, one_val]; congr

lemma mul_matrix_apply [semiring R] (f : pequiv m n) (M : matrix n o R) (i j) :
  (f.to_matrix ⬝ M) i j = option.cases_on (f i) 0 (λ fi, M fi j) :=
begin
  dsimp [to_matrix, matrix.mul],
  cases h : f i with fi,
  { simp [h] },
  { rw finset.sum_eq_single fi;
    simp [h, eq_comm] {contextual := tt} }
end

lemma matrix_mul_apply [semiring R] (M : matrix m n R) (f : pequiv n o) (i j) :
  (M ⬝ f.to_matrix) i j = option.cases_on (f.symm j) 0 (λ fj, M i fj) :=
begin
  dsimp [to_matrix, matrix.mul],
  cases h : f.symm j with fj,
  { simp [h, f.eq_some_iff.symm] },
  { conv in (_ ∈ _) { rw ← f.mem_iff_mem },
    rw finset.sum_eq_single fj;
    simp [h, eq_comm] {contextual := tt} }
end

lemma to_matrix_trans [semiring R] (f : pequiv m n) (g : pequiv n o) :
  ((f.trans g).to_matrix : matrix m o R) = f.to_matrix ⬝ g.to_matrix :=
begin
  ext i j,
  rw [mul_matrix_apply],
  dsimp [to_matrix, pequiv.trans],
  cases f i; simp
end

@[simp] lemma to_matrix_bot [has_one R] [has_zero R] :
  ((⊥ : pequiv m n).to_matrix : matrix m n R) = 0 := rfl

lemma to_matrix_injective [zero_ne_one_class R] :
  function.injective (@to_matrix m n _ _ _ _ R _ _) :=
λ f g, not_imp_not.1 begin
  simp only [matrix.ext_iff.symm, to_matrix, pequiv.ext_iff,
    classical.not_forall, exists_imp_distrib],
  assume i hi,
  use i,
  cases hf : f i with fi,
  { cases hg : g i with gi,
    { cc },
    { use gi,
      simp } },
  { use fi,
    simp [hf.symm, ne.symm hi] }
end

lemma swap_to_matrix_eq [ring R] (i j : n) : (equiv.swap i j).to_pequiv.to_matrix =
  (1 : matrix n n R) - (single i i).to_matrix - (single j j).to_matrix + (single i j).to_matrix +
    (single j i).to_matrix :=
begin
  ext,
  dsimp [to_matrix, single, equiv.swap_apply_def, equiv.to_pequiv, one_val],
  split_ifs; simp * at *
end

@[simp] lemma single_mul_single [ring R] (a : m) (b : n) (c : k) :
  ((single a b).to_matrix : matrix _ _ R) ⬝ (single b c).to_matrix = (single a c).to_matrix :=
by rw [← to_matrix_trans, single_trans_single]

lemma single_mul_single_of_ne [ring R] {b₁ b₂ : n} (hb : b₁ ≠ b₂) (a : m) (c : k) :
  ((single a b₁).to_matrix : matrix _ _ R) ⬝ (single b₂ c).to_matrix = 0 :=
by rw [← to_matrix_trans, single_trans_single_of_ne hb, to_matrix_bot]

@[simp] lemma single_mul_single_right [ring R] (a :  m) (b : n) (c : k)
  (M : matrix k l R) : (single a b).to_matrix ⬝ ((single b c).to_matrix ⬝ M) =
  (single a c).to_matrix ⬝ M :=
by rw [← matrix.mul_assoc, single_mul_single]

end pequiv
