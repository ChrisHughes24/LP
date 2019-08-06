/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import data.matrix data.pequiv data.rat.basic

namespace pequiv
open matrix

universes u v

variables {k l m n o : Type u}
variables [fintype k] [fintype l] [fintype m] [fintype n]
variables [decidable_eq k] [decidable_eq l] [decidable_eq m] [decidable_eq n]
  [decidable_eq o]
variables {α : Type v}

local infix ` ⬝ `:70 := matrix.mul
local postfix `ᵀ` : 1500 := transpose

def to_matrix [has_one α] [has_zero α] (f : pequiv m n) : matrix m n α
| i j := if j ∈ f i then 1 else 0

lemma to_matrix_symm [has_one α] [has_zero α] (f : pequiv m n) :
  (f.symm.to_matrix : matrix n m α) = f.to_matrixᵀ :=
by ext; simp only [transpose, mem_iff_mem f, to_matrix]; congr

@[simp] lemma to_matrix_refl [has_one α] [has_zero α] :
  ((pequiv.refl n).to_matrix : matrix n n α) = 1 :=
by ext; simp [to_matrix, one_val]; congr

lemma mul_matrix_apply [semiring α] (f : pequiv l m) (M : matrix m n α) (i j) :
  (f.to_matrix ⬝ M) i j = option.cases_on (f i) 0 (λ fi, M fi j) :=
begin
  dsimp [to_matrix, matrix.mul],
  cases h : f i with fi,
  { simp [h] },
  { rw finset.sum_eq_single fi;
    simp [h, eq_comm] {contextual := tt} }
end

lemma matrix_mul_apply [semiring α] (M : matrix l m α) (f : pequiv m n) (i j) :
  (M ⬝ f.to_matrix) i j = option.cases_on (f.symm j) 0 (λ fj, M i fj) :=
begin
  dsimp [to_matrix, matrix.mul],
  cases h : f.symm j with fj,
  { simp [h, f.eq_some_iff.symm] },
  { conv in (_ ∈ _) { rw ← f.mem_iff_mem },
    rw finset.sum_eq_single fj;
    simp [h, eq_comm] {contextual := tt} }
end

lemma to_matrix_trans [semiring α] (f : pequiv l m) (g : pequiv m n) :
  ((f.trans g).to_matrix : matrix l n α) = f.to_matrix ⬝ g.to_matrix :=
begin
  ext i j,
  rw [mul_matrix_apply],
  dsimp [to_matrix, pequiv.trans],
  cases f i; simp
end

@[simp] lemma to_matrix_bot [has_one α] [has_zero α] :
  ((⊥ : pequiv m n).to_matrix : matrix m n α) = 0 := rfl

lemma to_matrix_injective [zero_ne_one_class α] :
  function.injective (@to_matrix m n _ _ _ _ α _ _) :=
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

lemma to_matrix_swap [ring α] (i j : n) : (equiv.swap i j).to_pequiv.to_matrix =
  (1 : matrix n n α) - (single i i).to_matrix - (single j j).to_matrix + (single i j).to_matrix +
    (single j i).to_matrix :=
begin
  ext,
  dsimp [to_matrix, single, equiv.swap_apply_def, equiv.to_pequiv, one_val],
  split_ifs; simp * at *
end

@[simp] lemma single_mul_single [semiring α] (a : m) (b : n) (c : k) :
  ((single a b).to_matrix : matrix _ _ α) ⬝ (single b c).to_matrix = (single a c).to_matrix :=
by rw [← to_matrix_trans, single_trans_single]

lemma single_mul_single_of_ne [semiring α] {b₁ b₂ : n} (hb : b₁ ≠ b₂) (a : m) (c : k) :
  ((single a b₁).to_matrix : matrix _ _ α) ⬝ (single b₂ c).to_matrix = 0 :=
by rw [← to_matrix_trans, single_trans_single_of_ne hb, to_matrix_bot]

@[simp] lemma single_mul_single_right [semiring α] (a :  m) (b : n) (c : k)
  (M : matrix k l α) : (single a b).to_matrix ⬝ ((single b c).to_matrix ⬝ M) =
  (single a c).to_matrix ⬝ M :=
by rw [← matrix.mul_assoc, single_mul_single]

@[simp] lemma single_val [has_zero α] [has_one α] (a : m) (b : n) :
  (single a b).to_matrix a b = 1 := if_pos (if_pos rfl)

end pequiv
