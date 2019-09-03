import data.matrix data.rat.basic .misc tactic.fin_cases
import .matrix_pequiv

open matrix fintype finset function

variables {m n : ℕ}

local notation `rvec`:2000 n := matrix (fin 1) (fin n) ℚ
local notation `cvec`:2000 m := matrix (fin m) (fin 1) ℚ

def list.to_matrix (m :ℕ) (n : ℕ) (l : list (list ℚ)) : matrix (fin m) (fin n) ℚ :=
λ i j, (l.nth_le i sorry).nth_le j sorry

local attribute [instance] matrix.ordered_comm_group matrix.decidable_le
open pequiv

lemma cvec_one_lt_iff {a b : cvec 1} : a < b ↔ a 0 0 < b 0 0 :=
begin
  simp only [lt_iff_le_not_le],
  show (∀ i j, a i j ≤ b i j) ∧ (¬ ∀ i j, b i j ≤ a i j) ↔ _,
  simp [unique.forall_iff], refl,
end

instance : discrete_linear_ordered_field (cvec 1) :=
{ mul_nonneg := λ a b ha0 hb0 i j, by simp [matrix.mul];
    exact mul_nonneg (ha0 _ _) (hb0 _ _),
  mul_pos := λ a b ha0 hb0,
    begin
      rw [cvec_one_lt_iff] at *,
      simp [matrix.mul],
      exact mul_pos ha0 hb0
    end,
  le_total := λ a b, (le_total (a 0 0) (b 0 0)).elim
    (λ hab, or.inl $ λ i j, by fin_cases i; fin_cases j; exact hab)
    (λ hba, or.inr $ λ i j, by fin_cases i; fin_cases j; exact hba),
  zero_lt_one := dec_trivial,
  decidable_le := matrix.decidable_le,
  ..matrix.discrete_field,
  ..matrix.ordered_comm_group }

instance : decidable_linear_order (cvec 1) :=
{ ..matrix.discrete_linear_ordered_field }

local infix ` ⬝ `:70 := matrix.mul
local postfix `ᵀ` : 1500 := transpose

lemma cvec_le_iff (a b : cvec n) : a ≤ b ↔
  (∀ i : fin n, (single (0 : fin 1) i).to_matrix ⬝ a ≤ (single 0 i).to_matrix ⬝ b) :=
show (∀ i j, a i j ≤ b i j) ↔
  (∀ i j k, ((single (0 : fin 1) i).to_matrix ⬝ a) j k ≤ ((single 0 i).to_matrix ⬝ b) j k),
begin
  simp only [mul_matrix_apply],
  split,
  { intros h i j k,
    fin_cases j, fin_cases k,
    exact h _ _ },
  { intros h i j,
    fin_cases j,
    exact h i 0 0 }
end

lemma rvec_le_iff (a b : rvec n) : a ≤ b ↔
  (∀ j : fin n, a ⬝ (single j (0 : fin 1)).to_matrix ≤ b ⬝ (single j 0).to_matrix) :=
show (∀ i k, a i k ≤ b i k) ↔
  (∀ j i k, (a ⬝ (single j (0 : fin 1)).to_matrix) i k ≤ (b ⬝ (single j 0).to_matrix) i k),
begin
  simp only [matrix_mul_apply],
  split,
  { intros h i j k,
    fin_cases j, fin_cases k,
    exact h _ _ },
  { intros h i j,
    fin_cases i,
    exact h _ 0 0 }
end

def rvec.to_list {n : ℕ} (x : rvec n) : list ℚ :=
(vector.of_fn (x 0)).1

instance has_repr_fin_fun {n : ℕ} {α : Type*} [has_repr α] : has_repr (fin n → α) :=
⟨λ f, repr (vector.of_fn f).to_list⟩

instance {m n} : has_repr (matrix (fin m) (fin n) ℚ) := has_repr_fin_fun

namespace simplex

open list

def pequiv_of_vector (v : vector (fin n) m) (hv : v.1.nodup) : fin m ≃. fin n :=
{ to_fun := λ i, some $ v.nth i,
  inv_fun := λ j, fin.find (λ i, v.nth i = j),
  inv := λ i j, ⟨λ h, by rw ← fin.find_spec _ h; exact rfl,
    λ h, fin.mem_find_of_unique
      (begin
        rintros ⟨i, him⟩ ⟨j, hjm⟩ h₁ h₂,
        cases v,
        refine fin.eq_of_veq (list.nodup_iff_nth_le_inj.1 hv i j _ _ (h₁.trans h₂.symm));
        simpa [v.2]
      end)
      (option.some_inj.1 h)⟩ }

def nonbasis_vector_of_vector (v : vector (fin n) m) (hv : v.to_list.nodup) :
  {v : vector (fin n) (n - m) // v.to_list.nodup} :=
⟨⟨(fin_range n).diff v.to_list,
  have h : m ≤ n,
    by rw [← list.length_fin_range n, ← v.2];
      exact list.length_le_of_subperm
        (subperm_of_subset_nodup hv (λ _ _, list.mem_fin_range _)),
  begin
    rw [← add_right_inj m, nat.sub_add_cancel h],
    conv in m { rw [← vector.to_list_length v] },
    rw ← length_append,
    conv_rhs { rw ← length_fin_range n },
    exact list.perm_length ((perm_ext
      (nodup_append.2 ⟨nodup_diff (nodup_fin_range _), hv,
        by simp [list.disjoint, mem_diff_iff_of_nodup (nodup_fin_range n), imp_false]⟩)
      (nodup_fin_range _)).2
      (by simp only [list.mem_diff_iff_of_nodup (nodup_fin_range n),
          list.mem_append, mem_fin_range, true_and, iff_true];
        exact λ _, or.symm (decidable.em _))),
  end⟩,
  nodup_diff (nodup_fin_range _)⟩

def pre_nonbasis_of_vector (v : vector (fin n) m) (hv : v.1.nodup) : fin (n - m) ≃. fin n :=
pequiv_of_vector (nonbasis_vector_of_vector v hv).1 (nonbasis_vector_of_vector v hv).2

structure prebasis (m n : ℕ) : Type :=
( basis : fin m ≃. fin n )
( nonbasis : fin (n - m) ≃. fin n )
( basis_trans_basis_symm : basis.trans basis.symm = pequiv.refl (fin m) )
( nonbasis_trans_nonbasis_symm : nonbasis.trans nonbasis.symm = pequiv.refl (fin (n - m)) )
( basis_trans_nonbasis_symm : basis.trans nonbasis.symm = ⊥ )

namespace prebasis
open pequiv

attribute [simp] basis_trans_basis_symm nonbasis_trans_nonbasis_symm basis_trans_nonbasis_symm

lemma is_some_basis (B : prebasis m n) : ∀ (i : fin m), (B.basis i).is_some :=
by rw [← trans_symm_eq_iff_forall_is_some, basis_trans_basis_symm]

lemma is_some_nonbasis (B : prebasis m n) : ∀ (k : fin (n - m)), (B.nonbasis k).is_some :=
by rw [← trans_symm_eq_iff_forall_is_some, nonbasis_trans_nonbasis_symm]

lemma injective_basis (B : prebasis m n) : injective B.basis :=
injective_of_forall_is_some (is_some_basis B)

lemma injective_nonbasis (B : prebasis m n) : injective B.nonbasis :=
injective_of_forall_is_some (is_some_nonbasis B)

def basisg (B : prebasis m n) (r : fin m) : fin n :=
option.get (B.is_some_basis r)

def nonbasisg (B : prebasis m n) (s : fin (n - m)) : fin n :=
option.get (B.is_some_nonbasis s)

lemma injective_basisg (B : prebasis m n) : injective B.basisg :=
λ x y h, by rw [basisg, basisg, ← option.some_inj, option.some_get, option.some_get] at h;
  exact injective_basis B h

lemma injective_nonbasisg (B : prebasis m n) : injective B.nonbasisg :=
λ x y h, by rw [nonbasisg, nonbasisg, ← option.some_inj, option.some_get, option.some_get] at h;
  exact injective_nonbasis B h

local infix ` ♣ `: 70 := pequiv.trans

def swap (B : prebasis m n) (r : fin m) (s : fin (n - m)) : prebasis m n :=
{ basis := B.basis.trans (equiv.swap (B.basisg r) (B.nonbasisg s)).to_pequiv,
  nonbasis := B.nonbasis.trans (equiv.swap (B.basisg r) (B.nonbasisg s)).to_pequiv,
  basis_trans_basis_symm := by rw [symm_trans_rev, ← trans_assoc, trans_assoc B.basis,
      ← equiv.to_pequiv_symm,  ← equiv.to_pequiv_trans];
    simp,
  nonbasis_trans_nonbasis_symm := by rw [symm_trans_rev, ← trans_assoc, trans_assoc B.nonbasis,
      ← equiv.to_pequiv_symm, ← equiv.to_pequiv_trans];
    simp,
  basis_trans_nonbasis_symm := by rw [symm_trans_rev, ← trans_assoc, trans_assoc B.basis,
      ← equiv.to_pequiv_symm, ← equiv.to_pequiv_trans];
    simp }

lemma not_is_some_nonbasis_of_is_some_basis (B : prebasis m n) (j : fin n) :
  (B.basis.symm j).is_some → (B.nonbasis.symm j).is_some → false :=
begin
  rw [option.is_some_iff_exists, option.is_some_iff_exists],
  rintros ⟨i, hi⟩ ⟨k, hk⟩,
  have : B.basis.trans B.nonbasis.symm i = none,
  { rw [B.basis_trans_nonbasis_symm, pequiv.bot_apply] },
  rw [pequiv.trans_eq_none] at this,
  rw [pequiv.eq_some_iff] at hi,
  exact (this j k).resolve_left (not_not.2 hi) hk
end

lemma nonbasis_ne_none_of_basis_eq_none (B : prebasis m n) (j : fin n)
  (hb : B.basis.symm j = none) (hnb : B.nonbasis.symm j = none) : false :=
have hs : card (univ.image B.basis) = m,
  by rw [card_image_of_injective _ (B.injective_basis), card_univ, card_fin],
have ht : card (univ.image B.nonbasis) = (n - m),
  by rw [card_image_of_injective _ (B.injective_nonbasis), card_univ, card_fin],
have hst : disjoint (univ.image B.basis) (univ.image B.nonbasis),
  from finset.disjoint_left.2 begin
    simp only [mem_image, exists_imp_distrib, not_exists],
    assume j i _ hbasis k _ hnonbasis,
    cases option.is_some_iff_exists.1 (is_some_basis B i) with x hi,
    cases option.is_some_iff_exists.1 (is_some_nonbasis B k) with y hk,
    have hxy : x = y,
    { rw [← option.some_inj, ← hk, ← hi, hbasis, hnonbasis] }, subst hxy,
    rw [← eq_some_iff] at hi hk,
    refine not_is_some_nonbasis_of_is_some_basis B x _ _;
    simp [hi, hk]
  end,
have (univ.image B.basis) ∪ (univ.image B.nonbasis) = univ.image (@some (fin n)),
  from eq_of_subset_of_card_le
    begin
      assume i h,
      simp only [finset.mem_image, finset.mem_union] at h,
      rcases h with ⟨j, _, hj⟩ | ⟨k, _, hk⟩,
      { simpa [hj.symm, option.is_some_iff_exists, eq_comm] using is_some_basis B j },
      { simpa [hk.symm, option.is_some_iff_exists, eq_comm] using is_some_nonbasis B k }
    end
    (begin
      rw [card_image_of_injective, card_univ, card_fin, card_disjoint_union hst, hs, ht],
      { rw add_comm,
        exact nat.le_sub_add _ _ },
      { intros _ _ h, injection h }
    end),
begin
  simp only [option.eq_none_iff_forall_not_mem, mem_iff_mem B.basis,
    mem_iff_mem B.nonbasis] at hb hnb,
  have := (finset.ext.1 this (some j)).2 (mem_image_of_mem _ (mem_univ _)),
  simp only [hb, hnb, mem_image, finset.mem_union, option.mem_def.symm] at this, tauto
end

lemma is_some_basis_iff (B : prebasis m n) (j : fin n) :
  (B.basis.symm j).is_some ↔ ¬(B.nonbasis.symm j).is_some :=
⟨not_is_some_nonbasis_of_is_some_basis B j,
  by erw [option.not_is_some_iff_eq_none, ← option.ne_none_iff_is_some, forall_swap];
    exact nonbasis_ne_none_of_basis_eq_none B j⟩

@[simp] lemma nonbasis_basisg_eq_none (B : prebasis m n) (r : fin m) :
  B.nonbasis.symm (B.basisg r) = none :=
option.not_is_some_iff_eq_none.1 ((B.is_some_basis_iff _).1 (is_some_symm_get _ _))

@[simp] lemma basis_nonbasisg_eq_none (B : prebasis m n) (s : fin (n - m)) :
  B.basis.symm (B.nonbasisg s) = none :=
option.not_is_some_iff_eq_none.1 (mt (B.is_some_basis_iff _).1 $ not_not.2 (is_some_symm_get _ _))

@[simp] lemma basisg_mem (B : prebasis m n) (r : fin m) :
  (B.basisg r) ∈ B.basis r :=
option.get_mem _

@[simp] lemma nonbasisg_mem (B : prebasis m n) (s : fin (n - m)) :
  (B.nonbasisg s) ∈ B.nonbasis s :=
option.get_mem _

@[simp] lemma basis_basisg (B : prebasis m n) (r : fin m) : B.basis.symm (B.basisg r) = some r:=
B.basis.mem_iff_mem.2 (basisg_mem _ _)

@[simp] lemma nonbasis_nonbasisg (B : prebasis m n) (s : fin (n - m)) :
  B.nonbasis.symm (B.nonbasisg s) = some s :=
B.nonbasis.mem_iff_mem.2 (nonbasisg_mem _ _)

lemma eq_basisg_or_nonbasisg (B : prebasis m n) (i : fin n) :
  (∃ j, i = B.basisg j) ∨ (∃ j, i = B.nonbasisg j) :=
begin
  dsimp only [basisg, nonbasisg],
  by_cases h : ↥(B.basis.symm i).is_some,
  { cases option.is_some_iff_exists.1 h with j hj,
    exact or.inl ⟨j, by rw [B.basis.eq_some_iff] at hj;
      rw [← option.some_inj, ← hj, option.some_get]⟩ },
  { rw [(@not_iff_comm _ _ (classical.dec _) (classical.dec _)).1 (B.is_some_basis_iff _).symm] at h,
    cases option.is_some_iff_exists.1 h with j hj,
    exact or.inr ⟨j, by rw [B.nonbasis.eq_some_iff] at hj;
      rw [← option.some_inj, ← hj, option.some_get]⟩ }
end

lemma basisg_ne_nonbasisg (B : prebasis m n) (i : fin m) (j : fin (n - m)):
  B.basisg i ≠ B.nonbasisg j :=
λ h, by simpa using congr_arg B.basis.symm h

lemma single_basisg_mul_basis (B : prebasis m n) (i : fin m) :
  ((single (0 : fin 1) (B.basisg i)).to_matrix : matrix _ _ ℚ) ⬝
    B.basis.to_matrixᵀ = (single (0 : fin 1) i).to_matrix :=
by rw [← to_matrix_symm, ← to_matrix_trans, single_trans_of_mem _ (basis_basisg _ _)]

lemma single_basisg_mul_nonbasis (B : prebasis m n) (i : fin m) :
  ((single (0 : fin 1) (B.basisg i)).to_matrix : matrix _ _ ℚ) ⬝
    B.nonbasis.to_matrixᵀ = 0 :=
by rw [← to_matrix_symm, ← to_matrix_trans, single_trans_of_eq_none _ (nonbasis_basisg_eq_none _ _),
  to_matrix_bot]; apply_instance

lemma single_nonbasisg_mul_nonbasis (B : prebasis m n) (k : fin (n - m)) :
  ((single (0 : fin 1) (B.nonbasisg k)).to_matrix : matrix _ _ ℚ) ⬝
    B.nonbasis.to_matrixᵀ = (single (0 : fin 1) k).to_matrix :=
by rw [← to_matrix_symm, ← to_matrix_trans, single_trans_of_mem _ (nonbasis_nonbasisg _ _)]

lemma single_nonbasisg_mul_basis (B : prebasis m n) (k : fin (n - m)) :
  ((single (0 : fin 1) (B.nonbasisg k)).to_matrix : matrix _ _ ℚ) ⬝
    B.basis.to_matrixᵀ = 0 :=
by rw [← to_matrix_symm, ← to_matrix_trans, single_trans_of_eq_none _ (basis_nonbasisg_eq_none _ _),
  to_matrix_bot]; apply_instance

lemma nonbasis_trans_basis_symm (B : prebasis m n) : B.nonbasis.trans B.basis.symm = ⊥ :=
symm_injective $ by rw [symm_trans_rev, symm_symm, basis_trans_nonbasis_symm, symm_bot]

@[simp] lemma nonbasis_mul_basis_transpose (B : prebasis m n) :
  (B.nonbasis.to_matrix : matrix _ _ ℚ) ⬝ B.basis.to_matrixᵀ = 0 :=
by rw [← to_matrix_bot, ← B.nonbasis_trans_basis_symm, to_matrix_trans, to_matrix_symm]

@[simp] lemma basis_mul_nonbasis_transpose (B : prebasis m n) :
  (B.basis.to_matrix : matrix _ _ ℚ) ⬝ B.nonbasis.to_matrixᵀ = 0 :=
by rw [← to_matrix_bot, ← B.basis_trans_nonbasis_symm, to_matrix_trans, to_matrix_symm]

@[simp] lemma nonbasis_mul_nonbasis_transpose (B : prebasis m n) :
  (B.nonbasis.to_matrix : matrix _ _ ℚ) ⬝ B.nonbasis.to_matrixᵀ = 1 :=
by rw [← to_matrix_refl, ← B.nonbasis_trans_nonbasis_symm, to_matrix_trans, to_matrix_symm]

@[simp] lemma basis_mul_basis_transpose (B : prebasis m n) :
  (B.basis.to_matrix : matrix _ _ ℚ) ⬝ B.basis.to_matrixᵀ = 1 :=
by rw [← to_matrix_refl, ← B.basis_trans_basis_symm, to_matrix_trans, to_matrix_symm]

lemma transpose_mul_add_tranpose_mul (B : prebasis m n) :
  (B.basis.to_matrixᵀ ⬝ B.basis.to_matrix : matrix (fin n) (fin n) ℚ) +
  B.nonbasis.to_matrixᵀ ⬝ B.nonbasis.to_matrix  = 1 :=
begin
  ext,
  repeat {rw [← to_matrix_symm, ← to_matrix_trans] },
  simp only [add_val, pequiv.symm_trans, pequiv.to_matrix, one_val,
    pequiv.mem_of_set_iff, set.mem_set_of_eq],
  have := is_some_basis_iff B j,
  split_ifs; tauto
end

lemma swap_basis_eq (B : prebasis m n) (r : fin m) (s : fin (n - m)) :
  (B.swap r s).basis.to_matrix = (B.basis.to_matrix : matrix _ _ ℚ)
  - (single r (B.basisg r)).to_matrix + (single r (B.nonbasisg s)).to_matrix :=
begin
  dsimp [swap],
  rw [to_matrix_trans, to_matrix_swap],
  simp only [matrix.mul_add, sub_eq_add_neg, matrix.mul_one, matrix.mul_neg,
    (to_matrix_trans _ _).symm, trans_single_of_mem _ (basisg_mem B r),
    trans_single_of_eq_none _ (basis_nonbasisg_eq_none B s), to_matrix_bot, neg_zero, add_zero]
end

lemma nonbasis_trans_swap_basis_symm (B : prebasis m n) (r : fin m) (s : fin (n - m)) :
  B.nonbasis.trans (B.swap r s).basis.symm = single s r :=
begin
  rw [swap, symm_trans_rev, ← equiv.to_pequiv_symm, ← equiv.perm.inv_def, equiv.swap_inv],
  ext i j,
  rw [mem_single_iff],
  dsimp [pequiv.trans, equiv.to_pequiv, equiv.swap_apply_def],
  simp only [coe, coe_mk_apply, option.mem_def, option.bind_eq_some'],
  rw [option.mem_def.1 (nonbasisg_mem B i)],
  simp [B.injective_nonbasisg.eq_iff, (B.basisg_ne_nonbasisg _ _).symm],
  split_ifs; simp [*, eq_comm]
end

lemma nonbasis_mul_swap_basis_tranpose (B : prebasis m n) (r : fin m) (s : fin (n - m)) :
  (B.nonbasis.to_matrix : matrix _ _ ℚ) ⬝ (B.swap r s).basis.to_matrixᵀ = (single s r).to_matrix :=
by rw [← nonbasis_trans_swap_basis_symm, to_matrix_trans, to_matrix_symm]

lemma basis_trans_swap_basis_transpose (B : prebasis m n) (r : fin m) (s : fin (n - m)) :
  B.basis.trans (B.swap r s).basis.symm = of_set {i | i ≠ r} :=
begin
  rw [swap, symm_trans_rev, ← equiv.to_pequiv_symm, ← equiv.perm.inv_def, equiv.swap_inv],
  ext i j,
  dsimp [pequiv.trans, equiv.to_pequiv, equiv.swap_apply_def],
  simp only [coe, coe_mk_apply, option.mem_def, option.bind_eq_some'],
  rw [option.mem_def.1 (basisg_mem B i)],
  simp [B.injective_basisg.eq_iff, B.basisg_ne_nonbasisg],
  split_ifs,
  { simp * },
  { simp *; split; intros; simp * at * }
end

lemma swap_basis_transpose_apply_single_of_ne (B : prebasis m n) {r : fin m}
  (s : fin (n - m)) {i : fin m} (hir : i ≠ r) :
  ((B.swap r s).basis.to_matrixᵀ : matrix (fin n) (fin m) ℚ) ⬝ (single i (0 : fin 1)).to_matrix =
  B.basis.to_matrixᵀ ⬝ (single i 0).to_matrix :=
begin
  simp only [swap_basis_eq, sub_eq_add_neg, matrix.mul_add, matrix.mul_neg, matrix.mul_one,
    matrix.add_mul, (to_matrix_trans _ _).symm, (to_matrix_symm _).symm, transpose_add,
    transpose_neg, matrix.neg_mul, symm_trans_rev, trans_assoc],
  rw [trans_single_of_mem _ (basis_basisg _ _), trans_single_of_eq_none, trans_single_of_eq_none,
    to_matrix_bot, neg_zero, add_zero, add_zero];
  {dsimp [single]; simp [*, B.injective_basisg.eq_iff]} <|> apply_instance
end

lemma swap_basis_transpose_apply_single (B : prebasis m n) (r : fin m) (s : fin (n - m)) :
  ((B.swap r s).basis.to_matrixᵀ : matrix (fin n) (fin m) ℚ) ⬝ (single r (0 : fin 1)).to_matrix =
  B.nonbasis.to_matrixᵀ ⬝ (single s (0 : fin 1)).to_matrix :=
begin
  simp only [swap_basis_eq, sub_eq_add_neg, matrix.mul_add, matrix.mul_neg, matrix.mul_one,
    matrix.add_mul, (to_matrix_trans _ _).symm, (to_matrix_symm _).symm, transpose_add,
    transpose_neg, matrix.neg_mul, symm_trans_rev, trans_assoc, symm_single],
  rw [trans_single_of_mem _ (basis_basisg _ _), trans_single_of_mem _ (mem_single _ _),
    trans_single_of_mem _ (mem_single _ _), trans_single_of_mem _ (nonbasis_nonbasisg _ _)],
  simp,
  all_goals {apply_instance}
end

def equiv_aux : prebasis m n ≃ Σ' (basis : fin m ≃. fin n)
  (nonbasis : fin (n - m) ≃. fin n)
  ( basis_trans_basis_symm : basis.trans basis.symm = pequiv.refl (fin m) )
( nonbasis_trans_nonbasis_symm : nonbasis.trans nonbasis.symm = pequiv.refl (fin (n - m)) ),
  basis.trans nonbasis.symm = ⊥ :=
{ to_fun := λ ⟨a, b, c, d, e⟩, ⟨a, b, c, d, e⟩,
  inv_fun := λ ⟨a, b, c, d, e⟩, ⟨a, b, c, d, e⟩,
  left_inv := λ ⟨_, _, _, _, _⟩, rfl,
  right_inv := λ ⟨_, _, _, _, _⟩, rfl }

--instance : fintype (prebasis m n) := sorry

end prebasis

open prebasis

/- By convention `A_bar` and `b_bar` are in tableau form, so definitions may only be correct
  assuming `A ⬝ B.basis.to_matrixᵀ = 1` and `b_bar = 0` -/

def pivot_element (B : prebasis m n) (A_bar : matrix (fin m) (fin n) ℚ) (r : fin m)
  (s : fin (n - m)) : cvec 1 :=
(single 0 r).to_matrix ⬝ A_bar ⬝ B.nonbasis.to_matrixᵀ ⬝ (single s 0).to_matrix

def swap_inverse (B : prebasis m n) (A_bar : matrix (fin m) (fin n) ℚ)
  (r : fin m) (s : fin (n - m)) : matrix (fin m) (fin m) ℚ :=
(1 + (1 - A_bar ⬝ B.nonbasis.to_matrixᵀ ⬝ (single s (0 : fin 1)).to_matrix ⬝
    (single (0 : fin 1) r).to_matrix) ⬝ (single r (0 : fin 1)).to_matrix ⬝
    (pivot_element B A_bar r s)⁻¹ ⬝ (single (0 : fin 1) r).to_matrix)

def ratio (B : prebasis m n) (A_bar : matrix (fin m) (fin n) ℚ) (b_bar : cvec m)
  (r : fin m) (s : fin (n - m)) : cvec 1 :=
(pivot_element B A_bar r s)⁻¹ ⬝ ((single 0 r).to_matrix ⬝ b_bar)

lemma swap_mul_swap_inverse {B : prebasis m n} {A_bar : matrix (fin m) (fin n) ℚ}
  {r : fin m} {s : fin (n - m)} (hA_bar : A_bar ⬝ B.basis.to_matrixᵀ = 1)
  (hpivot : pivot_element B A_bar r s ≠ 0) :
  swap_inverse B A_bar r s ⬝ (A_bar ⬝ (B.swap r s).basis.to_matrixᵀ) = 1 :=
have ((single (0 : fin 1) r).to_matrix ⬝ (single r 0).to_matrix : cvec 1) = 1,
  by rw [← to_matrix_trans]; simp,
begin
  refine mul_single_ext (λ i, _),
  simp only [swap_inverse, matrix.mul_add, matrix.add_mul, sub_eq_add_neg, matrix.neg_mul, matrix.mul_neg,
    matrix.one_mul, matrix.mul_one, matrix.mul_assoc, transpose_add, transpose_neg,
     mul_right_eq_of_mul_eq this, pivot_element],
  rw [pivot_element, matrix.mul_assoc, matrix.mul_assoc] at hpivot,
  by_cases h : i = r,
  { simp only [h, swap_basis_transpose_apply_single, mul_right_eq_of_mul_eq hA_bar,
      one_by_one_inv_mul_cancel hpivot, inv_eq_inverse],
    simp },
  { have : ((single (0 : fin 1) r).to_matrix ⬝ (single i 0).to_matrix : cvec 1) = 0,
    { rw [← to_matrix_trans, single_trans_single_of_ne (ne.symm h), to_matrix_bot] },
    simp [swap_basis_transpose_apply_single_of_ne _ _ h,
      mul_right_eq_of_mul_eq hA_bar, this] }
end

lemma has_left_inverse_swap {B : prebasis m n} {A_bar : matrix (fin m) (fin n) ℚ}
  {r : fin m} {s : fin (n - m)} (hA_bar : A_bar ⬝ B.basis.to_matrixᵀ = 1)
  (hpivot : pivot_element B A_bar r s ≠ 0) :
  (A_bar ⬝ (B.swap r s).basis.to_matrixᵀ).has_left_inverse :=
⟨_, swap_mul_swap_inverse hA_bar hpivot⟩

lemma has_left_inverse_swap_inverse {B : prebasis m n} {A_bar : matrix (fin m) (fin n) ℚ}
  {r : fin m} {s : fin (n - m)} (hA_bar : A_bar ⬝ B.basis.to_matrixᵀ = 1)
  (hpivot : pivot_element B A_bar r s ≠ 0) :
  (swap_inverse B A_bar r s).has_left_inverse :=
has_right_inverse_iff_has_left_inverse.1 ⟨_, swap_mul_swap_inverse hA_bar hpivot⟩

lemma inverse_swap_eq {A_bar : matrix (fin m) (fin n) ℚ} {B : prebasis m n}
  {r : fin m} {s : fin (n - m)} (hA_bar : A_bar ⬝ B.basis.to_matrixᵀ = 1)
  (hpivot : pivot_element B A_bar r s ≠ 0) :
  inverse (A_bar ⬝ (B.swap r s).basis.to_matrixᵀ) = swap_inverse B A_bar r s :=
eq.symm $ eq_inverse_of_mul_eq_one $ by rw [swap_mul_swap_inverse hA_bar hpivot]

def adjust (B : prebasis m n) (A_bar : matrix (fin m) (fin n) ℚ) (b_bar : cvec m)
  (s : fin (n - m)) (a : cvec 1) : cvec n :=
B.basis.to_matrixᵀ ⬝ b_bar + (B.nonbasis.to_matrixᵀ -
  B.basis.to_matrixᵀ ⬝ A_bar ⬝ B.nonbasis.to_matrixᵀ) ⬝ (single s 0).to_matrix ⬝ a

lemma adjust_is_solution {B : prebasis m n} {A_bar : matrix (fin m) (fin n) ℚ} (b_bar : cvec m)
  (s : fin (n - m)) (a : cvec 1) (hA_bar : A_bar ⬝ B.basis.to_matrixᵀ = 1) :
  A_bar ⬝ adjust B A_bar b_bar s a = b_bar :=
by simp [matrix.mul_assoc, matrix.mul_add, adjust, matrix.add_mul, mul_right_eq_of_mul_eq hA_bar]

lemma single_pivot_mul_adjust (B : prebasis m n) (A_bar : matrix (fin m) (fin n) ℚ) (b_bar : cvec m)
  (s : fin (n - m)) (a : cvec 1) :
  (single 0 s).to_matrix ⬝ B.nonbasis.to_matrix ⬝ adjust B A_bar b_bar s a = a :=
by simp [matrix.mul_assoc, matrix.add_mul, matrix.mul_add, adjust,
  mul_right_eq_of_mul_eq (nonbasis_mul_basis_transpose B),
  mul_right_eq_of_mul_eq (nonbasis_mul_nonbasis_transpose B)]

lemma basis_mul_adjust (B : prebasis m n) (A_bar : matrix (fin m) (fin n) ℚ) (b_bar : cvec m)
  (s : fin (n - m)) (a : cvec 1) : B.basis.to_matrix ⬝ adjust B A_bar b_bar s a = b_bar -
  A_bar ⬝ B.nonbasis.to_matrixᵀ ⬝ (single s 0).to_matrix ⬝ a :=
by simp [matrix.mul_assoc, matrix.add_mul, matrix.mul_add, adjust,
  mul_right_eq_of_mul_eq (basis_mul_basis_transpose B),
  mul_right_eq_of_mul_eq (basis_mul_nonbasis_transpose B)]

lemma nonbasis_mul_adjust (B : prebasis m n) (A_bar : matrix (fin m) (fin n) ℚ)
  (b_bar : cvec m) (s : fin (n - m)) (a : cvec 1) :
  B.nonbasis.to_matrix ⬝ adjust B A_bar b_bar s a = to_matrix (single s 0) ⬝ a :=
by simp [matrix.mul_assoc, matrix.add_mul, matrix.mul_add, adjust,
  mul_right_eq_of_mul_eq (nonbasis_mul_basis_transpose B),
  mul_right_eq_of_mul_eq (nonbasis_mul_nonbasis_transpose B)]

lemma adjust_nonneg_iff {B : prebasis m n} {A_bar : matrix (fin m) (fin n) ℚ}
  {b_bar : cvec m} {s : fin (n - m)} {a : cvec 1} (ha : 0 ≤ a) (hb : 0 ≤ b_bar) :
  0 ≤ adjust B A_bar b_bar s a ↔
    ∀ (i : fin m), 0 < pivot_element B A_bar i s → a ≤ ratio B A_bar b_bar i s :=
have ∀ i : fin m, (single (0 : fin 1) (B.basisg i)).to_matrix ⬝ 0 ≤
  (single 0 (B.basisg i)).to_matrix ⬝ (B.basis.to_matrixᵀ ⬝ b_bar +
    (B.nonbasis.to_matrixᵀ - B.basis.to_matrixᵀ ⬝ A_bar ⬝ B.nonbasis.to_matrixᵀ) ⬝
    to_matrix (single s 0) ⬝ a) ↔
    0 < pivot_element B A_bar i s → a ≤ ratio B A_bar b_bar i s,
  begin
    assume i,
    simp only [matrix.mul_zero, ratio, matrix.mul_add, matrix.add_mul, matrix.mul_assoc,
      sub_eq_add_neg, matrix.mul_neg, matrix.neg_mul, matrix.mul_assoc,
      mul_right_eq_of_mul_eq (single_basisg_mul_basis B i),
      mul_right_eq_of_mul_eq (single_basisg_mul_nonbasis B i), matrix.zero_mul, zero_add],
    rw [← sub_eq_add_neg, sub_nonneg],
    simp only [pivot_element, matrix.mul_assoc],
    cases classical.em (0 < (single (0 : fin 1) i).to_matrix ⬝
      (A_bar ⬝ (B.nonbasis.to_matrixᵀ ⬝ (single s (0 : fin 1)).to_matrix))) with hpos hpos,
    { rw [← matrix.mul_eq_mul, ← mul_comm, ← div_eq_mul_inv, le_div_iff hpos, mul_comm,
        matrix.mul_eq_mul],
      simp [matrix.mul_assoc, hpos] },
    { simp only [hpos, forall_prop_of_false, iff_true, not_false_iff],
      simp only [(matrix.mul_assoc _ _ _).symm, (matrix.mul_eq_mul _ _).symm] at *,
      intros,
      refine le_trans (mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hpos) ha) _,
      rw [cvec_le_iff] at hb,
      simpa using hb i },
  end,
begin
  rw [adjust, cvec_le_iff],
  split,
  { assume h i,
    rw [← this],
    exact h (B.basisg i) },
  { assume h j,
    rcases eq_basisg_or_nonbasisg B j with ⟨i, hi⟩ | ⟨k, hk⟩,
    { rw [hi, this], exact h _ },
    { simp only [hk, matrix.mul_assoc,
        mul_right_eq_of_mul_eq (single_nonbasisg_mul_basis _ _),
        matrix.mul_add, matrix.add_mul, matrix.mul_neg,
        mul_right_eq_of_mul_eq (single_nonbasisg_mul_nonbasis _ _),
        add_zero, matrix.neg_mul, matrix.zero_mul,
        zero_add, matrix.mul_zero, sub_eq_add_neg, neg_zero],
      by_cases hks : k = s,
      { simpa [hks] },
      { rw [mul_right_eq_of_mul_eq (single_mul_single_of_ne hks _ _), matrix.zero_mul],
        exact le_refl _ } } }
end

def reduced_cost (B : prebasis m n) (A_bar : matrix (fin m) (fin n) ℚ) (c : rvec n) :
  rvec (n - m) :=
c ⬝ (B.nonbasis.to_matrixᵀ - B.basis.to_matrixᵀ ⬝ A_bar ⬝ B.nonbasis.to_matrixᵀ)

noncomputable def solution_of_basis (B : prebasis m n) (A : matrix (fin m) (fin n) ℚ) (b : cvec m) :
  cvec n :=
B.basis.to_matrixᵀ ⬝ inverse (A ⬝ B.basis.to_matrixᵀ) ⬝ b

lemma solution_of_basis_is_solution {A : matrix (fin m) (fin n) ℚ} {B : prebasis m n}
  (b : cvec m) (hA : (A ⬝ B.basis.to_matrixᵀ).has_left_inverse) :
  A ⬝ solution_of_basis B A b = b :=
by rw [solution_of_basis, ← matrix.mul_assoc, ← matrix.mul_assoc,
    mul_inverse (has_right_inverse_iff_has_left_inverse.2 hA), matrix.one_mul]

noncomputable def objective_function_of_basis (A : matrix (fin m) (fin n) ℚ) (B : prebasis m n)
  (b : cvec m) (c : rvec n) : cvec 1 :=
c ⬝ solution_of_basis B A b

/-- For proving `solution_of_basis_eq_adjust`, it suffices to prove they are equal after
  left multiplication by `A_bar` and after left multiplication by `B.nonbasis.to_matrix`.
  This lemma helps prove that. -/
lemma basis_transpose_add_nonbasis_transpose_mul_nonbasis {B : prebasis m n}
  {A_bar : matrix (fin m) (fin n) ℚ} (hA_bar : A_bar ⬝ B.basis.to_matrixᵀ = 1) :
  (B.basis.to_matrixᵀ ⬝ A_bar + B.nonbasis.to_matrixᵀ ⬝ B.nonbasis.to_matrix) ⬝
  (1 - B.basis.to_matrixᵀ ⬝ A_bar ⬝ B.nonbasis.to_matrixᵀ ⬝ B.nonbasis.to_matrix) = 1 :=
by rw [← transpose_mul_add_tranpose_mul B];
  simp [matrix.mul_add, matrix.add_mul, matrix.mul_neg, matrix.mul_assoc,
    mul_right_eq_of_mul_eq hA_bar,
    mul_right_eq_of_mul_eq (nonbasis_mul_basis_transpose _),
    mul_right_eq_of_mul_eq (nonbasis_mul_nonbasis_transpose _)]

lemma solution_of_basis_eq_adjust {B : prebasis m n} {A_bar : matrix (fin m) (fin n) ℚ}
  (b_bar : cvec m) {r : fin m} {s : fin (n - m)} (hA_bar : A_bar ⬝ B.basis.to_matrixᵀ = 1)
  (hpivot : pivot_element B A_bar r s ≠ 0) :
  solution_of_basis (B.swap r s) A_bar b_bar = adjust B A_bar b_bar s (ratio B A_bar b_bar r s) :=
/- It suffices to prove they are equal after left multiplication by `A_bar` and by
`B.nonbasis.to_matrix` -/
suffices A_bar ⬝ (B.swap r s).basis.to_matrixᵀ
    ⬝ inverse (A_bar ⬝ (B.swap r s).basis.to_matrixᵀ) ⬝ b_bar =
    A_bar ⬝ adjust B A_bar b_bar s (ratio B A_bar b_bar r s) ∧
    B.nonbasis.to_matrix ⬝ (B.swap r s).basis.to_matrixᵀ
    ⬝ inverse (A_bar ⬝ (B.swap r s).basis.to_matrixᵀ) ⬝ b_bar =
    B.nonbasis.to_matrix ⬝ adjust B A_bar b_bar s (ratio B A_bar b_bar r s),
  begin
    rw [solution_of_basis, ← matrix.mul_left_inj ⟨_, mul_eq_one_comm.1
      (basis_transpose_add_nonbasis_transpose_mul_nonbasis hA_bar)⟩, matrix.add_mul,
      matrix.add_mul],
    simp only [matrix.mul_assoc] at *,
    rw [this.1, this.2]
  end,
{ left := by rw [adjust_is_solution _ _ _ hA_bar, matrix.mul_inverse
    (has_right_inverse_iff_has_left_inverse.2 (has_left_inverse_swap hA_bar hpivot)),
    matrix.one_mul],
  right :=
/- This `have` would be unnecessary with a powerful `assoc_rw` tactic -/
    have (single s r).to_matrix ⬝ (A_bar ⬝ (B.nonbasis.to_matrixᵀ ⬝ ((single s (0 : fin 1)).to_matrix
      ⬝ ((single 0 r).to_matrix ⬝ ((single r 0).to_matrix ⬝ (inverse (pivot_element B A_bar r s)
      ⬝ ((single 0 r).to_matrix ⬝ b_bar))))))) = (single s (0 : fin 1)).to_matrix
      ⬝ (single 0 r).to_matrix ⬝ b_bar,
      begin
        rw [pivot_element, mul_right_eq_of_mul_eq (single_mul_single (0 : fin 1) r (0 : fin 1)),
          single_subsingleton_eq_refl, to_matrix_refl, matrix.one_mul,
          ← single_mul_single s (0 : fin 1) r],
        simp only [(matrix.mul_assoc _ _ _).symm],
        simp only [(single s (0 : fin 1)).to_matrix.mul_assoc],
        rw [one_by_one_mul_inv_cancel, matrix.one_mul],
        { simpa [pivot.matrix.mul_assoc] using hpivot }
      end,
    begin
      simp only [adjust, matrix.mul_add, zero_add, sub_eq_add_neg, matrix.neg_mul,
        mul_right_eq_of_mul_eq (nonbasis_mul_basis_transpose _), matrix.zero_mul,
        nonbasis_mul_swap_basis_tranpose, matrix.mul_assoc, matrix.add_mul, matrix.mul_neg,
        mul_right_eq_of_mul_eq (nonbasis_mul_nonbasis_transpose _), matrix.one_mul, neg_zero,
        add_zero, inverse_swap_eq hA_bar hpivot, swap_inverse, ratio, this, inv_eq_inverse],
      simp
    end }

lemma cvec_eq_basis_add_nonbasis (B : prebasis m n) (x : cvec n) :
  x = B.basis.to_matrixᵀ ⬝ B.basis.to_matrix ⬝ x + B.nonbasis.to_matrixᵀ ⬝ B.nonbasis.to_matrix ⬝ x :=
by simp only [(matrix.mul_assoc _ _ _).symm, (matrix.add_mul _ _ _).symm,
  B.transpose_mul_add_tranpose_mul, matrix.one_mul]

lemma objective_function_eq {B : prebasis m n}
  {A_bar : matrix (fin m) (fin n) ℚ}  {b_bar : cvec m} {c : rvec n} {x : cvec n}
  (hAx : A_bar ⬝ x = b_bar) (hA_bar : A_bar ⬝ B.basis.to_matrixᵀ = 1) :
  c ⬝ x = c ⬝ B.basis.to_matrixᵀ ⬝ b_bar +
  reduced_cost B A_bar c ⬝ B.nonbasis.to_matrix ⬝ x :=
have B.basis.to_matrix ⬝ x = b_bar - A_bar ⬝ B.nonbasis.to_matrixᵀ
    ⬝ B.nonbasis.to_matrix ⬝ x,
  by rw [eq_sub_iff_add_eq, ← (B.basis.to_matrix).one_mul, ← hA_bar,
    matrix.mul_assoc, matrix.mul_assoc, matrix.mul_assoc, matrix.mul_assoc,
    ← matrix.mul_add, ← matrix.mul_assoc, ← matrix.mul_assoc, ← matrix.add_mul,
    transpose_mul_add_tranpose_mul, matrix.one_mul, hAx],
begin
  conv_lhs {rw [cvec_eq_basis_add_nonbasis B x, matrix.mul_assoc, this]},
  simp [matrix.mul_add, matrix.mul_assoc, matrix.add_mul, reduced_cost]
end

lemma objective_function_swap_eq {B : prebasis m n} {A_bar : matrix (fin m) (fin n) ℚ}
  (b_bar : cvec m) (c : rvec n) {r : fin m} {s : fin (n - m)}
  (hA_bar : A_bar ⬝ B.basis.to_matrixᵀ = 1) (hpivot : pivot_element B A_bar r s ≠ 0) :
  objective_function_of_basis A_bar (B.swap r s) b_bar c =
  objective_function_of_basis A_bar B b_bar c +
  reduced_cost B A_bar c ⬝ (single s (0 : fin 1)).to_matrix ⬝ ratio B A_bar b_bar r s :=
have h₁ : A_bar ⬝ (B.basis.to_matrixᵀ ⬝ b_bar) = b_bar,
  by rw [← matrix.mul_assoc, hA_bar, matrix.one_mul],
have h₂ : (A_bar ⬝ (to_matrix ((swap B r s).basis))ᵀ).has_left_inverse,
  from has_left_inverse_swap hA_bar hpivot,
begin
  rw [objective_function_of_basis, objective_function_eq
    (solution_of_basis_is_solution _ h₂) hA_bar,
    solution_of_basis_eq_adjust _ hA_bar hpivot, objective_function_of_basis,
    solution_of_basis, hA_bar, inverse_one, matrix.mul_one, c.mul_assoc,
    matrix.mul_assoc, matrix.mul_assoc],
  congr' 2,
  rw [adjust],
  simp only [matrix.mul_add, matrix.mul_assoc, sub_eq_add_neg,
    matrix.add_mul, matrix.neg_mul, matrix.mul_neg,
    mul_right_eq_of_mul_eq (nonbasis_mul_basis_transpose _),
    mul_right_eq_of_mul_eq (nonbasis_mul_nonbasis_transpose _)],
  simp
end

lemma swap_nonneg_iff {B : prebasis m n} {A_bar : matrix (fin m) (fin n) ℚ} (b_bar : cvec m)
  {r : fin m} {s : fin (n - m)} (hA_bar : A_bar ⬝ B.basis.to_matrixᵀ = 1)
  (hpivot : 0 < pivot_element B A_bar r s) (h0b : 0 ≤ b_bar) :
  0 ≤ solution_of_basis (B.swap r s) A_bar b_bar ↔
  (∀ i : fin m, 0 < pivot_element B A_bar i s →
    ratio B A_bar b_bar r s ≤ ratio B A_bar b_bar i s) :=
begin
  rw [solution_of_basis_eq_adjust _ hA_bar (ne_of_lt hpivot).symm, adjust_nonneg_iff _ h0b, ratio],
  rw cvec_le_iff at h0b,
  exact mul_nonneg (inv_nonneg.2 (le_of_lt hpivot)) (by simpa using h0b r)
end

lemma swap_inverse_mul_nonneg {B : prebasis m n} {A_bar : matrix (fin m) (fin n) ℚ} (b_bar : cvec m)
  {r : fin m} {s : fin (n - m)} (hA_bar : A_bar ⬝ B.basis.to_matrixᵀ = 1)
  (hpivot : 0 < pivot_element B A_bar r s) (h0b : 0 ≤ b_bar) :
  (∀ i : fin m, 0 < pivot_element B A_bar i s →
    ratio B A_bar b_bar r s ≤ ratio B A_bar b_bar i s) →
  0 ≤ swap_inverse B A_bar r s ⬝ b_bar:=
begin
  rw [← swap_nonneg_iff b_bar hA_bar hpivot h0b, solution_of_basis,
    inverse_swap_eq hA_bar (ne_of_lt hpivot).symm],
  assume hratio,
  rw [cvec_le_iff] at *,
  assume i,
  simpa [mul_right_eq_of_mul_eq (single_basisg_mul_basis _ _), matrix.mul_assoc]
    using hratio ((B.swap r s).basisg i)
end

def is_unbounded (A : matrix (fin m) (fin n) ℚ) (b : cvec m) (c : rvec n) : Prop :=
∀ q : cvec 1, ∃ x, 0 ≤ x ∧ A ⬝ x = b ∧ q ≤ c ⬝ x

def is_optimal (A : matrix (fin m) (fin n) ℚ) (b : cvec m) (c : rvec n) (x : cvec n) : Prop :=
0 ≤ x ∧ A ⬝ x = b ∧ ∀ y, 0 ≤ y → A ⬝ y = b → c ⬝ y ≤ c ⬝ x

def is_optimal_basis (B : prebasis m n) (A : matrix (fin m) (fin n) ℚ)
  (b : cvec m) (c : rvec n) : Prop :=
(A ⬝ B.basis.to_matrixᵀ).has_left_inverse ∧
  is_optimal A b c (B.basis.to_matrixᵀ ⬝ inverse (A ⬝ B.basis.to_matrixᵀ) ⬝ b)

lemma is_unbounded_of_pivot_element_nonpos {B : prebasis m n}
  {A_bar : matrix (fin m) (fin n) ℚ} (b_bar : cvec m) (c : rvec n)
  {s : fin (n - m)} (hA_bar : A_bar ⬝ B.basis.to_matrixᵀ = 1)
  (h0b : 0 ≤ b_bar) (hs : reduced_cost B A_bar c ⬝ (single s (0 : fin 1)).to_matrix > 0)
  (h : ∀ r, pivot_element B A_bar r s ≤ 0) : is_unbounded A_bar b_bar c :=
begin
  assume q,
  let a := (reduced_cost B A_bar c ⬝ (single s (0 : fin 1)).to_matrix)⁻¹ ⬝
    (q - c ⬝ ((to_matrix (B.basis))ᵀ ⬝ b_bar)),
  use adjust B A_bar b_bar s (max 0 a),
  simp only [adjust_is_solution b_bar _ _ hA_bar, true_and, eq_self_iff_true],
  simp only [objective_function_eq (adjust_is_solution b_bar _ _ hA_bar) hA_bar]
    {single_pass := tt},
  simp only [nonbasis_mul_adjust, matrix.mul_assoc],
  split,
  { rw adjust_nonneg_iff (le_max_left _ _) h0b,
    assume i hi,
    exact absurd hi (not_lt_of_ge (h _)), },
  { cases le_total a 0 with ha0 ha0,
    { rw [max_eq_left ha0],
      simp only [a, (mul_eq_mul _ _).symm] at ha0,
      rw [mul_comm, ← div_eq_mul_inv, div_le_iff hs, _root_.zero_mul, sub_nonpos] at ha0,
      simpa },
    { simp only [max_eq_right ha0],
      rw [← (reduced_cost _ _ _).mul_assoc],
      dsimp only [a],
      rw [← matrix.mul_assoc (reduced_cost _ _ _ ⬝ _ ), ← mul_eq_mul,
        ← mul_eq_mul, mul_inv_cancel (ne_of_lt hs).symm, one_mul],
      simp [le_refl] } }
end

lemma is_optimal_basis_of_reduced_cost_nonpos {B : prebasis m n} {A_bar : matrix (fin m) (fin n) ℚ}
  (b_bar : cvec m) (c : rvec n) (hA_bar : A_bar ⬝ B.basis.to_matrixᵀ = 1)
  (h0b : 0 ≤ b_bar) (hs : reduced_cost B A_bar c ≤ 0) :
  is_optimal_basis B A_bar b_bar c :=
begin
  rw [is_optimal_basis, hA_bar, inverse_one, matrix.mul_one],
  refine ⟨⟨1, matrix.one_mul _⟩, matrix.mul_nonneg (by rw [← to_matrix_symm]; exact pequiv_nonneg _) h0b,
    by rw [← matrix.mul_assoc, hA_bar, matrix.one_mul], _⟩,
  assume x h0x hAx,
  rw [objective_function_eq hAx hA_bar, ← le_sub_iff_add_le', ← matrix.mul_assoc, sub_self],
  exact matrix.mul_nonpos_of_nonpos_of_nonneg
    (matrix.mul_nonpos_of_nonpos_of_nonneg hs (pequiv_nonneg _)) h0x
end

def choose_pivot_column (B : prebasis m n) (A_bar : matrix (fin m) (fin n) ℚ) (b_bar : cvec m)
  (c : rvec n) : option (fin (n - m)) :=
(fin.find (λ j : fin n, ∃ h : (B.nonbasis.symm j).is_some,
  0 < reduced_cost B A_bar c ⬝ (single (option.get h) (0 : fin 1)).to_matrix)).bind
    B.nonbasis.symm

lemma choose_pivot_column_eq_none (B : prebasis m n) (A_bar : matrix (fin m) (fin n) ℚ)
  (b_bar : cvec m) (c : rvec n) (hA_bar : A_bar ⬝ B.basis.to_matrixᵀ = 1)
  (h0b : 0 ≤ b_bar)
  (h : choose_pivot_column B A_bar b_bar c = none) :
  is_optimal_basis B A_bar b_bar c :=
is_optimal_basis_of_reduced_cost_nonpos _ _ hA_bar h0b $
  begin
    rw [choose_pivot_column, option.bind_eq_none] at h,
    have : ∀ j, j ∉ fin.find (λ j : fin n, ∃ h : (B.nonbasis.symm j).is_some,
      0 < reduced_cost B A_bar c ⬝ (single (option.get h) (0 : fin 1)).to_matrix),
    { assume j hj,
      cases option.is_some_iff_exists.1 (fin.find_spec _ hj).fst with s hs,
      exact h s j hj hs },
    rw [← option.eq_none_iff_forall_not_mem, fin.find_eq_none_iff] at this,
    rw [rvec_le_iff],
    assume j,
    refine le_of_not_gt (λ h0j, _),
    have hj : ↥(B.nonbasis.symm (B.nonbasisg j)).is_some,
      from option.is_some_iff_exists.2 ⟨j, nonbasis_nonbasisg _ _⟩,
    have hjg : j = option.get hj, { rw [← option.some_inj, option.some_get, nonbasis_nonbasisg] },
    exact this (B.nonbasisg j) ⟨hj, by { rw ← hjg, rwa [matrix.zero_mul] at h0j} ⟩
  end

lemma choose_pivot_column_spec (B : prebasis m n) (A_bar : matrix (fin m) (fin n) ℚ)
  (b_bar : cvec m) (c : rvec n) (s : fin (n - m)) (hA_bar : A_bar ⬝ B.basis.to_matrixᵀ = 1)
  (h0b : 0 ≤ b_bar) (h : choose_pivot_column B A_bar b_bar c = some s) :
  0 < reduced_cost B A_bar c ⬝ (single s (0 : fin 1)).to_matrix :=
begin
  rw [choose_pivot_column, option.bind_eq_some'] at h,
  cases h with j hj,
  have := fin.find_spec _ hj.1,
  have hs : s = option.get this.fst,
  { rw [← option.some_inj, option.some_get, hj.2] },
  exact hs.symm ▸ this.snd
end

set_option class.instance_max_depth 60

def choose_pivot_row (B : prebasis m n) (A_bar : matrix (fin m) (fin n) ℚ) (b_bar : cvec m)
  (c : rvec n) (s : fin (n - m)) : option (fin m) :=
(fin.find (λ j : fin n, ∃ h : (B.basis.symm j).is_some,
  0 < pivot_element B A_bar (option.get h) s ∧
  ∀ i : fin m, ((0 : cvec 1) < pivot_element B A_bar i s) →
    ratio B A_bar b_bar (option.get h) s ≤ ratio B A_bar b_bar i s)).bind B.basis.symm

lemma choose_pivot_row_spec (B : prebasis m n) (A_bar : matrix (fin m) (fin n) ℚ)
  (b_bar : cvec m) (c : rvec n) (r : fin m) (s : fin (n - m))
  (hr : r ∈ choose_pivot_row B A_bar b_bar c s) :
  0 < pivot_element B A_bar r s ∧
  ∀ i : fin m, 0 < pivot_element B A_bar i s →
    ratio B A_bar b_bar r s ≤ ratio B A_bar b_bar i s :=
begin
  rw [choose_pivot_row, option.mem_def, option.bind_eq_some'] at hr,
  cases hr with j hj,
  have hrj : r = option.get (fin.find_spec _ hj.1).fst,
  { rw [← option.some_inj, option.some_get, ← hj.2] },
  rw hrj,
  exact (fin.find_spec _ hj.1).snd
end

lemma choose_pivot_row_eq_none (B : prebasis m n) (A_bar : matrix (fin m) (fin n) ℚ)
  (b_bar : cvec m) (c : rvec n) (r : fin m) (s : fin (n - m))
  (hn : choose_pivot_row B A_bar b_bar c s = none) :
  pivot_element B A_bar r s ≤ 0 :=
le_of_not_gt $ λ hpivot, begin
  rw [choose_pivot_row, option.bind_eq_none] at hn,
  cases @finset.min_of_mem _ _
    ((univ.filter (λ j, 0 < pivot_element B A_bar j s)).image
      (λ i, ratio B A_bar b_bar i s)) (ratio B A_bar b_bar r s)
      (mem_image_of_mem _ (finset.mem_filter.2 ⟨mem_univ _, hpivot⟩)) with q hq,
  rcases mem_image.1 (mem_of_min hq) with ⟨i, hip, hiq⟩,
  subst hiq,
  have : ∀ j : fin n, j ∉ fin.find (λ j : fin n, ∃ h : (B.basis.symm j).is_some,
    0 < pivot_element B A_bar (option.get h) s ∧
    ∀ i : fin m, 0 < pivot_element B A_bar i s →
      ratio B A_bar b_bar (option.get h) s ≤ ratio B A_bar b_bar i s),
  { assume j hj,
    cases option.is_some_iff_exists.1 (fin.find_spec _ hj).fst with r hr,
    exact hn _ _ hj hr },
  rw [← option.eq_none_iff_forall_not_mem, fin.find_eq_none_iff] at this,
  have hi : ↥(B.basis.symm (B.basisg i)).is_some,
    from option.is_some_iff_exists.2 ⟨i, basis_basisg _ _⟩,
  have hig : i = option.get hi, { rw [← option.some_inj, option.some_get, basis_basisg] },
  exact this (B.basisg i) ⟨(option.is_some_iff_exists.2 ⟨i, basis_basisg _ _⟩),
    begin
      rw [← hig],
      clear_aux_decl,
      refine ⟨by simpa using hip, _⟩,
      assume j hj,
      refine min_le_of_mem (mem_image.2 ⟨j, _⟩) hq,
      simp [hj]
    end⟩
end

lemma is_unbounded_of_choose_pivot_row_eq_none (B : prebasis m n) (A_bar : matrix (fin m) (fin n) ℚ)
  (b_bar : cvec m) (c : rvec n) (s : fin (n - m))
  (hA_bar : A_bar ⬝ B.basis.to_matrixᵀ = 1) (h0b : 0 ≤ b_bar)
  (hs : 0 < reduced_cost B A_bar c ⬝ (single s (0 : fin 1)).to_matrix)
  (hn : choose_pivot_row B A_bar b_bar c s = none) : is_unbounded A_bar b_bar c :=
is_unbounded_of_pivot_element_nonpos _ _ hA_bar h0b hs
  (λ _, choose_pivot_row_eq_none _ _ _ _ _ _ hn)

lemma is_unbounded_swap {B : prebasis m n} {A_bar : matrix (fin m) (fin n) ℚ} {b_bar : cvec m}
  {c : rvec n} {r : fin m} {s : fin (n - m)} (hA_bar : A_bar ⬝ B.basis.to_matrixᵀ = 1)
  (hpivot : pivot_element B A_bar r s ≠ 0) :
  is_unbounded (swap_inverse B A_bar r s ⬝ A_bar) (swap_inverse B A_bar r s ⬝ b_bar) c →
  is_unbounded A_bar b_bar c :=
by simp only [is_unbounded, matrix.mul_assoc, matrix.mul_left_inj
  (has_left_inverse_swap_inverse hA_bar hpivot), imp_self]

lemma is_optimal_basis_swap {B  : prebasis m n} {A_bar : matrix (fin m) (fin n) ℚ}
  {b_bar : cvec m} {c : rvec n} (S : matrix (fin m) (fin m) ℚ)
  (hS : S.has_left_inverse) (h : is_optimal_basis B (S ⬝ A_bar) (S ⬝ b_bar) c) :
  is_optimal_basis B A_bar b_bar c :=
begin
  rw [is_optimal_basis, matrix.mul_assoc, ← has_left_inverse_mul hS] at h,
  simp only [is_optimal_basis, is_optimal, matrix.mul_assoc, matrix.mul_left_inj
    hS, h.1, inverse_one, matrix.one_mul,
    matrix.mul_one, matrix.mul_left_inj
    (inverse_has_left_inverse (has_right_inverse_iff_has_left_inverse.2 hS)),
    inverse_mul hS, inverse_one, mul_right_eq_of_mul_eq (inverse_mul hS),
    matrix.one_mul, matrix.mul_one, mul_inverse_rev hS h.1, *] at *,
  tauto,
end

axiom wf (p : Prop) : p

def simplex : Π (B : prebasis m n) (A_bar : matrix (fin m) (fin n) ℚ)
  (b_bar : cvec m) (c : rvec n) (hA_bar : A_bar ⬝ B.basis.to_matrixᵀ = 1)
  (h0b : 0 ≤ b_bar),
  { o : option (Σ (B : prebasis m n) (A_bar : matrix (fin m) (fin n) ℚ), cvec m) //
    option.cases_on o (is_unbounded A_bar b_bar c)
      (λ P, is_optimal_basis P.1 A_bar b_bar c) }
| B A_bar b_bar c hA_bar h0b :=
  match choose_pivot_column B A_bar b_bar c,
    (λ s, choose_pivot_column_spec B A_bar b_bar c s hA_bar h0b),
      choose_pivot_column_eq_none B A_bar b_bar c hA_bar h0b with
  | none,   _, hn := ⟨some ⟨B, A_bar, b_bar⟩, hn rfl⟩
  | some s, hs, _ :=
    match choose_pivot_row B A_bar b_bar c s,
      (λ r, choose_pivot_row_spec B A_bar b_bar c r s),
      is_unbounded_of_choose_pivot_row_eq_none B A_bar b_bar c s hA_bar h0b (hs _ rfl) with
    | none,     _, hnone  := ⟨none, hnone rfl⟩
    | (some r), hr, _ := let S := swap_inverse B A_bar r s in
      have wf : prebasis.sizeof m n (swap B r s) < prebasis.sizeof m n B, from wf _,
      let o := simplex (B.swap r s) (S ⬝ A_bar) (S ⬝ b_bar) c
        (by rw [matrix.mul_assoc, swap_mul_swap_inverse hA_bar (ne_of_lt (hr r rfl).1).symm])
        (swap_inverse_mul_nonneg b_bar hA_bar (hr _ rfl).1 h0b (hr _ rfl).2) in
      ⟨o.1, option.cases_on o.1 (is_unbounded_swap hA_bar (ne_of_lt (hr r rfl).1).symm)
        (λ P, is_optimal_basis_swap S (has_left_inverse_swap_inverse hA_bar
          (ne_of_lt (hr r rfl).1).symm))
        o.2⟩
    end
  end

#print axioms simplex.simplex

def rel (A : matrix (fin m) (fin n) ℚ) (b : cvec m) (c : rvec n) :
  prebasis m n → prebasis m n → Prop :=
tc (λ B C, ∃ hs : (choose_pivot_column B
    (inverse (A ⬝ B.basis.to_matrixᵀ) ⬝ A) (inverse (A ⬝ B.basis.to_matrixᵀ) ⬝ b) c).is_some,
  ∃ hr : (choose_pivot_row B
    (inverse (A ⬝ B.basis.to_matrixᵀ) ⬝ A) (inverse (A ⬝ B.basis.to_matrixᵀ) ⬝ b)
      c (option.get hs)).is_some,
  C = B.swap (option.get hr) (option.get hs))

#eval inverse (list.to_matrix 3 3
  [[1,2,3],[0,1,5],[0,0,1]])

-- def ex.A := list.to_matrix 2 5 [[1,1,0,1,0],
--                                 [0,1,-1,0,1]]

-- def ex.b : cvec 2 := (λ i _, (list.nth_le [8,0] i sorry))

-- def ex.c : rvec 5 := λ _ i, (list.nth_le [1, 1, 1, 0, 0] i sorry)

-- def ex.B : prebasis 2 5 :=
--   ⟨pequiv_of_vector ⟨[3, 4], rfl⟩ dec_trivial,
--     pre_nonbasis_of_vector ⟨[3, 4], rfl⟩ dec_trivial, sorry, sorry, sorry⟩

-- #eval ex.A ⬝ ex.B.basis.to_matrixᵀ

-- #eval (simplex ex.B ex.A ex.b ex.c dec_trivial dec_trivial).1.is_some

def ex.A := list.to_matrix 3 7 [[1/4, - 8, -  1, 9, 1, 0, 0],
                                [1/2, -12, -1/2, 3, 0, 1, 0],
                                [  0,   0,    1, 0, 0, 0, 1]]

def ex.b : cvec 3 := (λ i _, list.nth_le [0,0,1] i sorry)
--#eval ex.b
def ex.c : rvec 7 := λ _ i, (list.nth_le [3/4, -20, 1/2, -6, 0, 0, 0] i sorry)
--#eval ex.c
def ex.B : prebasis 3 7 :=
  ⟨pequiv_of_vector ⟨[4, 5, 6], rfl⟩ dec_trivial,
    pre_nonbasis_of_vector ⟨[4,5,6], rfl⟩ dec_trivial, sorry, sorry, sorry⟩

--#eval (simplex ex.B ex.A ex.b ex.c dec_trivial dec_trivial).1.is_some

#eval (find_optimal_solution_from_starting_basis ex.A ex.c ex.b ex.B)
--set_option trace.fun_info true
#eval (is_optimal_bool ex.A ex.c ex.b ex.B)

-- (some [[2064/445]])
-- (some [[6401/1895]])
#eval (is_feasible_basis ex.A ex.c ex.b ex.B : bool)
-- #eval (show matrix _ _ ℚ, from minor ex.A id ex.B.read) *
--   _root_.inverse (show matrix _ _ ℚ, from minor ex.A id ex.B.read )
-- #eval ((1 : cvec 1) - (minor ex.c id ex.B.read) ⬝
--   _root_.inverse (minor ex.A id ex.B.read) ⬝
--   (minor ex.A id ex.NB.read))

#eval finishing_basis ex.A ex.c ex.b ex.B

#eval test ex.A ex.c ex.b ex.B

#eval (let x : cvec 4 := λ i _, list.nth_le [0, 80/89, 62/89, 196/89] i sorry in
  let A := list.to_matrix 3 4 [[12, -1, 1, 1],
                     [1, 1.45, 1, 0],
                     [1, 2, 0, 1]]
                     in A ⬝ x
 )
