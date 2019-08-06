import data.matrix data.rat.basic tactic.fin_cases .misc
import .matrix_pequiv

open matrix fintype finset function pequiv

variables {m n : ℕ}

local notation `rvec`:2000 n := matrix (fin 1) (fin n) ℚ
local notation `cvec`:2000 m := matrix (fin m) (fin 1) ℚ
local infix ` ⬝ `:70 := matrix.mul
local postfix `ᵀ` : 1500 := transpose
local attribute [instance] matrix.partial_order
local attribute [instance, priority 0] algebra.has_scalar

structure prebasis (m n : ℕ) : Type :=
( row : fin m ≃. fin (m + n) )
( col : fin n ≃. fin (m + n) )
( row_trans_row_symm : row.trans row.symm = pequiv.refl (fin m) )
( col_trans_col_symm : col.trans col.symm = pequiv.refl (fin n) )
( row_trans_col_symm : row.trans col.symm = ⊥ )

namespace prebasis

attribute [simp] row_trans_row_symm col_trans_col_symm row_trans_col_symm

lemma is_some_row (B : prebasis m n) : ∀ (i : fin m), (B.row i).is_some :=
by rw [← trans_symm_eq_iff_forall_is_some, row_trans_row_symm]

lemma is_some_col (B : prebasis m n) : ∀ (k : fin n), (B.col k).is_some :=
by rw [← trans_symm_eq_iff_forall_is_some, col_trans_col_symm]

lemma injective_row (B : prebasis m n) : injective B.row :=
injective_of_forall_is_some (is_some_row B)

lemma injective_col (B : prebasis m n) : injective B.col :=
injective_of_forall_is_some (is_some_col B)

def rowg (B : prebasis m n) (r : fin m) : fin (m + n) :=
option.get (B.is_some_row r)

def colg (B : prebasis m n) (s : fin n) : fin (m + n) :=
option.get (B.is_some_col s)

lemma injective_rowg (B : prebasis m n) : injective B.rowg :=
λ x y h, by rw [rowg, rowg, ← option.some_inj, option.some_get, option.some_get] at h;
  exact injective_row B h

lemma injective_colg (B : prebasis m n) : injective B.colg :=
λ x y h, by rw [colg, colg, ← option.some_inj, option.some_get, option.some_get] at h;
  exact injective_col B h

local infix ` ♣ `: 70 := pequiv.trans

def swap (B : prebasis m n) (r : fin m) (s : fin n) : prebasis m n :=
{ row := B.row.trans (equiv.swap (B.rowg r) (B.colg s)).to_pequiv,
  col := B.col.trans (equiv.swap (B.rowg r) (B.colg s)).to_pequiv,
  row_trans_row_symm := by rw [symm_trans_rev, ← trans_assoc, trans_assoc B.row,
      ← equiv.to_pequiv_symm,  ← equiv.to_pequiv_trans];
    simp,
  col_trans_col_symm := by rw [symm_trans_rev, ← trans_assoc, trans_assoc B.col,
      ← equiv.to_pequiv_symm, ← equiv.to_pequiv_trans];
    simp,
  row_trans_col_symm := by rw [symm_trans_rev, ← trans_assoc, trans_assoc B.row,
      ← equiv.to_pequiv_symm, ← equiv.to_pequiv_trans];
    simp }

@[simp] lemma swap_trans_swap {α : Type*} [decidable_eq α] (a b : α) :
  (equiv.swap a b).trans (equiv.swap b a) = equiv.refl _ :=
  sorry
--set_option pp.proofs true

lemma not_is_some_col_of_is_some_row (B : prebasis m n) (j : fin (m + n)) :
  (B.row.symm j).is_some → (B.col.symm j).is_some → false :=
begin
  rw [option.is_some_iff_exists, option.is_some_iff_exists],
  rintros ⟨i, hi⟩ ⟨k, hk⟩,
  have : B.row.trans B.col.symm i = none,
  { rw [B.row_trans_col_symm, pequiv.bot_apply] },
  rw [pequiv.trans_eq_none] at this,
  rw [pequiv.eq_some_iff] at hi,
  exact (this j k).resolve_left (not_not.2 hi) hk
end

lemma col_ne_none_of_row_eq_none (B : prebasis m n) (j : fin (m + n))
  (hb : B.row.symm j = none) (hnb : B.col.symm j = none) : false :=
have hs : card (univ.image B.row) = m,
  by rw [card_image_of_injective _ (B.injective_row), card_univ, card_fin],
have ht : card (univ.image B.col) = n,
  by rw [card_image_of_injective _ (B.injective_col), card_univ, card_fin],
have hst : disjoint (univ.image B.row) (univ.image B.col),
  from finset.disjoint_left.2 begin
    simp only [mem_image, exists_imp_distrib, not_exists],
    assume j i _ hrow k _ hcol,
    cases option.is_some_iff_exists.1 (is_some_row B i) with x hi,
    cases option.is_some_iff_exists.1 (is_some_col B k) with y hk,
    have hxy : x = y,
    { rw [← option.some_inj, ← hk, ← hi, hrow, hcol] }, subst hxy,
    rw [← eq_some_iff] at hi hk,
    refine not_is_some_col_of_is_some_row B x _ _;
    simp [hi, hk]
  end,
have (univ.image B.row) ∪ (univ.image B.col) = univ.image (@some (fin (m + n))),
  from eq_of_subset_of_card_le
    begin
      assume i h,
      simp only [finset.mem_image, finset.mem_union] at h,
      rcases h with ⟨j, _, hj⟩ | ⟨k, _, hk⟩,
      { simpa [hj.symm, option.is_some_iff_exists, eq_comm] using is_some_row B j },
      { simpa [hk.symm, option.is_some_iff_exists, eq_comm] using is_some_col B k }
    end
    (begin
      rw [card_image_of_injective, card_univ, card_fin, card_disjoint_union hst, hs, ht],
      exact λ _ _, option.some_inj.1,
    end),
begin
  simp only [option.eq_none_iff_forall_not_mem, mem_iff_mem B.row,
    mem_iff_mem B.col] at hb hnb,
  have := (finset.ext.1 this (some j)).2 (mem_image_of_mem _ (mem_univ _)),
  simp only [hb, hnb, mem_image, finset.mem_union, option.mem_def.symm] at this, tauto
end

lemma is_some_row_iff (B : prebasis m n) (j : fin (m + n)) :
  (B.row.symm j).is_some ↔ ¬(B.col.symm j).is_some :=
⟨not_is_some_col_of_is_some_row B j,
  by erw [option.not_is_some_iff_eq_none, ← option.ne_none_iff_is_some, forall_swap];
    exact col_ne_none_of_row_eq_none B j⟩

@[simp] lemma col_rowg_eq_none (B : prebasis m n) (r : fin m) :
  B.col.symm (B.rowg r) = none :=
option.not_is_some_iff_eq_none.1 ((B.is_some_row_iff _).1 (is_some_symm_get _ _))

@[simp] lemma row_colg_eq_none (B : prebasis m n) (s : fin n) :
  B.row.symm (B.colg s) = none :=
option.not_is_some_iff_eq_none.1 (mt (B.is_some_row_iff _).1 $ not_not.2 (is_some_symm_get _ _))

@[simp] lemma rowg_mem (B : prebasis m n) (r : fin m) : (B.rowg r) ∈ B.row r :=
option.get_mem _

lemma row_eq_some_rowg (B : prebasis m n) (r : fin m) : B.row r = some (B.rowg r) :=
rowg_mem _ _

@[simp] lemma colg_mem (B : prebasis m n) (s : fin n) : (B.colg s) ∈ B.col s :=
option.get_mem _

lemma col_eq_some_colg (B : prebasis m n) (s : fin n) : B.col s = some (B.colg s) :=
colg_mem _ _

@[simp] lemma row_rowg (B : prebasis m n) (r : fin m) : B.row.symm (B.rowg r) = some r :=
B.row.mem_iff_mem.2 (rowg_mem _ _)

@[simp] lemma col_colg (B : prebasis m n) (s : fin n) : B.col.symm (B.colg s) = some s :=
B.col.mem_iff_mem.2 (colg_mem _ _)

lemma eq_rowg_or_colg (B : prebasis m n) (i : fin (m + n)) :
  (∃ j, i = B.rowg j) ∨ (∃ j, i = B.colg j) :=
begin
  dsimp only [rowg, colg],
  by_cases h : ↥(B.row.symm i).is_some,
  { cases option.is_some_iff_exists.1 h with j hj,
    exact or.inl ⟨j, by rw [B.row.eq_some_iff] at hj;
      rw [← option.some_inj, ← hj, option.some_get]⟩ },
  { rw [(@not_iff_comm _ _ (classical.dec _) (classical.dec _)).1 (B.is_some_row_iff _).symm] at h,
    cases option.is_some_iff_exists.1 h with j hj,
    exact or.inr ⟨j, by rw [B.col.eq_some_iff] at hj;
      rw [← option.some_inj, ← hj, option.some_get]⟩ }
end

lemma rowg_ne_colg (B : prebasis m n) (i : fin m) (j : fin n) : B.rowg i ≠ B.colg j :=
λ h, by simpa using congr_arg B.row.symm h

@[simp] lemma option.get_inj {α : Type*} : Π {a b : option α} {ha : a.is_some} {hb : b.is_some},
  option.get ha = option.get hb ↔ a = b
| (some a) (some b) _ _ := by rw [option.get_some, option.get_some, option.some_inj]

@[extensionality] lemma ext {B C : prebasis m n} (h : ∀ i, B.rowg i = C.rowg i)
  (h₂ : ∀ j, B.colg j = C.colg j) : B = C :=
begin
  cases B, cases C,
  simp [rowg, colg, function.funext_iff, pequiv.ext_iff] at *,
  tauto
end

@[simp] lemma single_rowg_mul_row (B : prebasis m n) (i : fin m) :
  ((single (0 : fin 1) (B.rowg i)).to_matrix : matrix _ _ ℚ) ⬝
    B.row.to_matrixᵀ = (single (0 : fin 1) i).to_matrix :=
by rw [← to_matrix_symm, ← to_matrix_trans, single_trans_of_mem _ (row_rowg _ _)]

@[simp] lemma single_rowg_mul_col (B : prebasis m n) (i : fin m) :
  ((single (0 : fin 1) (B.rowg i)).to_matrix : matrix _ _ ℚ) ⬝
    B.col.to_matrixᵀ = 0 :=
by rw [← to_matrix_symm, ← to_matrix_trans, single_trans_of_eq_none _ (col_rowg_eq_none _ _),
  to_matrix_bot]; apply_instance

@[simp] lemma single_colg_mul_col (B : prebasis m n) (k : fin n) :
  ((single (0 : fin 1) (B.colg k)).to_matrix : matrix _ _ ℚ) ⬝
    B.col.to_matrixᵀ = (single (0 : fin 1) k).to_matrix :=
by rw [← to_matrix_symm, ← to_matrix_trans, single_trans_of_mem _ (col_colg _ _)]

lemma single_colg_mul_row (B : prebasis m n) (k : fin n) :
  ((single (0 : fin 1) (B.colg k)).to_matrix : matrix _ _ ℚ) ⬝
    B.row.to_matrixᵀ = 0 :=
by rw [← to_matrix_symm, ← to_matrix_trans, single_trans_of_eq_none _ (row_colg_eq_none _ _),
  to_matrix_bot]; apply_instance

lemma col_trans_row_symm (B : prebasis m n) : B.col.trans B.row.symm = ⊥ :=
symm_injective $ by rw [symm_trans_rev, symm_symm, row_trans_col_symm, symm_bot]

@[simp] lemma col_mul_row_transpose (B : prebasis m n) :
  (B.col.to_matrix : matrix _ _ ℚ) ⬝ B.row.to_matrixᵀ = 0 :=
by rw [← to_matrix_bot, ← B.col_trans_row_symm, to_matrix_trans, to_matrix_symm]

@[simp] lemma row_mul_col_transpose (B : prebasis m n) :
  (B.row.to_matrix : matrix _ _ ℚ) ⬝ B.col.to_matrixᵀ = 0 :=
by rw [← to_matrix_bot, ← B.row_trans_col_symm, to_matrix_trans, to_matrix_symm]

@[simp] lemma col_mul_col_transpose (B : prebasis m n) :
  (B.col.to_matrix : matrix _ _ ℚ) ⬝ B.col.to_matrixᵀ = 1 :=
by rw [← to_matrix_refl, ← B.col_trans_col_symm, to_matrix_trans, to_matrix_symm]

@[simp] lemma row_mul_row_transpose (B : prebasis m n) :
  (B.row.to_matrix : matrix _ _ ℚ) ⬝ B.row.to_matrixᵀ = 1 :=
by rw [← to_matrix_refl, ← B.row_trans_row_symm, to_matrix_trans, to_matrix_symm]

lemma transpose_mul_add_transpose_mul (B : prebasis m n) :
  (B.row.to_matrixᵀ ⬝ B.row.to_matrix : matrix _ _ ℚ) +
  B.col.to_matrixᵀ ⬝ B.col.to_matrix  = 1 :=
begin
  ext,
  repeat {rw [← to_matrix_symm, ← to_matrix_trans] },
  simp only [add_val, pequiv.symm_trans, pequiv.to_matrix, one_val,
    pequiv.mem_of_set_iff, set.mem_set_of_eq],
  have := is_some_row_iff B j,
  split_ifs; tauto
end

lemma swap_row_eq (B : prebasis m n) (r : fin m) (s : fin n) :
  (B.swap r s).row.to_matrix = (B.row.to_matrix : matrix _ _ ℚ)
  - (single r (B.rowg r)).to_matrix + (single r (B.colg s)).to_matrix :=
begin
  dsimp [swap],
  rw [to_matrix_trans, to_matrix_swap],
  simp only [matrix.mul_add, sub_eq_add_neg, matrix.mul_one, matrix.mul_neg,
    (to_matrix_trans _ _).symm, trans_single_of_mem _ (rowg_mem B r),
    trans_single_of_eq_none _ (row_colg_eq_none B s), to_matrix_bot, neg_zero, add_zero]
end

lemma swap_col_eq (B : prebasis m n) (r : fin m) (s : fin n) :
  (B.swap r s).col.to_matrix = (B.col.to_matrix : matrix _ _ ℚ)
  - (single s (B.colg s)).to_matrix + (single s (B.rowg r)).to_matrix :=
begin
  dsimp [swap],
  rw [to_matrix_trans, to_matrix_swap],
  simp only [matrix.mul_add, sub_eq_add_neg, matrix.mul_one, matrix.mul_neg,
    (to_matrix_trans _ _).symm, trans_single_of_mem _ (colg_mem B s),
    trans_single_of_eq_none _ (col_rowg_eq_none B r), to_matrix_bot, neg_zero, add_zero]
end

@[simp] lemma rowg_swap (B : prebasis m n) (r : fin m) (s : fin n) :
  (B.swap r s).rowg r = B.colg s :=
option.some_inj.1 begin
  dsimp [swap, rowg, colg, pequiv.trans],
  rw [option.some_get, option.some_get],
  conv in (B.row r) { rw row_eq_some_rowg },
  dsimp [equiv.to_pequiv, equiv.swap_apply_def, rowg],
  simp,
end

@[simp] lemma colg_swap (B : prebasis m n) (r : fin m) (s : fin n) :
  (B.swap r s).colg s = B.rowg r :=
option.some_inj.1 begin
  dsimp [swap, rowg, colg, pequiv.trans],
  rw [option.some_get, option.some_get],
  conv in (B.col s) { rw col_eq_some_colg },
  dsimp [equiv.to_pequiv, equiv.swap_apply_def, colg],
  rw [if_neg, if_pos rfl, option.some_get],
  exact (rowg_ne_colg _ _ _).symm
end

lemma rowg_swap_of_ne (B : prebasis m n) {i r : fin m} {s : fin n} (h : i ≠ r) :
  (B.swap r s).rowg i = B.rowg i :=
option.some_inj.1 begin
  dsimp [swap, rowg, colg, pequiv.trans],
  rw [option.some_get, option.bind_eq_some'],
  use [B.rowg i, row_eq_some_rowg _ _],
  dsimp [equiv.to_pequiv, equiv.swap_apply_def, option.get_some],
  rw [← colg, ← rowg, if_neg (rowg_ne_colg B i s), if_neg
    (mt B.injective_rowg.eq_iff.1 h), rowg]
end

lemma colg_swap_of_ne (B : prebasis m n) {r : fin m} {j s : fin n} (h : j ≠ s) :
  (B.swap r s).colg j = B.colg j :=
option.some_inj.1 begin
  dsimp [swap, rowg, colg, pequiv.trans],
  rw [option.some_get, option.bind_eq_some'],
  use [B.colg j, col_eq_some_colg _ _],
  dsimp [equiv.to_pequiv, equiv.swap_apply_def, option.get_some],
  rw [← colg, ← rowg, if_neg (rowg_ne_colg B r j).symm, if_neg
    (mt B.injective_colg.eq_iff.1 h), colg]
end

lemma rowg_swap' (B : prebasis m n) (i r : fin m) (s : fin n) :
  (B.swap r s).rowg i = if i = r then B.colg s else B.rowg i :=
if hir : i = r then by simp [hir]
  else by rw [if_neg hir, rowg_swap_of_ne _ hir]

lemma colg_swap' (B : prebasis m n) (r : fin m) (j s : fin n) :
  (B.swap r s).colg j = if j = s then B.rowg r else B.colg j :=
if hjs : j = s then by simp [hjs]
  else by rw [if_neg hjs, colg_swap_of_ne _ hjs]

@[simp] lemma swap_swap (B : prebasis m n) (r : fin m) (s : fin n) :
  (B.swap r s).swap r s = B :=
by ext; intros; simp [rowg_swap', colg_swap']; split_ifs; cc

@[simp] lemma col_trans_swap_row_symm (B : prebasis m n) (r : fin m) (s : fin n) :
  B.col.trans (B.swap r s).row.symm = single s r :=
begin
  rw [swap, symm_trans_rev, ← equiv.to_pequiv_symm, ← equiv.perm.inv_def, equiv.swap_inv],
  ext i j,
  rw [mem_single_iff],
  dsimp [pequiv.trans, equiv.to_pequiv, equiv.swap_apply_def],
  simp only [coe, coe_mk_apply, option.mem_def, option.bind_eq_some'],
  rw [option.mem_def.1 (colg_mem B i)],
  simp [B.injective_colg.eq_iff, (B.rowg_ne_colg _ _).symm],
  split_ifs; simp [*, eq_comm]
end

@[simp] lemma col_mul_swap_row_tranpose (B : prebasis m n) (r : fin m) (s : fin n) :
  (B.col.to_matrix : matrix _ _ ℚ) ⬝ (B.swap r s).row.to_matrixᵀ = (single s r).to_matrix :=
by rw [← col_trans_swap_row_symm, to_matrix_trans, to_matrix_symm]

lemma row_trans_swap_row_transpose (B : prebasis m n) (r : fin m) (s : fin n) :
  B.row.trans (B.swap r s).row.symm = of_set {i | i ≠ r} :=
begin
  rw [swap, symm_trans_rev, ← equiv.to_pequiv_symm, ← equiv.perm.inv_def, equiv.swap_inv],
  ext i j,
  dsimp [pequiv.trans, equiv.to_pequiv, equiv.swap_apply_def],
  simp only [coe, coe_mk_apply, option.mem_def, option.bind_eq_some'],
  rw [option.mem_def.1 (rowg_mem B i)],
  simp [B.injective_rowg.eq_iff, B.rowg_ne_colg],
  split_ifs,
  { simp * },
  { simp *; split; intros; simp * at * }
end

lemma swap_row_transpose_mul_single_of_ne (B : prebasis m n) {r : fin m}
  (s : fin n) {i : fin m} (hir : i ≠ r) :
  ((B.swap r s).row.to_matrixᵀ : matrix _ _ ℚ) ⬝ (single i (0 : fin 1)).to_matrix =
  B.row.to_matrixᵀ ⬝ (single i 0).to_matrix :=
begin
  simp only [swap_row_eq, sub_eq_add_neg, matrix.mul_add, matrix.mul_neg, matrix.mul_one,
    matrix.add_mul, (to_matrix_trans _ _).symm, (to_matrix_symm _).symm, transpose_add,
    transpose_neg, matrix.neg_mul, symm_trans_rev, trans_assoc],
  rw [trans_single_of_mem _ (row_rowg _ _), trans_single_of_eq_none, trans_single_of_eq_none,
    to_matrix_bot, neg_zero, add_zero, add_zero];
  {dsimp [single]; simp [*, B.injective_rowg.eq_iff]} <|> apply_instance
end

@[simp] lemma swap_row_transpose_mul_single (B : prebasis m n) (r : fin m) (s : fin n) :
  ((B.swap r s).row.to_matrixᵀ : matrix _ _ ℚ) ⬝ (single r (0 : fin 1)).to_matrix =
  B.col.to_matrixᵀ ⬝ (single s (0 : fin 1)).to_matrix :=
begin
  simp only [swap_row_eq, sub_eq_add_neg, matrix.mul_add, matrix.mul_neg, matrix.mul_one,
    matrix.add_mul, (to_matrix_trans _ _).symm, (to_matrix_symm _).symm, transpose_add,
    transpose_neg, matrix.neg_mul, symm_trans_rev, trans_assoc, symm_single],
  rw [trans_single_of_mem _ (row_rowg _ _), trans_single_of_mem _ (mem_single _ _),
    trans_single_of_mem _ (mem_single _ _), trans_single_of_mem _ (col_colg _ _)],
  simp,
  all_goals {apply_instance}
end

def equiv_aux : prebasis m n ≃ Σ' (row : fin m ≃. fin (m + n))
  (col : fin n ≃. fin (m + n))
  ( row_trans_row_symm : row.trans row.symm = pequiv.refl (fin m) )
( col_trans_col_symm : col.trans col.symm = pequiv.refl (fin n) ),
  row.trans col.symm = ⊥ :=
{ to_fun := λ ⟨a, b, c, d, e⟩, ⟨a, b, c, d, e⟩,
  inv_fun := λ ⟨a, b, c, d, e⟩, ⟨a, b, c, d, e⟩,
  left_inv := λ ⟨_, _, _, _, _⟩, rfl,
  right_inv := λ ⟨_, _, _, _, _⟩, rfl }

end prebasis

structure tableau (m n : ℕ) :=
(to_matrix : matrix (fin m) (fin n) ℚ)
(offset : cvec m)
(to_prebasis : prebasis m n)
(restricted : finset (fin (m + n)))

namespace tableau
open prebasis

section predicates
variable (T : tableau m n)

def flat : set (cvec (m + n)) := { x | T.to_prebasis.row.to_matrix ⬝ x =
  T.to_matrix ⬝ T.to_prebasis.col.to_matrix ⬝ x + T.offset }

def sol_set : set (cvec (m + n)) :=
  flat T ∩ { x | ∀ i, i ∈ T.restricted → 0 ≤ x i 0 }

def is_unbounded (i : fin (m + n)) : Prop :=
  ∀ q : ℚ, ∃ (x : cvec (m + n)), x ∈ sol_set T ∧ q ≤ x i 0

def is_maximised (x : cvec (m + n)) (i : fin (m + n)) : Prop :=
∀ y : cvec (m + n), y ∈ sol_set T → y i 0 ≤ x i 0

/- Is this equivalent to `∀ (x : cvec (m + n)), x ∈ flat T → x i 0 = x j 0`? -/
def equal (i j : fin (m + n)) : Prop :=
∀ (x : cvec (m + n)), x ∈ sol_set T → x i 0 = x j 0

def of_col (T : tableau m n) (c : cvec n) : cvec (m + n) :=
T.to_prebasis.col.to_matrixᵀ ⬝ c + T.to_prebasis.row.to_matrixᵀ ⬝
  (T.to_matrix ⬝ c + T.offset)

def feasible : Prop :=
∀ i, T.to_prebasis.rowg i ∈ T.restricted → 0 ≤ T.offset i 0

def pivot (r : fin m) (s : fin n) : tableau m n :=
let p := (T.to_matrix r s)⁻¹ in
{ to_matrix := λ i j,
    if i = r
      then if j = s
        then p
        else -T.to_matrix r j * p
      else if j = s
        then T.to_matrix i s * p
        else T.to_matrix i j - T.to_matrix i s * T.to_matrix r j * p,
  to_prebasis := T.to_prebasis.swap r s,
  offset := λ i k,
    if i = r
      then -T.offset r k * p
      else T.offset i k - T.to_matrix i s * T.offset r k * p,
  restricted := T.restricted  }

end predicates

section predicate_lemmas
variable (T : tableau m n)

lemma mem_flat_iff {x : cvec (m + n)} : x ∈ T.flat ↔
  ∀ i, x (T.to_prebasis.rowg i) 0 = univ.sum
    (λ j : fin n, T.to_matrix i j * x (T.to_prebasis.colg j) 0) +
  T.offset i 0 :=
have hx : x ∈ T.flat ↔ ∀ i, (T.to_prebasis.row.to_matrix ⬝ x) i 0 =
    (T.to_matrix ⬝ T.to_prebasis.col.to_matrix ⬝ x + T.offset) i 0,
  by rw [flat, set.mem_set_of_eq, matrix.ext_iff.symm, forall_swap,
      unique.forall_iff];
    refl,
begin
  rw hx,
  refine forall_congr (λ i, _),
  rw [mul_matrix_apply, add_val, row_eq_some_rowg, matrix.mul_assoc, matrix.mul],
  conv in (T.to_matrix _ _ * (T.to_prebasis.col.to_matrix ⬝ x) _ _)
  { rw [mul_matrix_apply, col_eq_some_colg] },
end

lemma of_col_mem_flat (T : tableau m n) (c : cvec n) : T.of_col c ∈ T.flat :=
by simp [matrix.mul_assoc, matrix.mul_add, of_col, flat,
    mul_right_eq_of_mul_eq (row_mul_col_transpose _),
    mul_right_eq_of_mul_eq (row_mul_row_transpose _),
    mul_right_eq_of_mul_eq (col_mul_col_transpose _),
    mul_right_eq_of_mul_eq (col_mul_row_transpose _)]

@[simp] lemma col_mul_of_col (T : tableau m n) (c : cvec n) :
  T.to_prebasis.col.to_matrix ⬝ of_col T c = c :=
by simp [matrix.mul_assoc, matrix.mul_add, of_col, flat,
    mul_right_eq_of_mul_eq (row_mul_col_transpose _),
    mul_right_eq_of_mul_eq (row_mul_row_transpose _),
    mul_right_eq_of_mul_eq (col_mul_col_transpose _),
    mul_right_eq_of_mul_eq (col_mul_row_transpose _)]

@[simp] lemma row_mul_of_col (T : tableau m n) (c : cvec n) :
  T.to_prebasis.row.to_matrix ⬝ of_col T c = T.to_matrix ⬝ c + T.offset :=
by simp [matrix.mul_assoc, matrix.mul_add, of_col, flat,
    mul_right_eq_of_mul_eq (row_mul_col_transpose _),
    mul_right_eq_of_mul_eq (row_mul_row_transpose _),
    mul_right_eq_of_mul_eq (col_mul_col_transpose _),
    mul_right_eq_of_mul_eq (col_mul_row_transpose _)]

@[simp] lemma of_col_colg (T : tableau m n) (c : cvec n) (j : fin n) :
  of_col T c (T.to_prebasis.colg j) = c j :=
funext $ λ k,
  calc of_col T c (T.to_prebasis.colg j) k =
      (T.to_prebasis.col.to_matrix ⬝ of_col T c) j k :
    by rw [mul_matrix_apply, col_eq_some_colg]
  ... = c j k : by rw [col_mul_of_col]

@[simp] lemma of_col_rowg (T : tableau m n) (c : cvec n) (i : fin m) :
  of_col T c (T.to_prebasis.rowg i) = (T.to_matrix ⬝ c + T.offset) i :=
funext $ λ k,
  calc of_col T c (T.to_prebasis.rowg i) k =
      (T.to_prebasis.row.to_matrix ⬝ of_col T c) i k :
    by rw [mul_matrix_apply, row_eq_some_rowg]
  ... = (T.to_matrix ⬝ c + T.offset) i k : by rw [row_mul_of_col]

lemma feasible_iff_of_col_zero_mem_sol_set : T.feasible ↔ T.of_col 0 ∈ T.sol_set :=
suffices (∀ i : fin m, T.to_prebasis.rowg i ∈ T.restricted → 0 ≤ T.offset i 0) ↔
    ∀ k : fin (m + n), k ∈ T.restricted → (0 : ℚ) ≤ T.of_col 0 k 0,
by simpa [sol_set, feasible, of_col_mem_flat],
⟨λ h k hk, (T.to_prebasis.eq_rowg_or_colg k).elim
    (by rintros ⟨i, hi⟩; subst hi; simp; tauto)
    (by rintros ⟨j, hj⟩; subst hj; simp),
  λ h i hi, by simpa using h _ hi⟩

/-- A column variable is unbounded if it is in a column where every nonpositive entry is
  in a row owned by an un -/
lemma is_unbounded_of {j : fin n} (hf : T.feasible)
  (h : ∀ i : fin m, T.to_prebasis.rowg i ∈ T.restricted → 0 ≤ T.to_matrix i j) :
  T.is_unbounded (T.to_prebasis.colg j) :=
assume q,
⟨T.of_col (max q 0 • (single j 0).to_matrix),
  ⟨of_col_mem_flat _ _,
    λ k, (T.to_prebasis.eq_rowg_or_colg k).elim
      begin
        rintros ⟨i, hi⟩ hres,
        subst hi,
        rw [of_col_rowg, add_val, matrix.mul_smul, smul_val,
          matrix_mul_apply, symm_single, single_apply],
        exact add_nonneg (mul_nonneg (le_max_right _ _) (h _ hres)) (hf _ hres),
      end
      begin
        rintros ⟨j', hj'⟩ hres,
        subst hj',
        simp [of_col_colg, smul_val, pequiv.single, pequiv.to_matrix],
        by_cases hjj : j' = j; simp [*, le_refl]
      end⟩,
  by simp [of_col_colg, smul_val, pequiv.single, pequiv.to_matrix, le_refl q]⟩

lemma is_maximised_of_col_zero {i : fin m} (hf : T.feasible)
  (hnonpos : ∀ j, T.to_matrix i j ≤ 0)
  (h0 : ∀ j, T.to_prebasis.colg j ∉ T.restricted → T.to_matrix i j = 0) :
  T.is_maximised (T.of_col 0) (T.to_prebasis.rowg i) :=
λ x hx, begin
  rw [of_col_rowg, matrix.mul_zero, zero_add, T.mem_flat_iff.1 hx.1],
  refine add_le_of_nonpos_of_le _ (le_refl _),
  refine sum_le_zero (λ j _, _),
  by_cases hj : (T.to_prebasis.colg j) ∈ T.restricted,
  { refine mul_nonpos_of_nonpos_of_nonneg (hnonpos _) (hx.2 _ hj) },
  { rw [h0 _ hj, _root_.zero_mul] }
end

lemma row_sum_erase_eq {x : cvec (m + n)} (hx : x ∈ T.flat) {r : fin m} {s : fin n} :
  (univ.erase s).sum (λ j : fin n, T.to_matrix r j * x (T.to_prebasis.colg j) 0) =
    x (T.to_prebasis.rowg r) 0 - T.offset r 0 - T.to_matrix r s * x (colg (T.to_prebasis) s) 0 :=
begin
  rw [mem_flat_iff] at hx,
  conv_rhs { rw [hx r, ← insert_erase (mem_univ s), sum_insert (not_mem_erase _ _)] },
  simp
end

/-- An expression for a column variable in terms of row variables -/
lemma colg_eq {x : cvec (m + n)} (hx : x ∈ T.flat) {r : fin m} {s : fin n}
  (hrs : T.to_matrix r s ≠ 0) : x (T.to_prebasis.colg s) 0 =
    (x (T.to_prebasis.rowg r) 0
    -(univ.erase s).sum (λ j : fin n, T.to_matrix r j * x (T.to_prebasis.colg j) 0)
        - T.offset r 0) * (T.to_matrix r s)⁻¹ :=
by simp [T.row_sum_erase_eq hx, mul_left_comm (T.to_matrix r s)⁻¹, mul_assoc,
    mul_left_comm (T.to_matrix r s), mul_inv_cancel hrs]

lemma colg_eq' {x : cvec (m + n)} (hx : x ∈ T.flat) {r : fin m} {s : fin n}
  (hrs : T.to_matrix r s ≠ 0) : x (T.to_prebasis.colg s) 0 =
  univ.sum (λ (j : fin n), (if j = s then (T.to_matrix r s)⁻¹
    else (-(T.to_matrix r j * (T.to_matrix r s)⁻¹))) *
      x (colg (swap (T.to_prebasis) r s) j) 0) -
  (T.offset r 0) * (T.to_matrix r s)⁻¹ :=
have (univ.erase s).sum
    (λ j : fin n, ite (j = s) (T.to_matrix r s)⁻¹ (-(T.to_matrix r j * (T.to_matrix r s)⁻¹)) *
      x (colg (swap (T.to_prebasis) r s) j) 0) =
    (univ.erase s).sum (λ j : fin n,
      -T.to_matrix r j * x (T.to_prebasis.colg j) 0 * (T.to_matrix r s)⁻¹),
  from finset.sum_congr rfl $ λ j hj,
    by simp [if_neg (mem_erase.1 hj).1, colg_swap_of_ne _ (mem_erase.1 hj).1,
      mul_comm, mul_assoc, mul_left_comm],
by rw [← finset.insert_erase (mem_univ s), finset.sum_insert (not_mem_erase _ _),
    if_pos rfl, colg_swap, colg_eq T hx hrs, this, ← finset.sum_mul];
  simp [_root_.add_mul, mul_comm, _root_.mul_add]

lemma pivot_pivot {r : fin m} {s : fin n} (hrs : T.to_matrix r s ≠ 0) :
  (T.pivot r s).pivot r s = T :=
begin
  cases T,
  simp [pivot, function.funext_iff],
  split; intros; split_ifs;
  simp [*, mul_assoc, mul_left_comm (T_to_matrix r s),
    mul_left_comm (T_to_matrix r s)⁻¹, mul_comm (T_to_matrix r s),
    inv_mul_cancel hrs]
end

/- These two set are equal -/
private lemma subset_flat_pivot {r : fin m} {s : fin n} (h : T.to_matrix r s ≠ 0) :
  T.flat ⊆ (T.pivot r s).flat :=
λ x hx,
have ∀ i : fin m, (univ.erase s).sum (λ j : fin n,
  ite (j = s) (T.to_matrix i s * (T.to_matrix r s)⁻¹)
    (T.to_matrix i j + -(T.to_matrix i s * T.to_matrix r j * (T.to_matrix r s)⁻¹))
      * x ((T.to_prebasis.swap r s).colg j) 0) =
  (univ.erase s).sum (λ j : fin n, T.to_matrix i j * x (T.to_prebasis.colg j) 0 -
    T.to_matrix r j *
      x (T.to_prebasis.colg j) 0 * T.to_matrix i s * (T.to_matrix r s)⁻¹),
  from λ i, finset.sum_congr rfl (λ j hj,
    by rw [if_neg (mem_erase.1 hj).1, colg_swap_of_ne _ (mem_erase.1 hj).1];
      simp [_root_.mul_add, _root_.add_mul, mul_comm, mul_assoc, mul_left_comm]),
begin
  rw [mem_flat_iff],
  assume i,
  by_cases hir : i = r,
  { rw eq_comm at hir,
    subst hir,
    dsimp [pivot],
    simp [mul_inv_cancel h, neg_mul_eq_neg_mul_symm, if_true,
      add_comm, mul_inv_cancel, rowg_swap, eq_self_iff_true, T.colg_eq' hx h],
    congr, funext, congr },
  { dsimp [pivot],
    simp only [if_neg hir],
    rw [← insert_erase (mem_univ s), sum_insert (not_mem_erase _ _),
      if_pos rfl, colg_swap, this, sum_sub_distrib, ← sum_mul, ← sum_mul,
      T.row_sum_erase_eq hx, rowg_swap_of_ne _ hir],
    simp [T.row_sum_erase_eq hx, _root_.mul_add, _root_.add_mul,
      mul_comm, mul_left_comm, mul_assoc],
    simp [mul_assoc, mul_left_comm (T.to_matrix r s), mul_left_comm (T.to_matrix r s)⁻¹,
      mul_comm (T.to_matrix r s), inv_mul_cancel h] }
end

@[simp] lemma pivot_pivot_element (r : fin m) (s : fin n) :
  (T.pivot r s).to_matrix r s = (T.to_matrix r s)⁻¹ :=
by simp [pivot, if_pos rfl]

@[simp] lemma pivot_pivot_row {r : fin m} {j s : fin n} (h : j ≠ s) :
  (T.pivot r s).to_matrix r j = -T.to_matrix r j / T.to_matrix r s :=
by dsimp [pivot]; rw [if_pos rfl, if_neg h, div_eq_mul_inv]

@[simp] lemma pivot_pivot_column {i r : fin m} {s : fin n} (h : i ≠ r) :
  (T.pivot r s).to_matrix i s = T.to_matrix i s / T.to_matrix r s :=
by dsimp [pivot]; rw [if_neg h, if_pos rfl, div_eq_mul_inv]

@[simp] lemma pivot_of_ne_of_ne {i r : fin m} {j s : fin n} (hir : i ≠ r)
  (hjs : j ≠ s) : (T.pivot r s).to_matrix i j =
  T.to_matrix i j - T.to_matrix i s * T.to_matrix r j / T.to_matrix r s :=
by dsimp [pivot]; rw [if_neg hir, if_neg hjs, div_eq_mul_inv]

lemma offset_pivot_row {r : fin m} {s : fin n} : (T.pivot r s).offset r 0 =
  -T.offset r 0 / T.to_matrix r s :=
by simp [pivot, if_pos rfl, div_eq_mul_inv]

lemma offset_pivot_of_ne {i r : fin m} {s : fin n} (hir : i ≠ r) : (T.pivot r s).offset i 0 =
  T.offset i 0 - T.to_matrix i s * T.offset r 0 / T.to_matrix r s :=
by dsimp [pivot]; rw [if_neg hir, div_eq_mul_inv]

lemma flat_pivot {r : fin m} {s : fin n} (hrs : T.to_matrix r s ≠ 0) :
  (T.pivot r s).flat = T.flat :=
set.subset.antisymm
  (by conv_rhs { rw ← T.pivot_pivot hrs };
    exact subset_flat_pivot _ (by simp [pivot, hrs]))
  (subset_flat_pivot T hrs)

lemma sol_set_pivot {r : fin m} {s : fin n} (hrs : T.to_matrix r s ≠ 0) :
  (T.pivot r s).sol_set = T.sol_set :=
by rw [sol_set, flat_pivot _ hrs]; refl

end predicate_lemmas

section simplex




end simplex

end tableau
