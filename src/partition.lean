import data.matrix.pequiv data.rat.basic

variables {m n : ℕ}

/-- The type of ordered partitions of `m + n` elements into a
  `m` row variables and `n` column variables  -/
structure partition (m n : ℕ) : Type :=
( rowp : fin m ≃. fin (m + n) )
( colp : fin n ≃. fin (m + n) )
( rowp_trans_rowp_symm : rowp.trans rowp.symm = pequiv.refl (fin m) )
( colp_trans_colp_symm : colp.trans colp.symm = pequiv.refl (fin n) )
( rowp_trans_colp_symm : rowp.trans colp.symm = ⊥ )

namespace partition
open pequiv function matrix finset fintype

local infix ` ⬝ `:70 := matrix.mul
local postfix `ᵀ` : 1500 := transpose

attribute [simp] rowp_trans_rowp_symm colp_trans_colp_symm rowp_trans_colp_symm

lemma fin.coe_eq_val (a : fin n) : (a : ℕ) = a.val := rfl

def default : partition m n :=
{ rowp :=
  { to_fun := some ∘ fin.cast_le (le_add_right (le_refl _)),
    inv_fun := λ j, if hm : j.1 < m then some ⟨j, hm⟩ else none,
    inv := begin
      rintros ⟨i, _⟩ ⟨j, _⟩, split_ifs;
      simp [fin.coe_eq_val, fin.cast_le, fin.cast_lt, eq_comm, -not_lt];
      intro; simp [*, -not_lt] at *,
    end },
  colp := { to_fun := λ i, some ⟨m + i, add_lt_add_of_le_of_lt (le_refl _) i.2⟩,
    inv_fun := λ j, if hm : m ≤ j.1
      then some ⟨j - m, (nat.sub_lt_left_iff_lt_add hm).2 j.2⟩ else none,
    inv := begin
      rintros ⟨i, _⟩ ⟨j, _⟩,
      simp [pequiv.trans, pequiv.symm, fin.cast_le, fin.cast_lt, fin.coe_eq_val, fin.ext_iff],
      split_ifs,
      { simp [fin.ext_iff, nat.sub_eq_iff_eq_add h, @eq_comm _ j] at * },
      { simp, intro, subst j, simp [nat.le_add_left, *] at * }
    end },
  rowp_trans_rowp_symm := trans_symm_eq_iff_forall_is_some.2 (λ _, rfl),
  colp_trans_colp_symm := trans_symm_eq_iff_forall_is_some.2 (λ _, rfl),
  rowp_trans_colp_symm := pequiv.ext begin
    rintro ⟨i, hi⟩,
    dsimp [pequiv.trans, pequiv.symm, fin.cast_le, fin.cast_lt],
    rw [dif_neg (not_le_of_gt hi)]
  end }

instance : inhabited (partition m n) := ⟨default⟩

lemma is_some_rowp (B : partition m n) : ∀ (i : fin m), (B.rowp i).is_some :=
by rw [← trans_symm_eq_iff_forall_is_some, rowp_trans_rowp_symm]

lemma is_some_colp (B : partition m n) : ∀ (k : fin n), (B.colp k).is_some :=
by rw [← trans_symm_eq_iff_forall_is_some, colp_trans_colp_symm]

lemma injective_rowp (B : partition m n) : injective B.rowp :=
injective_of_forall_is_some (is_some_rowp B)

lemma injective_colp (B : partition m n) : injective B.colp :=
injective_of_forall_is_some (is_some_colp B)

/-- given a row index, `rowg` returns the variable in that position -/
def rowg (B : partition m n) (r : fin m) : fin (m + n) :=
option.get (B.is_some_rowp r)

/-- given a column index, `colg` returns the variable in that position -/
def colg (B : partition m n) (s : fin n) : fin (m + n) :=
option.get (B.is_some_colp s)

lemma injective_rowg (B : partition m n) : injective B.rowg :=
λ x y h, by rw [rowg, rowg, ← option.some_inj, option.some_get, option.some_get] at h;
  exact injective_rowp B h

lemma injective_colg (B : partition m n) : injective B.colg :=
λ x y h, by rw [colg, colg, ← option.some_inj, option.some_get, option.some_get] at h;
  exact injective_colp B h

local infix ` ♣ `: 70 := pequiv.trans

def swap (B : partition m n) (r : fin m) (s : fin n) : partition m n :=
{ rowp := B.rowp.trans (equiv.swap (B.rowg r) (B.colg s)).to_pequiv,
  colp := B.colp.trans (equiv.swap (B.rowg r) (B.colg s)).to_pequiv,
  rowp_trans_rowp_symm := by rw [symm_trans_rev, ← trans_assoc, trans_assoc B.rowp,
      ← equiv.to_pequiv_symm,  ← equiv.to_pequiv_trans];
    simp,
  colp_trans_colp_symm := by rw [symm_trans_rev, ← trans_assoc, trans_assoc B.colp,
      ← equiv.to_pequiv_symm, ← equiv.to_pequiv_trans];
    simp,
  rowp_trans_colp_symm := by rw [symm_trans_rev, ← trans_assoc, trans_assoc B.rowp,
      ← equiv.to_pequiv_symm, ← equiv.to_pequiv_trans];
    simp }

lemma not_is_some_colp_of_is_some_rowp (B : partition m n) (j : fin (m + n)) :
  (B.rowp.symm j).is_some → (B.colp.symm j).is_some → false :=
begin
  rw [option.is_some_iff_exists, option.is_some_iff_exists],
  rintros ⟨i, hi⟩ ⟨k, hk⟩,
  have : B.rowp.trans B.colp.symm i = none,
  { rw [B.rowp_trans_colp_symm, pequiv.bot_apply] },
  rw [pequiv.trans_eq_none] at this,
  rw [pequiv.eq_some_iff] at hi,
  exact (this j k).resolve_left (not_not.2 hi) hk
end

lemma colp_ne_none_of_rowp_eq_none (B : partition m n) (j : fin (m + n))
  (hb : B.rowp.symm j = none) (hnb : B.colp.symm j = none) : false :=
have hs : card (univ.image B.rowp) = m,
  by rw [card_image_of_injective _ (B.injective_rowp), card_univ, card_fin],
have ht : card (univ.image B.colp) = n,
  by rw [card_image_of_injective _ (B.injective_colp), card_univ, card_fin],
have hst : disjoint (univ.image B.rowp) (univ.image B.colp),
  from finset.disjoint_left.2 begin
    simp only [mem_image, exists_imp_distrib, not_exists],
    assume j i _ hrowp k _ hcolp,
    cases option.is_some_iff_exists.1 (is_some_rowp B i) with x hi,
    cases option.is_some_iff_exists.1 (is_some_colp B k) with y hk,
    have hxy : x = y,
    { rw [← option.some_inj, ← hk, ← hi, hrowp, hcolp] }, subst hxy,
    rw [← eq_some_iff] at hi hk,
    refine not_is_some_colp_of_is_some_rowp B x _ _;
    simp [hi, hk]
  end,
have (univ.image B.rowp) ∪ (univ.image B.colp) = univ.image (@some (fin (m + n))),
  from eq_of_subset_of_card_le
    begin
      assume i h,
      simp only [finset.mem_image, finset.mem_union] at h,
      rcases h with ⟨j, _, hj⟩ | ⟨k, _, hk⟩,
      { simpa [hj.symm, option.is_some_iff_exists, eq_comm] using is_some_rowp B j },
      { simpa [hk.symm, option.is_some_iff_exists, eq_comm] using is_some_colp B k }
    end
    (begin
      rw [card_image_of_injective, card_univ, card_fin, card_disjoint_union hst, hs, ht],
      exact λ _ _, option.some_inj.1,
    end),
begin
  simp only [option.eq_none_iff_forall_not_mem, mem_iff_mem B.rowp,
    mem_iff_mem B.colp] at hb hnb,
  have := (finset.ext.1 this (some j)).2 (mem_image_of_mem _ (mem_univ _)),
  simp only [hb, hnb, mem_image, finset.mem_union, option.mem_def.symm] at this, tauto
end

lemma is_some_rowp_iff (B : partition m n) (j : fin (m + n)) :
  (B.rowp.symm j).is_some ↔ ¬(B.colp.symm j).is_some :=
⟨not_is_some_colp_of_is_some_rowp B j,
  by erw [option.not_is_some_iff_eq_none, ← option.ne_none_iff_is_some, forall_swap];
    exact colp_ne_none_of_rowp_eq_none B j⟩

@[simp] lemma colp_rowg_eq_none (B : partition m n) (r : fin m) :
  B.colp.symm (B.rowg r) = none :=
option.not_is_some_iff_eq_none.1 ((B.is_some_rowp_iff _).1 (is_some_symm_get _ _))

@[simp] lemma rowp_colg_eq_none (B : partition m n) (s : fin n) :
  B.rowp.symm (B.colg s) = none :=
option.not_is_some_iff_eq_none.1 (mt (B.is_some_rowp_iff _).1 $ not_not.2 (is_some_symm_get _ _))

@[simp] lemma rowg_mem (B : partition m n) (r : fin m) : (B.rowg r) ∈ B.rowp r :=
option.get_mem _

lemma rowp_eq_some_rowg (B : partition m n) (r : fin m) : B.rowp r = some (B.rowg r) :=
rowg_mem _ _

@[simp] lemma colg_mem (B : partition m n) (s : fin n) : (B.colg s) ∈ B.colp s :=
option.get_mem _

lemma colp_eq_some_colg (B : partition m n) (s : fin n) : B.colp s = some (B.colg s) :=
colg_mem _ _

@[simp] lemma rowp_rowg (B : partition m n) (r : fin m) : B.rowp.symm (B.rowg r) = some r :=
B.rowp.mem_iff_mem.2 (rowg_mem _ _)

@[simp] lemma colp_colg (B : partition m n) (s : fin n) : B.colp.symm (B.colg s) = some s :=
B.colp.mem_iff_mem.2 (colg_mem _ _)

lemma eq_rowg_or_colg (B : partition m n) (i : fin (m + n)) :
  (∃ j, i = B.rowg j) ∨ (∃ j, i = B.colg j) :=
begin
  dsimp only [rowg, colg],
  by_cases h : ↥(B.rowp.symm i).is_some,
  { cases option.is_some_iff_exists.1 h with j hj,
    exact or.inl ⟨j, by rw [B.rowp.eq_some_iff] at hj;
      rw [← option.some_inj, ← hj, option.some_get]⟩ },
  { rw [(@not_iff_comm _ _ (classical.dec _) (classical.dec _)).1 (B.is_some_rowp_iff _).symm] at h,
    cases option.is_some_iff_exists.1 h with j hj,
    exact or.inr ⟨j, by rw [B.colp.eq_some_iff] at hj;
      rw [← option.some_inj, ← hj, option.some_get]⟩ }
end

lemma rowg_ne_colg (B : partition m n) (i : fin m) (j : fin n) : B.rowg i ≠ B.colg j :=
λ h, by simpa using congr_arg B.rowp.symm h

@[simp] lemma option.get_inj {α : Type*} : Π {a b : option α} {ha : a.is_some} {hb : b.is_some},
  option.get ha = option.get hb ↔ a = b
| (some a) (some b) _ _ := by rw [option.get_some, option.get_some, option.some_inj]

@[extensionality] lemma ext {B C : partition m n} (h : ∀ i, B.rowg i = C.rowg i)
  (h₂ : ∀ j, B.colg j = C.colg j) : B = C :=
begin
  cases B, cases C,
  simp [rowg, colg, function.funext_iff, pequiv.ext_iff] at *,
  tauto
end

@[simp] lemma single_rowg_mul_rowp (B : partition m n) (i : fin m) :
  ((single (0 : fin 1) (B.rowg i)).to_matrix : matrix _ _ ℚ) ⬝
    B.rowp.to_matrixᵀ = (single (0 : fin 1) i).to_matrix :=
by rw [← to_matrix_symm, ← to_matrix_trans, single_trans_of_mem _ (rowp_rowg _ _)]

@[simp] lemma single_rowg_mul_colp (B : partition m n) (i : fin m) :
  ((single (0 : fin 1) (B.rowg i)).to_matrix : matrix _ _ ℚ) ⬝
    B.colp.to_matrixᵀ = 0 :=
by rw [← to_matrix_symm, ← to_matrix_trans, single_trans_of_eq_none _ (colp_rowg_eq_none _ _),
  to_matrix_bot]; apply_instance

@[simp] lemma single_colg_mul_colp (B : partition m n) (k : fin n) :
  ((single (0 : fin 1) (B.colg k)).to_matrix : matrix _ _ ℚ) ⬝
    B.colp.to_matrixᵀ = (single (0 : fin 1) k).to_matrix :=
by rw [← to_matrix_symm, ← to_matrix_trans, single_trans_of_mem _ (colp_colg _ _)]

lemma single_colg_mul_rowp (B : partition m n) (k : fin n) :
  ((single (0 : fin 1) (B.colg k)).to_matrix : matrix _ _ ℚ) ⬝
    B.rowp.to_matrixᵀ = 0 :=
by rw [← to_matrix_symm, ← to_matrix_trans, single_trans_of_eq_none _ (rowp_colg_eq_none _ _),
  to_matrix_bot]; apply_instance

lemma colp_trans_rowp_symm (B : partition m n) : B.colp.trans B.rowp.symm = ⊥ :=
symm_injective $ by rw [symm_trans_rev, symm_symm, rowp_trans_colp_symm, symm_bot]

@[simp] lemma colp_mul_rowp_transpose (B : partition m n) :
  (B.colp.to_matrix : matrix _ _ ℚ) ⬝ B.rowp.to_matrixᵀ = 0 :=
by rw [← to_matrix_bot, ← B.colp_trans_rowp_symm, to_matrix_trans, to_matrix_symm]

@[simp] lemma rowp_mul_colp_transpose (B : partition m n) :
  (B.rowp.to_matrix : matrix _ _ ℚ) ⬝ B.colp.to_matrixᵀ = 0 :=
by rw [← to_matrix_bot, ← B.rowp_trans_colp_symm, to_matrix_trans, to_matrix_symm]

@[simp] lemma colp_mul_colp_transpose (B : partition m n) :
  (B.colp.to_matrix : matrix _ _ ℚ) ⬝ B.colp.to_matrixᵀ = 1 :=
by rw [← to_matrix_refl, ← B.colp_trans_colp_symm, to_matrix_trans, to_matrix_symm]

@[simp] lemma rowp_mul_rowp_transpose (B : partition m n) :
  (B.rowp.to_matrix : matrix _ _ ℚ) ⬝ B.rowp.to_matrixᵀ = 1 :=
by rw [← to_matrix_refl, ← B.rowp_trans_rowp_symm, to_matrix_trans, to_matrix_symm]

lemma transpose_mul_add_transpose_mul (B : partition m n) :
  (B.rowp.to_matrixᵀ ⬝ B.rowp.to_matrix : matrix _ _ ℚ) +
  B.colp.to_matrixᵀ ⬝ B.colp.to_matrix  = 1 :=
begin
  ext,
  repeat {rw [← to_matrix_symm, ← to_matrix_trans] },
  simp only [add_val, pequiv.symm_trans, pequiv.to_matrix, one_val,
    pequiv.mem_of_set_iff, set.mem_set_of_eq],
  have := is_some_rowp_iff B j,
  split_ifs; tauto
end

lemma swap_rowp_eq (B : partition m n) (r : fin m) (s : fin n) :
  (B.swap r s).rowp.to_matrix = (B.rowp.to_matrix : matrix _ _ ℚ)
  - (single r (B.rowg r)).to_matrix + (single r (B.colg s)).to_matrix :=
begin
  dsimp [swap],
  rw [to_matrix_trans, to_matrix_swap],
  simp only [matrix.mul_add, sub_eq_add_neg, matrix.mul_one, matrix.mul_neg,
    (to_matrix_trans _ _).symm, trans_single_of_mem _ (rowg_mem B r),
    trans_single_of_eq_none _ (rowp_colg_eq_none B s), to_matrix_bot, neg_zero, add_zero]
end

lemma swap_colp_eq (B : partition m n) (r : fin m) (s : fin n) :
  (B.swap r s).colp.to_matrix = (B.colp.to_matrix : matrix _ _ ℚ)
  - (single s (B.colg s)).to_matrix + (single s (B.rowg r)).to_matrix :=
begin
  dsimp [swap],
  rw [to_matrix_trans, to_matrix_swap],
  simp only [matrix.mul_add, sub_eq_add_neg, matrix.mul_one, matrix.mul_neg,
    (to_matrix_trans _ _).symm, trans_single_of_mem _ (colg_mem B s),
    trans_single_of_eq_none _ (colp_rowg_eq_none B r), to_matrix_bot, neg_zero, add_zero]
end

@[simp] lemma rowg_swap (B : partition m n) (r : fin m) (s : fin n) :
  (B.swap r s).rowg r = B.colg s :=
option.some_inj.1 begin
  dsimp [swap, rowg, colg, pequiv.trans],
  rw [option.some_get, option.some_get],
  conv in (B.rowp r) { rw rowp_eq_some_rowg },
  dsimp [equiv.to_pequiv, equiv.swap_apply_def, rowg],
  simp,
end

@[simp] lemma colg_swap (B : partition m n) (r : fin m) (s : fin n) :
  (B.swap r s).colg s = B.rowg r :=
option.some_inj.1 begin
  dsimp [swap, rowg, colg, pequiv.trans],
  rw [option.some_get, option.some_get],
  conv in (B.colp s) { rw colp_eq_some_colg },
  dsimp [equiv.to_pequiv, equiv.swap_apply_def, colg],
  rw [if_neg, if_pos rfl, option.some_get],
  exact (rowg_ne_colg _ _ _).symm
end

lemma rowg_swap_of_ne (B : partition m n) {i r : fin m} {s : fin n} (h : i ≠ r) :
  (B.swap r s).rowg i = B.rowg i :=
option.some_inj.1 begin
  dsimp [swap, rowg, colg, pequiv.trans],
  rw [option.some_get, option.bind_eq_some'],
  use [B.rowg i, rowp_eq_some_rowg _ _],
  dsimp [equiv.to_pequiv, equiv.swap_apply_def, option.get_some],
  rw [← colg, ← rowg, if_neg (rowg_ne_colg B i s), if_neg
    (mt B.injective_rowg.eq_iff.1 h), rowg]
end

lemma colg_swap_of_ne (B : partition m n) {r : fin m} {j s : fin n} (h : j ≠ s) :
  (B.swap r s).colg j = B.colg j :=
option.some_inj.1 begin
  dsimp [swap, rowg, colg, pequiv.trans],
  rw [option.some_get, option.bind_eq_some'],
  use [B.colg j, colp_eq_some_colg _ _],
  dsimp [equiv.to_pequiv, equiv.swap_apply_def, option.get_some],
  rw [← colg, ← rowg, if_neg (rowg_ne_colg B r j).symm, if_neg
    (mt B.injective_colg.eq_iff.1 h), colg]
end

lemma rowg_swap' (B : partition m n) (i r : fin m) (s : fin n) :
  (B.swap r s).rowg i = if i = r then B.colg s else B.rowg i :=
if hir : i = r then by simp [hir]
  else by rw [if_neg hir, rowg_swap_of_ne _ hir]

lemma colg_swap' (B : partition m n) (r : fin m) (j s : fin n) :
  (B.swap r s).colg j = if j = s then B.rowg r else B.colg j :=
if hjs : j = s then by simp [hjs]
  else by rw [if_neg hjs, colg_swap_of_ne _ hjs]

@[simp] lemma swap_swap (B : partition m n) (r : fin m) (s : fin n) :
  (B.swap r s).swap r s = B :=
by ext; intros; simp [rowg_swap', colg_swap']; split_ifs; cc

@[simp] lemma colp_trans_swap_rowp_symm (B : partition m n) (r : fin m) (s : fin n) :
  B.colp.trans (B.swap r s).rowp.symm = single s r :=
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

@[simp] lemma colp_mul_swap_rowp_tranpose (B : partition m n) (r : fin m) (s : fin n) :
  (B.colp.to_matrix : matrix _ _ ℚ) ⬝ (B.swap r s).rowp.to_matrixᵀ = (single s r).to_matrix :=
by rw [← colp_trans_swap_rowp_symm, to_matrix_trans, to_matrix_symm]

lemma rowp_trans_swap_rowp_transpose (B : partition m n) (r : fin m) (s : fin n) :
  B.rowp.trans (B.swap r s).rowp.symm = of_set {i | i ≠ r} :=
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

lemma swap_rowp_transpose_mul_single_of_ne (B : partition m n) {r : fin m}
  (s : fin n) {i : fin m} (hir : i ≠ r) :
  ((B.swap r s).rowp.to_matrixᵀ : matrix _ _ ℚ) ⬝ (single i (0 : fin 1)).to_matrix =
  B.rowp.to_matrixᵀ ⬝ (single i 0).to_matrix :=
begin
  simp only [swap_rowp_eq, sub_eq_add_neg, matrix.mul_add, matrix.mul_neg, matrix.mul_one,
    matrix.add_mul, (to_matrix_trans _ _).symm, (to_matrix_symm _).symm, transpose_add,
    transpose_neg, matrix.neg_mul, symm_trans_rev, trans_assoc],
  rw [trans_single_of_mem _ (rowp_rowg _ _), trans_single_of_eq_none, trans_single_of_eq_none,
    to_matrix_bot, neg_zero, add_zero, add_zero];
  {dsimp [single]; simp [*, B.injective_rowg.eq_iff]} <|> apply_instance
end

@[simp] lemma swap_rowp_transpose_mul_single (B : partition m n) (r : fin m) (s : fin n) :
  ((B.swap r s).rowp.to_matrixᵀ : matrix _ _ ℚ) ⬝ (single r (0 : fin 1)).to_matrix =
  B.colp.to_matrixᵀ ⬝ (single s (0 : fin 1)).to_matrix :=
begin
  simp only [swap_rowp_eq, sub_eq_add_neg, matrix.mul_add, matrix.mul_neg, matrix.mul_one,
    matrix.add_mul, (to_matrix_trans _ _).symm, (to_matrix_symm _).symm, transpose_add,
    transpose_neg, matrix.neg_mul, symm_trans_rev, trans_assoc, symm_single],
  rw [trans_single_of_mem _ (rowp_rowg _ _), trans_single_of_mem _ (mem_single _ _),
    trans_single_of_mem _ (mem_single _ _), trans_single_of_mem _ (colp_colg _ _)],
  simp,
  all_goals {apply_instance}
end

def equiv_aux : partition m n ≃ Σ' (rowp : fin m ≃. fin (m + n))
  (colp : fin n ≃. fin (m + n))
  ( rowp_trans_rowp_symm : rowp.trans rowp.symm = pequiv.refl (fin m) )
( colp_trans_colp_symm : colp.trans colp.symm = pequiv.refl (fin n) ),
  rowp.trans colp.symm = ⊥ :=
{ to_fun := λ ⟨a, b, c, d, e⟩, ⟨a, b, c, d, e⟩,
  inv_fun := λ ⟨a, b, c, d, e⟩, ⟨a, b, c, d, e⟩,
  left_inv := λ ⟨_, _, _, _, _⟩, rfl,
  right_inv := λ ⟨_, _, _, _, _⟩, rfl }

end partition
