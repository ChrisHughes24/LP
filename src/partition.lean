import data.matrix.pequiv data.rat.basic data.vector2

variables {m n : ℕ}

/-- The type of ordered partitions of `m + n` elements into vectors of
  `m` row variables and `n` column variables  -/
@[derive decidable_eq] structure partition (m n : ℕ) : Type :=
(row_indices : vector (fin (m + n)) m)
(col_indices : vector (fin (m + n)) n)
(mem_row_indices_or_col_indices :
  ∀ v : fin (m + n), v ∈ row_indices.to_list ∨ v ∈ col_indices.to_list)

open pequiv function matrix finset fintype

namespace partition

local infix ` ⬝ `:70 := matrix.mul
local postfix `ᵀ` : 1500 := transpose

variable (B : partition m n)

def fintype_aux : partition m n ≃ { x : vector (fin (m + n)) m × vector (fin (m + n)) n //
  ∀ v : fin (m + n), v ∈ x.1.to_list ∨ v ∈ x.2.to_list } :=
{ to_fun := λ ⟨r, c, h⟩, ⟨⟨r, c⟩, h⟩,
  inv_fun := λ ⟨⟨r, c⟩, h⟩, ⟨r, c, h⟩,
  left_inv := λ ⟨r, c, h⟩, rfl,
  right_inv := λ ⟨⟨r, c⟩, h⟩, rfl }

instance : fintype (partition m n) := fintype.of_equiv _ fintype_aux.symm

def rowg : fin m → fin (m + n) := B.row_indices.nth
def colg : fin n → fin (m + n) := B.col_indices.nth

lemma mem_row_indices_iff_exists {v : fin (m + n)} :
  v ∈ B.row_indices.to_list ↔ ∃ i, v = B.rowg i :=
by simp only [vector.mem_iff_nth, eq_comm, rowg]

lemma mem_col_indices_iff_exists {v : fin (m + n)} :
  v ∈ B.col_indices.to_list ↔ ∃ j, v = B.colg j :=
by simp only [vector.mem_iff_nth, eq_comm, colg]

lemma eq_rowg_or_colg (v : fin (m + n)) : (∃ i, v = B.rowg i) ∨ (∃ j, v = B.colg j) :=
by rw [← mem_row_indices_iff_exists, ← mem_col_indices_iff_exists];
  exact B.mem_row_indices_or_col_indices _

lemma row_indices_append_col_indices_nodup : (B.row_indices.append B.col_indices).to_list.nodup :=
vector.nodup_iff_nth_inj.2 $ fintype.injective_iff_surjective.2 $ λ v,
  (B.mem_row_indices_or_col_indices v).elim
    (by rw [← vector.mem_iff_nth]; simp {contextual := tt})
    (by rw [← vector.mem_iff_nth]; simp {contextual := tt})

lemma row_indices_nodup : B.row_indices.to_list.nodup :=
begin
  have := B.row_indices_append_col_indices_nodup,
  simp [list.nodup_append] at this, tauto
end

lemma col_indices_nodup : B.col_indices.to_list.nodup :=
begin
  have := B.row_indices_append_col_indices_nodup,
  simp [list.nodup_append] at this, tauto
end

@[simp] lemma rowg_ne_colg (i j) : B.rowg i ≠ B.colg j :=
λ h, begin
  rw [rowg, colg] at h,
  have := B.row_indices_append_col_indices_nodup,
  rw [vector.to_list_append (B.row_indices) (B.col_indices), list.nodup_append,
    list.disjoint_right] at this,
  exact this.2.2 (by rw h; exact vector.nth_mem _ _) (vector.nth_mem i B.row_indices)
end

@[simp] lemma colg_ne_rowg (i j) : B.colg j ≠ B.rowg i := ne.symm $ rowg_ne_colg _ _ _

lemma injective_rowg : injective B.rowg :=
vector.nodup_iff_nth_inj.1 B.row_indices_nodup

lemma injective_colg : injective B.colg :=
vector.nodup_iff_nth_inj.1 B.col_indices_nodup

def rowp : fin m ≃. fin (m + n) :=
{ to_fun := λ i, some (B.rowg i),
  inv_fun := λ v, fin.find (λ i, B.rowg i = v),
  inv := λ i v, begin
    cases h : fin.find (λ i, B.rowg i = v),
    { simp [fin.find_eq_none_iff, *] at * },
    { rw [fin.find_eq_some_iff] at h,
      cases h with h _,
      subst h,
      simp [B.injective_rowg.eq_iff, eq_comm] }
  end }

def colp : fin n ≃. fin (m + n) :=
{ to_fun := λ j, some (B.colg j),
  inv_fun := λ v, fin.find (λ j, B.colg j = v),
  inv := λ j v, begin
    cases h : fin.find (λ j, B.colg j = v),
    { simp [fin.find_eq_none_iff, *] at * },
    { rw [fin.find_eq_some_iff] at h,
      cases h with h _,
      subst h,
      simp [B.injective_colg.eq_iff, eq_comm] }
  end }

@[simp] lemma rowp_trans_rowp_symm : B.rowp.trans B.rowp.symm = pequiv.refl _ :=
trans_symm_eq_iff_forall_is_some.2 (λ _, rfl)

@[simp] lemma colp_trans_colp_symm : B.colp.trans B.colp.symm = pequiv.refl _ :=
trans_symm_eq_iff_forall_is_some.2 (λ _, rfl)

@[simp] lemma rowg_mem (B : partition m n) (r : fin m) : (B.rowg r) ∈ B.rowp r := eq.refl _

lemma rowp_eq_some_rowg (B : partition m n) (r : fin m) : B.rowp r = some (B.rowg r) := rfl

@[simp] lemma colg_mem (B : partition m n) (s : fin n) : (B.colg s) ∈ B.colp s := eq.refl _

lemma colp_eq_some_colg (B : partition m n) (s : fin n) : B.colp s = some (B.colg s) := rfl

@[simp] lemma rowp_rowg (B : partition m n) (r : fin m) : B.rowp.symm (B.rowg r) = some r :=
B.rowp.mem_iff_mem.2 (rowg_mem _ _)

@[simp] lemma colp_colg (B : partition m n) (s : fin n) : B.colp.symm (B.colg s) = some s :=
B.colp.mem_iff_mem.2 (colg_mem _ _)

@[simp] lemma rowp_trans_colp_symm : B.rowp.trans B.colp.symm = ⊥ :=
begin
  ext,
  simp, dsimp [pequiv.trans, pequiv.symm],
  simp [B.rowp_eq_some_rowg, colp, fin.find_eq_some_iff]
end

@[simp] lemma colg_get_colp_symm (v : fin (m + n)) (h : (B.colp.symm v).is_some) :
  B.colg (option.get h) = v :=
let ⟨j, hj⟩ := option.is_some_iff_exists.1 h in
have hj' : j ∈ B.colp.symm (B.colg (option.get h)), by simpa,
B.colp.symm.inj hj' hj

@[simp] lemma rowg_get_rowp_symm (v : fin (m + n)) (h : (B.rowp.symm v).is_some) :
  B.rowg (option.get h) = v :=
let ⟨i, hi⟩ := option.is_some_iff_exists.1 h in
have hi' : i ∈ B.rowp.symm (B.rowg (option.get h)), by simpa,
B.rowp.symm.inj hi' hi

def default : partition m n :=
{ row_indices := ⟨(list.fin_range m).map (fin.cast_add _), by simp⟩,
  col_indices := ⟨(list.fin_range n).map
    (λ i, ⟨m + i.1, add_lt_add_of_le_of_lt (le_refl _) i.2⟩), by simp⟩,
  mem_row_indices_or_col_indices := λ v,
    if h : v.1 < m
    then or.inl (list.mem_map.2 ⟨⟨v.1, h⟩, list.mem_fin_range _, fin.eta _ _⟩)
    else have v.val - m < n, from (nat.sub_lt_left_iff_lt_add (le_of_not_gt h)).2 v.2,
      or.inr (list.mem_map.2 ⟨⟨v.1 - m, this⟩, list.mem_fin_range _,
        by simp [nat.add_sub_cancel' (le_of_not_gt h)]⟩) }

instance : inhabited (partition m n) := ⟨default⟩

lemma is_some_rowp (B : partition m n) : ∀ (i : fin m), (B.rowp i).is_some := λ _, rfl

lemma is_some_colp (B : partition m n) : ∀ (k : fin n), (B.colp k).is_some := λ _, rfl

lemma injective_rowp (B : partition m n) : injective B.rowp :=
injective_of_forall_is_some (is_some_rowp B)

lemma injective_colp (B : partition m n) : injective B.colp :=
injective_of_forall_is_some (is_some_colp B)

@[elab_as_eliminator] def row_col_cases_on {C : fin (m + n) → Sort*} (B : partition m n)
  (v : fin (m + n)) (row : fin m → C v) (col : fin n → C v) : C v :=
begin
  cases h : B.rowp.symm v with r,
  { exact col (option.get (show (B.colp.symm v).is_some,
    from (B.eq_rowg_or_colg v).elim (λ ⟨r, hr⟩, absurd h (hr.symm ▸ by simp))
      (λ ⟨c, hc⟩, hc.symm ▸ by simp))) },
  { exact row r }
end

@[simp] lemma row_col_cases_on_rowg {C : fin (m + n) → Sort*} (B : partition m n)
  (r : fin m) (row : fin m → C (B.rowg r)) (col : fin n → C (B.rowg r)) :
  (row_col_cases_on B (B.rowg r) row col : C (B.rowg r)) = row r :=
by simp [row_col_cases_on]

local infix ` ♣ `: 70 := pequiv.trans

def swap (B : partition m n) (r : fin m) (s : fin n) : partition m n :=
{ row_indices := B.row_indices.update_nth r (B.col_indices.nth s),
  col_indices := B.col_indices.update_nth s (B.row_indices.nth r),
  mem_row_indices_or_col_indices := λ v,
    (B.mem_row_indices_or_col_indices v).elim
      (λ h, begin
        revert h,
        simp only [vector.mem_iff_nth, exists_imp_distrib, vector.nth_update_nth_eq_if],
        intros i hi,
        subst hi,
        by_cases r = i,
        { right, use s, simp [h] },
        { left, use i, simp [h] }
      end)
      (λ h, begin
        revert h,
        simp only [vector.mem_iff_nth, exists_imp_distrib, vector.nth_update_nth_eq_if],
        intros j hj,
        subst hj,
        by_cases s = j,
        { left, use r, simp [h] },
        { right, use j, simp [h] }
      end)}

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

lemma colp_ne_none_of_rowp_eq_none (B : partition m n) (v : fin (m + n))
  (hb : B.rowp.symm v = none) (hnb : B.colp.symm v = none) : false :=
have hs : card (univ.image B.rowg) = m,
  by rw [card_image_of_injective _ (B.injective_rowg), card_univ, card_fin],
have ht : card (univ.image B.colg) = n,
  by rw [card_image_of_injective _ (B.injective_colg), card_univ, card_fin],
have hst : disjoint (univ.image B.rowg) (univ.image B.colg),
  from finset.disjoint_left.2 begin
    simp only [mem_image, exists_imp_distrib, not_exists],
    assume v i _ hi j _ hj,
    subst hi,
    exact not_is_some_colp_of_is_some_rowp B (B.rowg i)
      (option.is_some_iff_exists.2 ⟨i, by simp⟩)
      (hj ▸ option.is_some_iff_exists.2 ⟨j, by simp⟩),
  end,
have (univ.image B.rowg) ∪ (univ.image B.colg) = univ,
  from eq_of_subset_of_card_le (λ _ _, mem_univ _)
    (by rw [card_disjoint_union hst, hs, ht, card_univ, card_fin]),
begin
  cases mem_union.1 (eq_univ_iff_forall.1 this v);
  rcases mem_image.1 h with ⟨_, _, h⟩; subst h; simp * at *
end

lemma is_some_rowp_iff (B : partition m n) (j : fin (m + n)) :
  (B.rowp.symm j).is_some ↔ ¬(B.colp.symm j).is_some :=
⟨not_is_some_colp_of_is_some_rowp B j,
  by erw [option.not_is_some_iff_eq_none, ← option.ne_none_iff_is_some, forall_swap];
    exact colp_ne_none_of_rowp_eq_none B j⟩

@[simp] lemma colp_rowg_eq_none (B : partition m n) (r : fin m) :
  B.colp.symm (B.rowg r) = none :=
option.not_is_some_iff_eq_none.1 ((B.is_some_rowp_iff _).1 (by simp))

@[simp] lemma rowp_colg_eq_none (B : partition m n) (s : fin n) :
  B.rowp.symm (B.colg s) = none :=
option.not_is_some_iff_eq_none.1 (mt (B.is_some_rowp_iff _).1 (by simp))


@[simp] lemma row_col_cases_on_colg {C : fin (m + n) → Sort*} (B : partition m n)
  (c : fin n) (row : fin m → C (B.colg c)) (col : fin n → C (B.colg c)) :
  (row_col_cases_on B (B.colg c) row col : C (B.colg c)) = col c :=
have ∀ (v' : option (fin m)) (p : option (fin m) → Prop) (h : p v') (h1 : v' = none)
  (f : Π (hpn : p none), fin n),
  (option.rec (λ (h : p none), col (f h)) (λ (r : fin m) (h : p (some r)), row r)
      v' h : C (colg B c)) = col (f (h1 ▸ h)),
  from λ v' p pv' hn f, by subst hn,
begin
  convert this (B.rowp.symm (B.colg c)) (λ x, B.rowp.symm (B.colg c) = x) rfl (by simp)
    (λ h, option.get (row_col_cases_on._proof_1 B (colg B c) h)),
  erw [← option.some_inj, option.some_get, colp_colg]
end

@[simp] lemma option.get_inj {α : Type*} : Π {a b : option α} {ha : a.is_some} {hb : b.is_some},
  option.get ha = option.get hb ↔ a = b
| (some a) (some b) _ _ := by rw [option.get_some, option.get_some, option.some_inj]

@[extensionality] lemma ext {B C : partition m n} (h : ∀ i, B.rowg i = C.rowg i)
  (h₂ : ∀ j, B.colg j = C.colg j) : B = C :=
begin
  cases B, cases C,
  simp [rowg, colg, function.funext_iff] at *,
  split; apply vector.ext; assumption
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

@[simp] lemma rowg_swap (B : partition m n) (r : fin m) (s : fin n) :
  (B.swap r s).rowg r = B.colg s :=
option.some_inj.1 begin
  dsimp [swap, rowg, colg, pequiv.trans],
  simp
end

@[simp] lemma colg_swap (B : partition m n) (r : fin m) (s : fin n) :
  (B.swap r s).colg s = B.rowg r :=
option.some_inj.1 begin
  dsimp [swap, rowg, colg, pequiv.trans],
  simp
end

lemma rowg_swap_of_ne (B : partition m n) {i r : fin m} {s : fin n} (h : i ≠ r) :
  (B.swap r s).rowg i = B.rowg i :=
option.some_inj.1 begin
  dsimp [swap, rowg, colg, pequiv.trans],
  simp [vector.nth_update_nth_of_ne h.symm]
end

lemma colg_swap_of_ne (B : partition m n) {r : fin m} {j s : fin n} (h : j ≠ s) :
  (B.swap r s).colg j = B.colg j :=
option.some_inj.1 begin
  dsimp [swap, rowg, colg, pequiv.trans],
  simp [vector.nth_update_nth_of_ne h.symm]
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

def fin.lastp : fin (m + 1 + n) := fin.cast (add_right_comm _ _ _) (fin.last (m + n))

def fin.castp (v : fin (m + n)) : fin (m + 1 + n) :=
fin.cast (add_right_comm _ _ _) (fin.cast_succ v)

def add_row (B : partition m n) : partition (m + 1) n :=
{ row_indices := (B.row_indices.map fin.castp).append ⟨[fin.lastp], rfl⟩,
  col_indices := B.col_indices.map (fin.cast (add_right_comm _ _ _) ∘ fin.cast_succ),
  mem_row_indices_or_col_indices := begin
    rintros ⟨v, hv⟩,
    simp only [fin.cast, fin.cast_le, fin.cast_lt, fin.last, vector.to_list_map,
      fin.eq_iff_veq, list.mem_map, fin.cast_le, vector.to_list_append, list.mem_append,
      function.comp, fin.cast_succ, fin.cast_add, fin.exists_iff, and_comm _ (_ = _),
      exists_and_distrib_left, exists_eq_left, fin.lastp, fin.castp],
    by_cases hvmn : v = m + n,
    { simp [hvmn] },
    { have hv : v < m + n, from lt_of_le_of_ne (nat.le_of_lt_succ $ by simpa using hv) hvmn,
      cases B.mem_row_indices_or_col_indices ⟨v, hv⟩; simp * }
  end }

lemma add_row_rowg_last (B : partition m n) : B.add_row.rowg (fin.last _) = fin.lastp :=
have (fin.last m).1 = (B.row_indices.map fin.castp).to_list.length := by simp [fin.last],
option.some_inj.1 $ by simp only [add_row, rowg, vector.nth_eq_nth_le, vector.to_list_append,
  (list.nth_le_nth _).symm, list.nth_concat_length, this, vector.to_list_mk]; refl

lemma add_row_rowg_cast_succ (B : partition m n) (i : fin m) :
  B.add_row.rowg (fin.cast_succ i) = fin.castp (B.rowg i) :=
have i.1 < (B.row_indices.to_list.map fin.castp).length, by simp [i.2],
by simp [add_row, rowg, vector.nth_eq_nth_le, vector.to_list_append,
  (list.nth_le_nth _).symm, list.nth_concat_length, vector.to_list_mk,
  list.nth_le_append _ this, list.nth_le_map]

lemma add_row_colg (B : partition m n) (j : fin n) : B.add_row.colg j = fin.castp (B.colg j) :=
fin.eq_of_veq $ by simp [add_row, colg, vector.nth_eq_nth_le, fin.castp]

def dual (B : partition m n) : partition n m :=
{ row_indices := B.col_indices.map (fin.cast (add_comm _ _)),
  col_indices := B.row_indices.map (fin.cast (add_comm _ _)),
  mem_row_indices_or_col_indices := λ v,
    (B.mem_row_indices_or_col_indices (fin.cast (add_comm _ _) v)).elim
      (λ h, or.inr begin
          simp only [vector.to_list_map, list.mem_map],
          use fin.cast (add_comm _ _) v,
          simp [fin.eq_iff_veq, h],
        end)
      (λ h, or.inl begin
          simp only [vector.to_list_map, list.mem_map],
          use fin.cast (add_comm _ _) v,
          simp [fin.eq_iff_veq, h],
        end) }

@[simp] lemma dual_dual (B : partition m n) : B.dual.dual = B :=
by cases B; simp [dual]; split; ext; simp [fin.eq_iff_veq]

end partition
