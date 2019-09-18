import data.matrix.pequiv data.rat.basic data.vector2

variables {m n : ℕ}

/-- The type of ordered partitions of `m + n` elements into vectors of
  `m` row variables and `n` column variables  -/
structure partition (m n : ℕ) : Type :=
(row_indices : vector (fin (m + n)) m)
(col_indices : vector (fin (m + n)) n)
(mem_row_indices_or_col_indices :
  ∀ v : fin (m + n), v ∈ row_indices.to_list ∨ v ∈ col_indices.to_list)

open pequiv function matrix finset fintype

namespace partition

local infix ` ⬝ `:70 := matrix.mul
local postfix `ᵀ` : 1500 := transpose

variable (P : partition m n)

def fintype_aux : partition m n ≃ { x : vector (fin (m + n)) m × vector (fin (m + n)) n //
  ∀ v : fin (m + n), v ∈ x.1.to_list ∨ v ∈ x.2.to_list } :=
{ to_fun := λ ⟨r, c, h⟩, ⟨⟨r, c⟩, h⟩,
  inv_fun := λ ⟨⟨r, c⟩, h⟩, ⟨r, c, h⟩,
  left_inv := λ ⟨r, c, h⟩, rfl,
  right_inv := λ ⟨⟨r, c⟩, h⟩, rfl }

instance : fintype (partition m n) := fintype.of_equiv _ fintype_aux.symm

def rowg : fin m → fin (m + n) := P.row_indices.nth
def colg : fin n → fin (m + n) := P.col_indices.nth

lemma mem_row_indices_iff_exists {v : fin (m + n)} :
  v ∈ P.row_indices.to_list ↔ ∃ i, v = P.rowg i :=
by simp only [vector.mem_iff_nth, eq_comm, rowg]

lemma mem_col_indices_iff_exists {v : fin (m + n)} :
  v ∈ P.col_indices.to_list ↔ ∃ j, v = P.colg j :=
by simp only [vector.mem_iff_nth, eq_comm, colg]

lemma eq_rowg_or_colg (v : fin (m + n)) : (∃ i, v = P.rowg i) ∨ (∃ j, v = P.colg j) :=
by rw [← mem_row_indices_iff_exists, ← mem_col_indices_iff_exists];
  exact P.mem_row_indices_or_col_indices _

lemma row_indices_append_col_indices_nodup : (P.row_indices.append P.col_indices).to_list.nodup :=
vector.nodup_iff_nth_inj.2 $ fintype.injective_iff_surjective.2 $ λ v,
  (P.mem_row_indices_or_col_indices v).elim
    (by rw [← vector.mem_iff_nth]; simp {contextual := tt})
    (by rw [← vector.mem_iff_nth]; simp {contextual := tt})

lemma row_indices_nodup : P.row_indices.to_list.nodup :=
begin
  have := P.row_indices_append_col_indices_nodup,
  simp [list.nodup_append] at this, tauto
end

lemma col_indices_nodup : P.col_indices.to_list.nodup :=
begin
  have := P.row_indices_append_col_indices_nodup,
  simp [list.nodup_append] at this, tauto
end

@[simp] lemma rowg_ne_colg (i j) : P.rowg i ≠ P.colg j :=
λ h, begin
  rw [rowg, colg] at h,
  have := P.row_indices_append_col_indices_nodup,
  rw [vector.to_list_append (P.row_indices) (P.col_indices), list.nodup_append,
    list.disjoint_right] at this,
  exact this.2.2 (by rw h; exact vector.nth_mem _ _) (vector.nth_mem i P.row_indices)
end

@[simp] lemma colg_ne_rowg (i j) : P.colg j ≠ P.rowg i := ne.symm $ rowg_ne_colg _ _ _

lemma injective_rowg : injective P.rowg :=
vector.nodup_iff_nth_inj.1 P.row_indices_nodup

@[simp] lemma rowg_inj {i i' : fin m} : P.rowg i = P.rowg i' ↔ i = i' := P.injective_rowg.eq_iff

lemma injective_colg : injective P.colg :=
vector.nodup_iff_nth_inj.1 P.col_indices_nodup

@[simp] lemma colg_inj {j j' : fin n} : P.colg j = P.colg j' ↔ j = j' := P.injective_colg.eq_iff

def rowp : fin (m + n) ≃. fin m :=
{ to_fun := λ v, fin.find (λ i, P.rowg i = v),
  inv_fun := λ i, some (P.rowg i),
  inv := λ v i, begin
    cases h : fin.find (λ i, P.rowg i = v),
    { simp [fin.find_eq_none_iff, *] at * },
    { rw [fin.find_eq_some_iff] at h,
      cases h with h _,
      subst h,
      simp [P.injective_rowg.eq_iff, eq_comm] }
  end }

def colp : fin (m + n) ≃. fin n :=
{ to_fun := λ v, fin.find (λ j, P.colg j = v),
  inv_fun := λ j, some (P.colg j),
  inv := λ v j, begin
    cases h : fin.find (λ j, P.colg j = v),
    { simp [fin.find_eq_none_iff, *] at * },
    { rw [fin.find_eq_some_iff] at h,
      cases h with h _,
      subst h,
      simp [P.injective_rowg.eq_iff, eq_comm] }
  end }

@[simp] lemma rowp_trans_rowp_symm : P.rowp.symm.trans P.rowp = pequiv.refl _ :=
trans_symm_eq_iff_forall_is_some.2 (λ _, rfl)

@[simp] lemma colp_trans_colp_symm : P.colp.symm.trans P.colp = pequiv.refl _ :=
trans_symm_eq_iff_forall_is_some.2 (λ _, rfl)

@[simp] lemma rowg_mem (P : partition m n) (r : fin m) : (P.rowg r) ∈ P.rowp.symm r := eq.refl _

lemma rowp_symm_eq_some_rowg (P : partition m n) (r : fin m) : P.rowp.symm r = some (P.rowg r) := rfl

@[simp] lemma colg_mem (P : partition m n) (s : fin n) : (P.colg s) ∈ P.colp.symm s := eq.refl _

lemma colp_symm_eq_some_colg (P : partition m n) (s : fin n) : P.colp.symm s = some (P.colg s) := rfl

@[simp] lemma rowp_rowg (P : partition m n) (r : fin m) : P.rowp (P.rowg r) = some r :=
P.rowp.symm.mem_iff_mem.2 (rowg_mem _ _)

@[simp] lemma colp_colg (P : partition m n) (s : fin n) : P.colp (P.colg s) = some s :=
P.colp.symm.mem_iff_mem.2 (colg_mem _ _)

@[simp] lemma rowp_symm_trans_colp : P.rowp.symm.trans P.colp = ⊥ :=
begin
  ext,
  dsimp [pequiv.trans, colp],
  simp [P.rowp_symm_eq_some_rowg, fin.find_eq_some_iff],
end

@[simp] lemma colg_get_colp_symm (v : fin (m + n)) (h : (P.colp v).is_some) :
  P.colg (option.get h) = v :=
let ⟨j, hj⟩ := option.is_some_iff_exists.1 h in
have hj' : j ∈ P.colp (P.colg (option.get h)), by simpa,
P.colp.inj hj' hj

@[simp] lemma rowg_get_rowp_symm (v : fin (m + n)) (h : (P.rowp v).is_some) :
  P.rowg (option.get h) = v :=
let ⟨i, hi⟩ := option.is_some_iff_exists.1 h in
have hi' : i ∈ P.rowp (P.rowg (option.get h)), by simpa,
P.rowp.inj hi' hi

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

lemma is_some_rowp_symm (P : partition m n) : ∀ (i : fin m), (P.rowp.symm i).is_some := λ _, rfl

lemma is_some_colp_symm (P : partition m n) : ∀ (k : fin n), (P.colp.symm k).is_some := λ _, rfl

lemma injective_rowp_symm (P : partition m n) : injective P.rowp.symm :=
injective_of_forall_is_some (is_some_rowp_symm P)

lemma injective_colp_symm (P : partition m n) : injective P.colp.symm :=
injective_of_forall_is_some (is_some_colp_symm P)

@[elab_as_eliminator] def row_col_cases_on {C : fin (m + n) → Sort*} (P : partition m n)
  (v : fin (m + n)) (row : fin m → C v) (col : fin n → C v) : C v :=
begin
  cases h : P.rowp v with r,
  { exact col (option.get (show (P.colp v).is_some,
    from (P.eq_rowg_or_colg v).elim (λ ⟨r, hr⟩, absurd h (hr.symm ▸ by simp))
      (λ ⟨c, hc⟩, hc.symm ▸ by simp))) },
  { exact row r }
end

@[simp] lemma row_col_cases_on_rowg {C : fin (m + n) → Sort*} (P : partition m n)
  (r : fin m) (row : fin m → C (P.rowg r)) (col : fin n → C (P.rowg r)) :
  (row_col_cases_on P (P.rowg r) row col : C (P.rowg r)) = row r :=
by simp [row_col_cases_on]

local infix ` ♣ `: 70 := pequiv.trans

def swap (P : partition m n) (r : fin m) (s : fin n) : partition m n :=
{ row_indices := P.row_indices.update_nth r (P.col_indices.nth s),
  col_indices := P.col_indices.update_nth s (P.row_indices.nth r),
  mem_row_indices_or_col_indices := λ v,
    (P.mem_row_indices_or_col_indices v).elim
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

lemma not_is_some_colp_of_is_some_rowp (P : partition m n) (j : fin (m + n)) :
  (P.rowp j).is_some → (P.colp j).is_some → false :=
begin
  rw [option.is_some_iff_exists, option.is_some_iff_exists],
  rintros ⟨i, hi⟩ ⟨k, hk⟩,
  have : P.rowp.symm.trans P.colp i = none,
  { rw [P.rowp_symm_trans_colp, pequiv.bot_apply] },
  rw [pequiv.trans_eq_none] at this,
  rw [← pequiv.eq_some_iff] at hi,
  exact (this j k).resolve_left (not_not.2 hi) hk
end

lemma colp_ne_none_of_rowp_eq_none (P : partition m n) (v : fin (m + n))
  (hb : P.rowp v = none) (hnb : P.colp v = none) : false :=
have hs : card (univ.image P.rowg) = m,
  by rw [card_image_of_injective _ (P.injective_rowg), card_univ, card_fin],
have ht : card (univ.image P.colg) = n,
  by rw [card_image_of_injective _ (P.injective_colg), card_univ, card_fin],
have hst : disjoint (univ.image P.rowg) (univ.image P.colg),
  from finset.disjoint_left.2 begin
    simp only [mem_image, exists_imp_distrib, not_exists],
    assume v i _ hi j _ hj,
    subst hi,
    exact not_is_some_colp_of_is_some_rowp P (P.rowg i)
      (option.is_some_iff_exists.2 ⟨i, by simp⟩)
      (hj ▸ option.is_some_iff_exists.2 ⟨j, by simp⟩),
  end,
have (univ.image P.rowg) ∪ (univ.image P.colg) = univ,
  from eq_of_subset_of_card_le (λ _ _, mem_univ _)
    (by rw [card_disjoint_union hst, hs, ht, card_univ, card_fin]),
begin
  cases mem_union.1 (eq_univ_iff_forall.1 this v);
  rcases mem_image.1 h with ⟨_, _, h⟩; subst h; simp * at *
end

lemma is_some_rowp_iff (P : partition m n) (j : fin (m + n)) :
  (P.rowp j).is_some ↔ ¬(P.colp j).is_some :=
⟨not_is_some_colp_of_is_some_rowp P j,
  by erw [option.not_is_some_iff_eq_none, ← option.ne_none_iff_is_some, forall_swap];
    exact colp_ne_none_of_rowp_eq_none P j⟩

@[simp] lemma colp_rowg_eq_none (P : partition m n) (r : fin m) :
  P.colp (P.rowg r) = none :=
option.not_is_some_iff_eq_none.1 ((P.is_some_rowp_iff _).1 (by simp))

@[simp] lemma rowp_colg_eq_none (P : partition m n) (s : fin n) :
  P.rowp (P.colg s) = none :=
option.not_is_some_iff_eq_none.1 (mt (P.is_some_rowp_iff _).1 (by simp))

@[simp] lemma row_col_cases_on_colg {C : fin (m + n) → Sort*} (P : partition m n)
  (c : fin n) (row : fin m → C (P.colg c)) (col : fin n → C (P.colg c)) :
  (row_col_cases_on P (P.colg c) row col : C (P.colg c)) = col c :=
have ∀ (v' : option (fin m)) (p : option (fin m) → Prop) (h : p v') (h1 : v' = none)
  (f : Π (hpn : p none), fin n),
  (option.rec (λ (h : p none), col (f h)) (λ (r : fin m) (h : p (some r)), row r)
      v' h : C (colg P c)) = col (f (h1 ▸ h)),
  from λ v' p pv' hn f, by subst hn,
begin
  convert this (P.rowp (P.colg c)) (λ x, P.rowp (P.colg c) = x) rfl (by simp)
    (λ h, option.get (row_col_cases_on._proof_1 P (colg P c) h)),
  erw [← option.some_inj, option.some_get, colp_colg]
end

@[simp] lemma option.get_inj {α : Type*} : Π {a b : option α} {ha : a.is_some} {hb : b.is_some},
  option.get ha = option.get hb ↔ a = b
| (some a) (some b) _ _ := by rw [option.get_some, option.get_some, option.some_inj]

@[extensionality] lemma ext {P C : partition m n} (h : ∀ i, P.rowg i = C.rowg i)
  (h₂ : ∀ j, P.colg j = C.colg j) : P = C :=
begin
  cases P, cases C,
  simp [rowg, colg, function.funext_iff] at *,
  split; apply vector.ext; assumption
end

@[simp] lemma single_rowg_mul_rowp (P : partition m n) (i : fin m) :
  ((single (0 : fin 1) (P.rowg i)).to_matrix : matrix _ _ ℚ) ⬝
    P.rowp.to_matrix = (single (0 : fin 1) i).to_matrix :=
by rw [← to_matrix_trans, single_trans_of_mem _ (rowp_rowg _ _)]

@[simp] lemma single_rowg_mul_colp (P : partition m n) (i : fin m) :
  ((single (0 : fin 1) (P.rowg i)).to_matrix : matrix _ _ ℚ) ⬝
    P.colp.to_matrix = 0 :=
by rw [← to_matrix_trans, single_trans_of_eq_none _ (colp_rowg_eq_none _ _),
  to_matrix_bot]; apply_instance

@[simp] lemma single_colg_mul_colp (P : partition m n) (k : fin n) :
  ((single (0 : fin 1) (P.colg k)).to_matrix : matrix _ _ ℚ) ⬝
    P.colp.to_matrix = (single (0 : fin 1) k).to_matrix :=
by rw [← to_matrix_trans, single_trans_of_mem _ (colp_colg _ _)]

lemma single_colg_mul_rowp (P : partition m n) (k : fin n) :
  ((single (0 : fin 1) (P.colg k)).to_matrix : matrix _ _ ℚ) ⬝
    P.rowp.to_matrix = 0 :=
by rw [← to_matrix_trans, single_trans_of_eq_none _ (rowp_colg_eq_none _ _),
  to_matrix_bot]; apply_instance

lemma colp_symm_trans_rowp (P : partition m n) : P.colp.symm.trans P.rowp = ⊥ :=
symm_injective $ by rw [symm_trans_rev, symm_symm, rowp_symm_trans_colp, symm_bot]

@[simp] lemma colp_transpose_mul_rowp (P : partition m n) :
  (P.colp.to_matrix : matrix _ _ ℚ)ᵀ ⬝ P.rowp.to_matrix = 0 :=
by rw [← to_matrix_bot, ← P.colp_symm_trans_rowp, to_matrix_trans, to_matrix_symm]

@[simp] lemma rowp_transpose_mul_colp (P : partition m n) :
  (P.rowp.to_matrix : matrix _ _ ℚ)ᵀ ⬝ P.colp.to_matrix = 0 :=
by rw [← to_matrix_bot, ← P.rowp_symm_trans_colp, to_matrix_trans, to_matrix_symm]

@[simp] lemma colp_transpose_mul_colp (P : partition m n) :
  (P.colp.to_matrix : matrix _ _ ℚ)ᵀ ⬝ P.colp.to_matrix = 1 :=
by rw [← to_matrix_refl, ← P.colp_trans_colp_symm, to_matrix_trans, to_matrix_symm]

@[simp] lemma rowp_transpose_mul_rowp (P : partition m n) :
  (P.rowp.to_matrix : matrix _ _ ℚ)ᵀ ⬝ P.rowp.to_matrix = 1 :=
by rw [← to_matrix_refl, ← P.rowp_trans_rowp_symm, to_matrix_trans, to_matrix_symm]

lemma mul_transpose_add_mul_transpose (P : partition m n) :
  (P.rowp.to_matrix ⬝ P.rowp.to_matrixᵀ : matrix _ _ ℚ) +
  P.colp.to_matrix ⬝ P.colp.to_matrixᵀ  = 1 :=
begin
  ext,
  repeat {rw [← to_matrix_symm, ← to_matrix_trans] },
  simp only [add_val, pequiv.trans_symm, pequiv.to_matrix, one_val,
    pequiv.mem_of_set_iff, set.mem_set_of_eq],
  have := is_some_rowp_iff P j,
  split_ifs; tauto
end

@[simp] lemma rowg_swap (P : partition m n) (r : fin m) (s : fin n) :
  (P.swap r s).rowg r = P.colg s :=
option.some_inj.1 begin
  dsimp [swap, rowg, colg, pequiv.trans],
  simp
end

@[simp] lemma colg_swap (P : partition m n) (r : fin m) (s : fin n) :
  (P.swap r s).colg s = P.rowg r :=
option.some_inj.1 begin
  dsimp [swap, rowg, colg, pequiv.trans],
  simp
end

@[simp] lemma swap_ne_self (P : partition m n) (r : fin m) (c : fin n) : (P.swap r c) ≠ P :=
mt (congr_arg (λ P : partition m n, P.rowg r)) $ by simp

lemma rowg_swap_of_ne (P : partition m n) {i r : fin m} {s : fin n} (h : i ≠ r) :
  (P.swap r s).rowg i = P.rowg i :=
option.some_inj.1 begin
  dsimp [swap, rowg, colg, pequiv.trans],
  simp [vector.nth_update_nth_of_ne h.symm]
end

lemma colg_swap_of_ne (P : partition m n) {r : fin m} {j s : fin n} (h : j ≠ s) :
  (P.swap r s).colg j = P.colg j :=
option.some_inj.1 begin
  dsimp [swap, rowg, colg, pequiv.trans],
  simp [vector.nth_update_nth_of_ne h.symm]
end

lemma rowg_swap' (P : partition m n) (i r : fin m) (s : fin n) :
  (P.swap r s).rowg i = if i = r then P.colg s else P.rowg i :=
if hir : i = r then by simp [hir]
  else by rw [if_neg hir, rowg_swap_of_ne _ hir]

lemma colg_swap' (P : partition m n) (r : fin m) (j s : fin n) :
  (P.swap r s).colg j = if j = s then P.rowg r else P.colg j :=
if hjs : j = s then by simp [hjs]
  else by rw [if_neg hjs, colg_swap_of_ne _ hjs]

@[simp] lemma swap_swap (P : partition m n) (r : fin m) (s : fin n) :
  (P.swap r s).swap r s = P :=
by ext; intros; simp [rowg_swap', colg_swap']; split_ifs; cc

def fin.lastp : fin (m + 1 + n) := fin.cast (add_right_comm _ _ _) (fin.last (m + n))

def fin.castp (v : fin (m + n)) : fin (m + 1 + n) :=
fin.cast (add_right_comm _ _ _) (fin.cast_succ v)

@[simp] lemma fin.castp_ne_lastp (v : fin (m + n)) : (fin.lastp : fin (m + 1 + n)) ≠ fin.castp v :=
ne_of_gt v.2

@[simp] lemma fin.lastp_ne_castp (v : fin (m + n)) : fin.castp v ≠ fin.lastp :=
ne_of_lt v.2

lemma fin.injective_castp : injective (@fin.castp m n) :=
λ ⟨_, _⟩ ⟨_, _⟩, by simp [fin.castp, fin.cast, fin.cast_le, fin.cast_lt, fin.cast_succ]

def add_row (P : partition m n) : partition (m + 1) n :=
{ row_indices := (P.row_indices.map fin.castp).append ⟨[fin.lastp], rfl⟩,
  col_indices := P.col_indices.map (fin.cast (add_right_comm _ _ _) ∘ fin.cast_succ),
  mem_row_indices_or_col_indices := begin
    rintros ⟨v, hv⟩,
    simp only [fin.cast, fin.cast_le, fin.cast_lt, fin.last, vector.to_list_map,
      fin.eq_iff_veq, list.mem_map, fin.cast_le, vector.to_list_append, list.mem_append,
      function.comp, fin.cast_succ, fin.cast_add, fin.exists_iff, and_comm _ (_ = _),
      exists_and_distrib_left, exists_eq_left, fin.lastp, fin.castp],
    by_cases hvmn : v = m + n,
    { simp [hvmn] },
    { have hv : v < m + n, from lt_of_le_of_ne (nat.le_of_lt_succ $ by simpa using hv) hvmn,
      cases P.mem_row_indices_or_col_indices ⟨v, hv⟩; simp * }
  end }

lemma add_row_rowg_last (P : partition m n) : P.add_row.rowg (fin.last m) = fin.lastp :=
have (fin.last m).1 = (P.row_indices.map fin.castp).to_list.length := by simp [fin.last],
option.some_inj.1 $ by simp only [add_row, rowg, vector.nth_eq_nth_le, vector.to_list_append,
  (list.nth_le_nth _).symm, list.nth_concat_length, this, vector.to_list_mk]; refl

lemma add_row_rowg_cast_succ (P : partition m n) (i : fin m) :
  P.add_row.rowg (fin.cast_succ i) = fin.castp (P.rowg i) :=
have i.1 < (P.row_indices.to_list.map fin.castp).length, by simp [i.2],
by simp [add_row, rowg, vector.nth_eq_nth_le, vector.to_list_append,
  (list.nth_le_nth _).symm, list.nth_concat_length, vector.to_list_mk,
  list.nth_le_append _ this, list.nth_le_map]

lemma add_row_colg (P : partition m n) (j : fin n) : P.add_row.colg j = fin.castp (P.colg j) :=
fin.eq_of_veq $ by simp [add_row, colg, vector.nth_eq_nth_le, fin.castp]

def dual (P : partition m n) : partition n m :=
{ row_indices := P.col_indices.map (fin.cast (add_comm _ _)),
  col_indices := P.row_indices.map (fin.cast (add_comm _ _)),
  mem_row_indices_or_col_indices := λ v,
    (P.mem_row_indices_or_col_indices (fin.cast (add_comm _ _) v)).elim
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

@[simp] lemma dual_dual (P : partition m n) : P.dual.dual = P :=
by cases P; simp [dual]; split; ext; simp [fin.eq_iff_veq]

end partition
