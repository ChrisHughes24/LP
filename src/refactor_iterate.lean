import data.matrix.pequiv data.rat.basic tactic.fin_cases data.list.min_max .partition2

open matrix fintype finset function pequiv

local notation `rvec`:2000 n := matrix (fin 1) (fin n) ℚ
local notation `cvec`:2000 m := matrix (fin m) (fin 1) ℚ
local infix ` ⬝ `:70 := matrix.mul
local postfix `ᵀ` : 1500 := transpose

section
universes u v
variables {l m n o : Type u} [fintype l] [fintype m] [fintype n] [fintype o] {R : Type v}

/- Belongs in mathlib -/
lemma mul_right_eq_of_mul_eq [semiring R] {M : matrix l m R} {N : matrix m n R} {O : matrix l n R}
  {P : matrix n o R} (h : M ⬝ N = O) : M ⬝ (N ⬝ P) = O ⬝ P :=
by rw [← matrix.mul_assoc, h]

end

variables {m n : ℕ}

/-- The tableau consists of a matrix and a constant `offset` column.
  `to_partition` stores the indices of the current row and column variables.
  `restricted` is the set of variables that are restricted to be nonnegative  -/
structure tableau (m n : ℕ) :=
(to_matrix : matrix (fin m) (fin n) ℚ)
(offset : cvec m)
(to_partition : partition m n)
(restricted : finset (fin (m + n)))

namespace tableau
open partition

section predicates
variable (T : tableau m n)

/-- The affine subspace represented by the tableau ignoring nonnegativity restrictiions -/
def flat : set (cvec (m + n)) := { x | T.to_partition.rowp.to_matrix ⬝ x =
  T.to_matrix ⬝ T.to_partition.colp.to_matrix ⬝ x + T.offset }

/-- The sol_set is the subset of ℚ^(m+n) that satisifies the tableau -/
def sol_set : set (cvec (m + n)) := flat T ∩ { x | ∀ i, i ∈ T.restricted → 0 ≤ x i 0 }

/-- Predicate for a variable being unbounded above in the `sol_set` -/
def is_unbounded_above (i : fin (m + n)) : Prop :=
  ∀ q : ℚ, ∃ x : cvec (m + n), x ∈ sol_set T ∧ q ≤ x i 0

/-- Predicate for a variable being unbounded below in the `sol_set` -/
def is_unbounded_below (i : fin (m + n)) : Prop :=
  ∀ q : ℚ, ∃ x : cvec (m + n), x ∈ sol_set T ∧ x i 0 ≤ q

def is_maximised (x : cvec (m + n)) (i : fin (m + n)) : Prop :=
∀ y : cvec (m + n), y ∈ sol_set T → y i 0 ≤ x i 0

/-- Is this equivalent to `∀ (x : cvec (m + n)), x ∈ sol_set T → x i 0 = x j 0`? No -/
def equal_in_flat (i j : fin (m + n)) : Prop :=
∀ (x : cvec (m + n)), x ∈ flat T → x i 0 = x j 0

/-- Returns an element of the `flat` after assigning values to the column variables -/
def of_col (T : tableau m n) (x : cvec n) : cvec (m + n) :=
T.to_partition.colp.to_matrixᵀ ⬝ x + T.to_partition.rowp.to_matrixᵀ ⬝
  (T.to_matrix ⬝ x + T.offset)

/-- A `tableau` is feasible if its `offset` column is nonnegative in restricted rows -/
def feasible : Prop :=
∀ i, T.to_partition.rowg i ∈ T.restricted → 0 ≤ T.offset i 0

instance : decidable_pred (@feasible m n) := λ _, by dunfold feasible; apply_instance

/-- Given a row index `r` and a column index `s` it returns a tableau with `r` and `s` switched,
  but with the same `sol_set` -/
def pivot (r : fin m) (c : fin n) : tableau m n :=
let p := (T.to_matrix r c)⁻¹ in
{ to_matrix := λ i j,
    if i = r
      then if j = c
        then p
        else -T.to_matrix r j * p
      else if j = c
        then T.to_matrix i c * p
        else T.to_matrix i j - T.to_matrix i c * T.to_matrix r j * p,
  to_partition := T.to_partition.swap r c,
  offset := λ i k,
    if i = r
      then -T.offset r k * p
      else T.offset i k - T.to_matrix i c * T.offset r k * p,
  restricted := T.restricted }

end predicates

section predicate_lemmas
variable {T : tableau m n}

lemma mem_flat_iff {x : cvec (m + n)} : x ∈ T.flat ↔
  ∀ r, x (T.to_partition.rowg r) 0 = univ.sum
    (λ c : fin n, T.to_matrix r c * x (T.to_partition.colg c) 0) +
  T.offset r 0 :=
have hx : x ∈ T.flat ↔ ∀ i, (T.to_partition.rowp.to_matrix ⬝ x) i 0 =
    (T.to_matrix ⬝ T.to_partition.colp.to_matrix ⬝ x + T.offset) i 0,
  by rw [flat, set.mem_set_of_eq, matrix.ext_iff.symm, forall_swap,
      unique.forall_iff];
    refl,
begin
  rw hx,
  refine forall_congr (λ i, _),
  rw [mul_matrix_apply, add_val, rowp_eq_some_rowg, matrix.mul_assoc, matrix.mul],
  conv in (T.to_matrix _ _ * (T.to_partition.colp.to_matrix ⬝ x) _ _)
  { rw [mul_matrix_apply, colp_eq_some_colg] },
end

variable (T)

@[simp] lemma colp_mul_of_col (x : cvec n) :
  T.to_partition.colp.to_matrix ⬝ of_col T x = x :=
by simp [matrix.mul_assoc, matrix.mul_add, of_col, flat,
    mul_right_eq_of_mul_eq (rowp_mul_colp_transpose _),
    mul_right_eq_of_mul_eq (rowp_mul_rowp_transpose _),
    mul_right_eq_of_mul_eq (colp_mul_colp_transpose _),
    mul_right_eq_of_mul_eq (colp_mul_rowp_transpose _)]

@[simp] lemma rowp_mul_of_col (x : cvec n) :
  T.to_partition.rowp.to_matrix ⬝ of_col T x = T.to_matrix ⬝ x + T.offset :=
by simp [matrix.mul_assoc, matrix.mul_add, of_col, flat,
    mul_right_eq_of_mul_eq (rowp_mul_colp_transpose _),
    mul_right_eq_of_mul_eq (rowp_mul_rowp_transpose _),
    mul_right_eq_of_mul_eq (colp_mul_colp_transpose _),
    mul_right_eq_of_mul_eq (colp_mul_rowp_transpose _)]

lemma of_col_mem_flat (x : cvec n) : T.of_col x ∈ T.flat :=
by simp [matrix.mul_assoc, matrix.mul_add, flat]

@[simp] lemma of_col_colg (x : cvec n) (c : fin n) :
  of_col T x (T.to_partition.colg c) = x c :=
funext $ λ v,
  calc of_col T x (T.to_partition.colg c) v =
      (T.to_partition.colp.to_matrix ⬝ of_col T x) c v :
    by rw [mul_matrix_apply, colp_eq_some_colg]
  ... = x c v : by rw [colp_mul_of_col]

@[simp] lemma of_col_rowg (c : cvec n) (r : fin m) :
  of_col T c (T.to_partition.rowg r) = (T.to_matrix ⬝ c + T.offset) r :=
funext $ λ v,
  calc of_col T c (T.to_partition.rowg r) v =
      (T.to_partition.rowp.to_matrix ⬝ of_col T c) r v :
    by rw [mul_matrix_apply, rowp_eq_some_rowg]
  ... = (T.to_matrix ⬝ c + T.offset) r v : by rw [rowp_mul_of_col]

variable {T}

/-- Condition for the solution given by setting column index `j` to `q` and all other columns to
  zero being in the `sol_set` -/
lemma of_col_single_mem_sol_set {q : ℚ} {c : fin n} (hT : T.feasible)
  (hi : ∀ i, T.to_partition.rowg i ∈ T.restricted → 0 ≤ q * T.to_matrix i c)
  (hj : T.to_partition.colg c ∉ T.restricted ∨ 0 ≤ q) :
  T.of_col (q • (single c 0).to_matrix) ∈ T.sol_set :=
⟨of_col_mem_flat _ _,
  λ v, (T.to_partition.eq_rowg_or_colg v).elim
    begin
      rintros ⟨r, hr⟩ hres,
      subst hr,
      rw [of_col_rowg, add_val, matrix.mul_smul, smul_val, matrix_mul_apply,
        symm_single, single_apply],
      exact add_nonneg (hi _ hres) (hT _ hres)
    end
    begin
      rintros ⟨j, hj⟩ hres,
      subst hj,
      simp [of_col_colg, smul_val, pequiv.single, pequiv.to_matrix],
      by_cases hjc : j = c; simp [*, le_refl] at *
    end⟩

lemma feasible_iff_of_col_zero_mem_sol_set : T.feasible ↔ T.of_col 0 ∈ T.sol_set :=
suffices (∀ i : fin m, T.to_partition.rowg i ∈ T.restricted → 0 ≤ T.offset i 0) ↔
    ∀ v : fin (m + n), v ∈ T.restricted → (0 : ℚ) ≤ T.of_col 0 v 0,
by simpa [sol_set, feasible, of_col_mem_flat],
⟨λ h v hv, (T.to_partition.eq_rowg_or_colg v).elim
    (by rintros ⟨i, hi⟩; subst hi; simp; tauto)
    (by rintros ⟨j, hj⟩; subst hj; simp),
  λ h i hi, by simpa using h _ hi⟩

lemma is_unbounded_above_colg_aux {c : fin n} (hT : T.feasible)
  (h : ∀ i : fin m, T.to_partition.rowg i ∈ T.restricted → 0 ≤ T.to_matrix i c) (q : ℚ):
  of_col T (max q 0 • (single c 0).to_matrix) ∈ sol_set T ∧
    q ≤ of_col T (max q 0 • (single c 0).to_matrix) (T.to_partition.colg c) 0 :=
⟨of_col_single_mem_sol_set hT (λ i hi, mul_nonneg (le_max_right _ _) (h _ hi))
    (or.inr (le_max_right _ _)),
  by simp [of_col_colg, smul_val, pequiv.single, pequiv.to_matrix, le_refl q]⟩

/-- A column variable is unbounded above if it is in a column where every negative entry is
  in a row owned by an unrestricted variable -/
lemma is_unbounded_above_colg {c : fin n} (hT : T.feasible)
  (h : ∀ i : fin m, T.to_partition.rowg i ∈ T.restricted → 0 ≤ T.to_matrix i c) :
  T.is_unbounded_above (T.to_partition.colg c) :=
λ q, ⟨_, is_unbounded_above_colg_aux hT h q⟩

lemma is_unbounded_below_colg_aux {c : fin n} (hT : T.feasible)
  (hres : T.to_partition.colg c ∉ T.restricted)
  (h : ∀ i : fin m, T.to_partition.rowg i ∈ T.restricted → T.to_matrix i c ≤ 0) (q : ℚ) :
  of_col T (min q 0 • (single c 0).to_matrix) ∈ sol_set T ∧
    of_col T (min q 0 • (single c 0).to_matrix) (T.to_partition.colg c) 0 ≤ q :=
⟨of_col_single_mem_sol_set hT
    (λ i hi, mul_nonneg_of_nonpos_of_nonpos (min_le_right _ _) (h _ hi))
    (or.inl hres),
  by simp [of_col_colg, smul_val, pequiv.single, pequiv.to_matrix, le_refl q]⟩

/-- A column variable is unbounded below if it is unrestricted and it is in a column where every
  positive entry is in a row owned by an unrestricted variable -/
lemma is_unbounded_below_colg {c : fin n} (hT : T.feasible)
  (hres : T.to_partition.colg c ∉ T.restricted)
  (h : ∀ i : fin m, T.to_partition.rowg i ∈ T.restricted → T.to_matrix i c ≤ 0) :
  T.is_unbounded_below (T.to_partition.colg c) :=
λ q, ⟨_, is_unbounded_below_colg_aux hT hres h q⟩

/-- A row variable `r` is unbounded above if it is unrestricted and there is a column `s`
  where every restricted row variable has a nonpositive entry in that column, and
  `r` has a negative entry in that column. -/
lemma is_unbounded_above_rowg_of_nonpos {r : fin m} (hT : T.feasible) (s : fin n)
  (hres : T.to_partition.colg s ∉ T.restricted)
  (h : ∀ i : fin m, T.to_partition.rowg i ∈ T.restricted → T.to_matrix i s ≤ 0)
  (his : T.to_matrix r s < 0) : is_unbounded_above T (T.to_partition.rowg r) :=
λ q, ⟨T.of_col (min ((q - T.offset r 0) / T.to_matrix r s) 0 • (single s 0).to_matrix),
  of_col_single_mem_sol_set hT
    (λ i' hi', mul_nonneg_of_nonpos_of_nonpos (min_le_right _ _) (h _ hi'))
    (or.inl hres),
  begin
    rw [of_col_rowg, add_val, matrix.mul_smul, smul_val, matrix_mul_apply,
      symm_single_apply],
    cases le_total 0 ((q - T.offset r 0) / T.to_matrix r s) with hq hq,
    { rw [min_eq_right hq],
      rw [le_div_iff_of_neg his, zero_mul, sub_nonpos] at hq,
      simpa },
    { rw [min_eq_left hq, div_mul_cancel _ (ne_of_lt his)],
      simp }
  end⟩

/-- A row variable `r` is unbounded above if there is a column `s`
  where every restricted row variable has a nonpositive entry in that column, and
  `r` has a positive entry in that column. -/
lemma is_unbounded_above_rowg_of_nonneg {r : fin m} (hT : T.feasible) (s : fin n)
  (hs : ∀ i : fin m, T.to_partition.rowg i ∈ T.restricted → 0 ≤ T.to_matrix i s)
  (his : 0 < T.to_matrix r s) : is_unbounded_above T (T.to_partition.rowg r) :=
λ q, ⟨T.of_col (max ((q - T.offset r 0) / T.to_matrix r s) 0 • (single s 0).to_matrix),
  of_col_single_mem_sol_set hT
    (λ i hi, mul_nonneg (le_max_right _ _) (hs i hi))
    (or.inr (le_max_right _ _)),
  begin
    rw [of_col_rowg, add_val, matrix.mul_smul, smul_val, matrix_mul_apply,
      symm_single_apply],
    cases le_total ((q - T.offset r 0) / T.to_matrix r s) 0 with hq hq,
    { rw [max_eq_right hq],
      rw [div_le_iff his, zero_mul, sub_nonpos] at hq,
      simpa },
    { rw [max_eq_left hq, div_mul_cancel _ (ne_of_gt his)],
      simp }
  end⟩

/-- The sample solution of a feasible tableau maximises the variable in row `r`,
  if every entry in that row is nonpositive and every entry in that row owned by a restricted
  variable is `0`  -/
lemma is_maximised_of_col_zero {r : fin m} (hf : T.feasible)
  (h : ∀ j, T.to_matrix r j ≤ 0 ∧ (T.to_partition.colg j ∉ T.restricted → T.to_matrix r j = 0)) :
  T.is_maximised (T.of_col 0) (T.to_partition.rowg r) :=
λ x hx, begin
  rw [of_col_rowg, matrix.mul_zero, zero_add, mem_flat_iff.1 hx.1],
  refine add_le_of_nonpos_of_le _ (le_refl _),
  refine sum_nonpos (λ j _, _),
  by_cases hj : (T.to_partition.colg j) ∈ T.restricted,
  { refine mul_nonpos_of_nonpos_of_nonneg (h _).1 (hx.2 _ hj) },
  { rw [(h _).2 hj, _root_.zero_mul] }
end

lemma not_maximised_of_unbounded_above {v : fin (m + n)} {x : cvec (m + n)}
  (hu : is_unbounded_above T v) : ¬is_maximised T x v :=
λ hm, let ⟨y, hy⟩ := hu (x v 0 + 1) in
  not_le_of_gt (lt_add_one (x v 0)) (le_trans hy.2 (hm y hy.1))

/-- Expression for the sum of all but one entries in the a row of a tableau. -/
lemma row_sum_erase_eq {x : cvec (m + n)} (hx : x ∈ T.flat) {r : fin m} {s : fin n} :
  (univ.erase s).sum (λ j : fin n, T.to_matrix r j * x (T.to_partition.colg j) 0) =
    x (T.to_partition.rowg r) 0 - T.offset r 0 - T.to_matrix r s * x (colg (T.to_partition) s) 0 :=
begin
  rw [mem_flat_iff] at hx,
  conv_rhs { rw [hx r, ← insert_erase (mem_univ s), sum_insert (not_mem_erase _ _)] },
  simp
end

/-- An expression for a column variable in terms of row variables. -/
lemma colg_eq {x : cvec (m + n)} (hx : x ∈ T.flat) {r : fin m} {s : fin n}
  (hrs : T.to_matrix r s ≠ 0) : x (T.to_partition.colg s) 0 =
    (x (T.to_partition.rowg r) 0
    -(univ.erase s).sum (λ j : fin n, T.to_matrix r j * x (T.to_partition.colg j) 0)
        - T.offset r 0) * (T.to_matrix r s)⁻¹ :=
by simp [row_sum_erase_eq hx, mul_left_comm (T.to_matrix r s)⁻¹, mul_assoc,
    mul_left_comm (T.to_matrix r s), mul_inv_cancel hrs]

/-- Another expression for a column variable in terms of row variables. -/
lemma colg_eq' {x : cvec (m + n)} (hx : x ∈ T.flat) {r : fin m} {s : fin n}
  (hrs : T.to_matrix r s ≠ 0) : x (T.to_partition.colg s) 0 =
  univ.sum (λ (j : fin n), (if j = s then (T.to_matrix r s)⁻¹
    else (-(T.to_matrix r j * (T.to_matrix r s)⁻¹))) *
      x (colg (swap (T.to_partition) r s) j) 0) -
  (T.offset r 0) * (T.to_matrix r s)⁻¹ :=
have (univ.erase s).sum
    (λ j : fin n, ite (j = s) (T.to_matrix r s)⁻¹ (-(T.to_matrix r j * (T.to_matrix r s)⁻¹)) *
      x (colg (swap (T.to_partition) r s) j) 0) =
    (univ.erase s).sum (λ j : fin n,
      -T.to_matrix r j * x (T.to_partition.colg j) 0 * (T.to_matrix r s)⁻¹),
  from finset.sum_congr rfl $ λ j hj,
    by simp [if_neg (mem_erase.1 hj).1, colg_swap_of_ne _ (mem_erase.1 hj).1,
      mul_comm, mul_assoc, mul_left_comm],
by rw [← finset.insert_erase (mem_univ s), finset.sum_insert (not_mem_erase _ _),
    if_pos rfl, colg_swap, colg_eq hx hrs, this, ← finset.sum_mul];
  simp [_root_.add_mul, mul_comm, _root_.mul_add]

/-- Pivoting twice in the same place does nothing -/
@[simp] lemma pivot_pivot {r : fin m} {s : fin n} (hrs : T.to_matrix r s ≠ 0) :
  (T.pivot r s).pivot r s = T :=
begin
  cases T,
  simp [pivot, function.funext_iff],
  split; intros; split_ifs;
  simp [*, mul_assoc, mul_left_comm (T_to_matrix r s), mul_left_comm (T_to_matrix r s)⁻¹,
    mul_comm (T_to_matrix r s), inv_mul_cancel hrs]
end

/- These two sets are equal_in_flat, the stronger lemma is `flat_pivot` -/
private lemma subset_flat_pivot {r : fin m} {s : fin n} (h : T.to_matrix r s ≠ 0) :
  T.flat ⊆ (T.pivot r s).flat :=
λ x hx,
have ∀ i : fin m, (univ.erase s).sum (λ j : fin n,
  ite (j = s) (T.to_matrix i s * (T.to_matrix r s)⁻¹)
    (T.to_matrix i j + -(T.to_matrix i s * T.to_matrix r j * (T.to_matrix r s)⁻¹))
      * x ((T.to_partition.swap r s).colg j) 0) =
  (univ.erase s).sum (λ j : fin n, T.to_matrix i j * x (T.to_partition.colg j) 0 -
    T.to_matrix r j *
      x (T.to_partition.colg j) 0 * T.to_matrix i s * (T.to_matrix r s)⁻¹),
  from λ i, finset.sum_congr rfl (λ j hj,
    by rw [if_neg (mem_erase.1 hj).1, colg_swap_of_ne _ (mem_erase.1 hj).1];
      simp [mul_add, add_mul, mul_comm, mul_assoc, mul_left_comm]),
begin
  rw mem_flat_iff,
  assume i,
  by_cases hir : i = r,
  { rw eq_comm at hir,
    subst hir,
    dsimp [pivot],
    simp [mul_inv_cancel h, neg_mul_eq_neg_mul_symm, if_true,
      add_comm, mul_inv_cancel, rowg_swap, eq_self_iff_true, colg_eq' hx h],
    congr, funext, congr },
  { dsimp [pivot],
    simp only [if_neg hir],
    rw [← insert_erase (mem_univ s), sum_insert (not_mem_erase _ _),
      if_pos rfl, colg_swap, this, sum_sub_distrib, ← sum_mul, ← sum_mul,
      row_sum_erase_eq hx, rowg_swap_of_ne _ hir],
    simp [row_sum_erase_eq hx, mul_add, add_mul,
      mul_comm, mul_left_comm, mul_assoc],
    simp [mul_assoc, mul_left_comm (T.to_matrix r s), mul_left_comm (T.to_matrix r s)⁻¹,
      mul_comm (T.to_matrix r s), inv_mul_cancel h] }
end

variable (T)

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

@[simp] lemma offset_pivot_row {r : fin m} {s : fin n} : (T.pivot r s).offset r 0 =
  -T.offset r 0 / T.to_matrix r s :=
by simp [pivot, if_pos rfl, div_eq_mul_inv]

@[simp] lemma offset_pivot_of_ne {i r : fin m} {s : fin n} (hir : i ≠ r) : (T.pivot r s).offset i 0
  = T.offset i 0 - T.to_matrix i s * T.offset r 0 / T.to_matrix r s :=
by dsimp [pivot]; rw [if_neg hir, div_eq_mul_inv]

@[simp] lemma restricted_pivot (r s) : (T.pivot r s).restricted = T.restricted := rfl

@[simp] lemma to_partition_pivot (r s) : (T.pivot r s).to_partition = T.to_partition.swap r s := rfl

variable {T}

@[simp] lemma flat_pivot {r : fin m} {s : fin n} (hrs : T.to_matrix r s ≠ 0) :
  (T.pivot r s).flat = T.flat :=
set.subset.antisymm
  (by conv_rhs { rw ← pivot_pivot hrs };
    exact subset_flat_pivot (by simp [hrs]))
  (subset_flat_pivot hrs)

@[simp] lemma sol_set_pivot {r : fin m} {s : fin n} (hrs : T.to_matrix r s ≠ 0) :
  (T.pivot r s).sol_set = T.sol_set :=
by rw [sol_set, flat_pivot hrs]; refl

-- lemma feasible_pivot (hTf : T.feasible) {r : fin m} {s : fin n}
--   (hs : T.to_partition.colg s ∈ T.restricted → T.offset r 0 / T.to_matrix r s ≤ 0)
--   (h : ∀ i : fin m, i ≠ r → T.to_partition.rowg i ∈ T.restricted →
--     0 ≤ T.offset i 0 - T.to_matrix i s * T.offset r 0 / T.to_matrix r s) :
--   (T.pivot r s).feasible :=
-- assume i hi,
-- if hir : i = r
--   then begin
--     subst hir,
--     rw [offset_pivot_row],
--     simp at *,
--   end
--   else begin
--     rw [to_partition_pivot, rowg_swap_of_ne _ hir, restricted_pivot] at hi,
--     rw [offset_pivot_of_ne _ hir, sub_nonneg, mul_div_assoc],
--     sorry

--   end

/-- Two row variables are `equal_in_flat` iff the corresponding rows of the tableau are equal -/
lemma equal_in_flat_row_row {i i' : fin m} :
  T.equal_in_flat (T.to_partition.rowg i) (T.to_partition.rowg i')
  ↔ (T.offset i 0 = T.offset i' 0 ∧ ∀ j : fin n, T.to_matrix i j = T.to_matrix i' j) :=
⟨λ h, have Hoffset : T.offset i 0 = T.offset i' 0,
    by simpa [of_col_rowg] using h (T.of_col 0) (of_col_mem_flat _ _),
  ⟨Hoffset,
    λ j, begin
      have := h (T.of_col (single j (0 : fin 1)).to_matrix) (of_col_mem_flat _ _),
      rwa [of_col_rowg, of_col_rowg, add_val, add_val, matrix_mul_apply, matrix_mul_apply,
        symm_single_apply, Hoffset, add_right_cancel_iff] at this,
    end⟩,
λ h x hx, by simp [mem_flat_iff.1 hx, h.1, h.2]⟩

/-- A row variable is equal_in_flat to a column variable iff its row has zeros, and a single
  one in that column. -/
lemma equal_in_flat_row_col {i : fin m} {j : fin n} :
  T.equal_in_flat (T.to_partition.rowg i) (T.to_partition.colg j)
  ↔ (∀ j', j' ≠ j → T.to_matrix i j' = 0) ∧ T.offset i 0 = 0 ∧ T.to_matrix i j = 1 :=
⟨λ h, have Hoffset : T.offset i 0 = 0,
    by simpa using h (T.of_col 0) (of_col_mem_flat _ _),
  ⟨assume j' hj', begin
      have := h (T.of_col (single j' (0 : fin 1)).to_matrix) (of_col_mem_flat _ _),
      rwa [of_col_rowg, of_col_colg, add_val, Hoffset, add_zero, matrix_mul_apply,
        symm_single_apply, pequiv.to_matrix, single_apply_of_ne hj',
        if_neg (option.not_mem_none _)] at this
    end,
  Hoffset,
  begin
    have := h (T.of_col (single j (0 : fin 1)).to_matrix) (of_col_mem_flat _ _),
    rwa [of_col_rowg, of_col_colg, add_val, Hoffset, add_zero, matrix_mul_apply,
        symm_single_apply, pequiv.to_matrix, single_apply] at this
  end⟩,
by rintros ⟨h₁, h₂, h₃⟩ x hx;
  rw [mem_flat_iff.1 hx, h₂, sum_eq_single j]; simp *; tauto⟩

end predicate_lemmas

/-- Conditions for unboundedness based on reading the tableau. The conditions are equivalent to the
  simplex pivot rule failing to find a pivot row. -/
lemma unbounded_of_tableau {T : tableau m n} {obj : fin m} {c : fin n} (hT : T.feasible)
  (hrow : ∀ r, obj ≠ r → T.to_partition.rowg r ∈ T.restricted →
    0 ≤ T.to_matrix obj c / T.to_matrix r c)
  (hc : (T.to_matrix obj c ≠ 0 ∧ T.to_partition.colg c ∉ T.restricted)
    ∨ (0 < T.to_matrix obj c ∧ T.to_partition.colg c ∈ T.restricted)) :
  T.is_unbounded_above (T.to_partition.rowg obj) :=
have hToc : T.to_matrix obj c ≠ 0, from λ h, by simpa [h, lt_irrefl] using hc,
(lt_or_gt_of_ne hToc).elim
  (λ hToc : T.to_matrix obj c < 0, is_unbounded_above_rowg_of_nonpos hT c
    (hc.elim and.right (λ h, (not_lt_of_gt hToc h.1).elim))
    (λ i hi, classical.by_cases
      (λ hoi : obj = i, le_of_lt (hoi ▸ hToc))
      (λ hoi : obj ≠ i, inv_nonpos.1 $ nonpos_of_mul_nonneg_right (hrow _ hoi hi) hToc))
    hToc)
  (λ hToc : 0 < T.to_matrix obj c, is_unbounded_above_rowg_of_nonneg hT c
    (λ i hi, classical.by_cases
      (λ hoi : obj = i, le_of_lt (hoi ▸ hToc))
      (λ hoi : obj ≠ i, inv_nonneg.1 $ nonneg_of_mul_nonneg_left (hrow _ hoi hi) hToc))
    hToc)

/-- Conditions for the tableau being feasible, that must be satisified by a simplex pivot rule -/
lemma feasible_pivot {T : tableau m n} {obj : fin m} (hT : T.feasible) {r c}
  (hres : rowg (T.to_partition) r ∈ T.restricted)
  (hrneg : T.to_matrix obj c / T.to_matrix r c < 0)
  (hrmin : ∀ (r' : fin m), obj ≠ r' → rowg (T.to_partition) r' ∈ T.restricted →
          T.to_matrix obj c / T.to_matrix r' c < 0 →
          abs (T.offset r 0 / T.to_matrix r c) ≤ abs (T.offset r' 0 / T.to_matrix r' c))
  (hc : T.to_matrix obj c ≠ 0 ∧ colg (T.to_partition) c ∉ T.restricted ∨ 0 < T.to_matrix obj c) :
  (T.pivot r c).feasible :=
begin
  assume i hi,
  dsimp only [pivot],
  by_cases hir : i = r,
  { subst i,
    rw [if_pos rfl, neg_mul_eq_neg_mul_symm, neg_nonneg],
    exact mul_nonpos_of_nonneg_of_nonpos (hT _ hres)
      (le_of_lt (neg_of_mul_neg_left hrneg (le_of_lt (by simp * at *)))) },
  { rw if_neg hir,
    rw [to_partition_pivot, rowg_swap_of_ne _ hir, restricted_pivot] at hi,
    by_cases hobji : obj = i,
    { subst i,
      refine add_nonneg (hT _ hi) (neg_nonneg.2 _),
      rw [mul_assoc, mul_left_comm],
      exact mul_nonpos_of_nonneg_of_nonpos (hT _ hres) (le_of_lt hrneg) },
    { by_cases hTir : 0 < T.to_matrix i c / T.to_matrix r c,
      { have hTic0 : T.to_matrix i c ≠ 0, from λ h, by simpa [h, lt_irrefl] using hTir,
        have hTrc0 : T.to_matrix r c ≠ 0, from λ h, by simpa [h, lt_irrefl] using hTir,
        have hTobji : T.to_matrix obj c / T.to_matrix i c < 0,
        { suffices : (T.to_matrix obj c / T.to_matrix r c) / (T.to_matrix i c / T.to_matrix r c) < 0,
          { simp only [div_eq_mul_inv, mul_assoc, mul_inv', inv_inv',
              mul_left_comm (T.to_matrix r c), mul_left_comm (T.to_matrix r c)⁻¹,
              mul_comm (T.to_matrix r c), inv_mul_cancel hTrc0, mul_one] at this,
            simpa [mul_comm, div_eq_mul_inv] },
        { exact div_neg_of_neg_of_pos hrneg hTir } },
        have := hrmin _ hobji hi hTobji,
        rwa [abs_div, abs_div, abs_of_nonneg (hT _ hres), abs_of_nonneg (hT _ hi),
          le_div_iff (abs_pos_iff.2 hTic0), div_eq_mul_inv, mul_right_comm, ← abs_inv, mul_assoc,
          ← abs_mul, ← div_eq_mul_inv, abs_of_nonneg (le_of_lt hTir), ← sub_nonneg,
          ← mul_div_assoc, div_eq_mul_inv, mul_comm (T.offset r 0)] at this },
      { refine add_nonneg (hT _ hi) (neg_nonneg.2 _),
        rw [mul_assoc, mul_left_comm],
        exact mul_nonpos_of_nonneg_of_nonpos (hT _ hres) (le_of_not_gt hTir) } } }
end

-- /-- Conditions for maximality of the sample solution based on reading the tableau. The conditions
--   are equivalent to the simplex pivot rule failing to find a pivot column. -/
-- lemma is_maximised_of_col_zero_of_tableau {T : tableau m n} {obj : fin m} (hT : T.feasible)
--   (h : ∀ s, (T.to_matrix obj s = 0 ∨ colg (T.to_partition) s ∈ T.restricted) ∧
--       (T.to_matrix obj s ≤ 0 ∨ colg (T.to_partition) s ∉ T.restricted)) :
--   T.is_maximised (T.of_col 0) (T.to_partition.rowg obj) :=
-- is_maximis

-- /-- definition used to define well-foundedness of a pivot rule -/
-- inductive rel_gen {α : Type*} (f : α → option α) : α → α → Prop
-- | of_mem : ∀ {x y}, x ∈ f y → rel_gen x y
-- | trans : ∀ {x y z}, rel_gen x y → rel_gen y z → rel_gen x z

-- /-- A pivot rule is a function that selects a nonzero pivot, given a tableau, such that
--   iterating using this pivot rule terminates. -/
-- structure pivot_rule (m n : ℕ) : Type :=
-- (pivot_indices : tableau m n → option (fin m × fin n))
-- (well_founded : well_founded (rel_gen (λ T, pivot_indices T >>= λ i, T.pivot i.1 i.2)))
-- (ne_zero : ∀ {T r s}, (r, s) ∈ pivot_indices T → T.to_matrix r s ≠ 0)

-- def pivot_rule.rel (p : pivot_rule m n) : tableau m n → tableau m n → Prop :=
-- rel_gen (λ T, p.pivot_indices T >>= λ i, T.pivot i.1 i.2)

-- lemma pivot_rule.rel_wf (p : pivot_rule m n) : well_founded p.rel := p.well_founded

-- def iterate (p : pivot_rule m n) : tableau m n → tableau m n
-- | T :=
-- have ∀ (r : fin m) (s : fin n), (r, s) ∈ p.pivot_indices T → p.rel (T.pivot r s) T,
--   from λ r s hrs, rel_gen.of_mem $ by rw option.mem_def.1 hrs; exact rfl,
-- option.cases_on (p.pivot_indices T) (λ _, T)
--   (λ i this,
--     have wf : p.rel (T.pivot i.1 i.2) T, from this _ _ (by cases i; exact rfl),
--     iterate (T.pivot i.1 i.2))
--   this
-- using_well_founded { rel_tac := λ _ _, `[exact ⟨_, p.rel_wf⟩],
--   dec_tac := tactic.assumption }

-- lemma iterate_pivot {p : pivot_rule m n} {T : tableau m n} {r : fin m} {s : fin n}
--   (hrs : (r, s) ∈ p.pivot_indices T) : (T.pivot r s).iterate p = T.iterate p :=
-- by conv_rhs {rw iterate}; simp [option.mem_def.1 hrs]

-- @[simp] lemma pivot_indices_iterate (p : pivot_rule m n) : ∀ (T : tableau m n),
--   p.pivot_indices (T.iterate p) = none
-- | T :=
-- have ∀ r s, (r, s) ∈ p.pivot_indices T → p.rel (T.pivot r s) T,
--   from λ r s hrs, rel_gen.of_mem $ by rw option.mem_def.1 hrs; exact rfl,
-- begin
--   rw iterate,
--   cases h : p.pivot_indices T with i,
--   { simp [h] },
--   { cases i with r s,
--     simp [h, pivot_indices_iterate (T.pivot r s)] }
-- end
-- using_well_founded { rel_tac := λ _ _, `[exact ⟨_, p.rel_wf⟩], dec_tac := `[tauto] }

-- /- Is there some nice elaborator attribute for this, to avoid `P` having to be explicit? -/
-- lemma iterate_induction_on (P : tableau m n → Prop) (p : pivot_rule m n) :
--   ∀ T : tableau m n, P T → (∀ T' r s, P T' → (r, s) ∈ p.pivot_indices T'
--     → P (T'.pivot r s)) → P (T.iterate p)
-- | T := λ hT ih,
-- have ∀ r s, (r, s) ∈ p.pivot_indices T → p.rel (T.pivot r s) T,
--   from λ r s hrs, rel_gen.of_mem $ by rw option.mem_def.1 hrs; exact rfl,
-- begin
--   rw iterate,
--   cases h : p.pivot_indices T with i,
--   { simp [hT, h] },
--   { cases i with r s,
--     simp [h, iterate_induction_on _ (ih _ _ _ hT h) ih] }
-- end
-- using_well_founded { rel_tac := λ _ _, `[exact ⟨_, p.rel_wf⟩], dec_tac := `[tauto] }

-- @[simp] lemma iterate_flat (p : pivot_rule m n) (T : tableau m n) :
--   (T.iterate p).flat = T.flat :=
-- iterate_induction_on (λ T', T'.flat = T.flat) p T rfl $
--   assume T' r s (hT' : T'.flat = T.flat) hrs, by rw [← hT', flat_pivot (p.ne_zero hrs)]

-- @[simp] lemma iterate_sol_set (p : pivot_rule m n) (T : tableau m n) :
--   (T.iterate p).sol_set = T.sol_set :=
-- iterate_induction_on (λ T', T'.sol_set = T.sol_set) p T rfl $
--   assume T' r s (hT' : T'.sol_set = T.sol_set) hrs,
--     by rw [← hT', sol_set_pivot (p.ne_zero hrs)]

namespace simplex

def find_pivot_column (T : tableau m n) (obj : fin m) : option (fin n) :=
option.cases_on (fin.find (λ c : fin n, T.to_matrix obj c ≠ 0 ∧ T.to_partition.colg c ∉ T.restricted))
  (fin.find (λ c : fin n, 0 < T.to_matrix obj c))
  some

def find_pivot_row (T : tableau m n) (obj: fin m) (c : fin n) : option (fin m) :=
let l := (list.fin_range m).filter (λ r : fin m, obj ≠ r ∧ T.to_partition.rowg r ∈ T.restricted
  ∧ T.to_matrix obj c / T.to_matrix r c < 0) in
l.argmin (λ r', abs (T.offset r' 0 / T.to_matrix r' c))

lemma find_pivot_column_spec {T : tableau m n} {obj : fin m} {s : fin n} :
  s ∈ find_pivot_column T obj → (T.to_matrix obj s ≠ 0 ∧ T.to_partition.colg s ∉ T.restricted)
  ∨ (0 < T.to_matrix obj s ∧ T.to_partition.colg s ∈ T.restricted) :=
begin
  simp [find_pivot_column],
  cases h : fin.find (λ s : fin n, T.to_matrix obj s ≠ 0 ∧ T.to_partition.colg s ∉ T.restricted),
  { finish [h, fin.find_eq_some_iff, fin.find_eq_none_iff, lt_irrefl (0 : ℚ)] },
  { finish [fin.find_eq_some_iff] }
end

lemma find_pivot_column_eq_none {T : tableau m n} {obj : fin m} (hT : T.feasible)
  (h : find_pivot_column T obj = none) : T.is_maximised (T.of_col 0) (T.to_partition.rowg obj) :=
is_maximised_of_col_zero hT
begin
  revert h,
  simp [find_pivot_column],
  cases h : fin.find (λ c : fin n, T.to_matrix obj c ≠ 0 ∧ T.to_partition.colg c ∉ T.restricted),
  { finish [fin.find_eq_none_iff] },
  { simp [h] }
end

lemma find_pivot_row_spec {T : tableau m n} {obj r : fin m} {c : fin n} :
  r ∈ find_pivot_row T obj c →
  obj ≠ r ∧ T.to_partition.rowg r ∈ T.restricted ∧
  T.to_matrix obj c / T.to_matrix r c < 0 ∧
  (∀ r' : fin m, obj ≠ r' → T.to_partition.rowg r' ∈ T.restricted →
    T.to_matrix obj c / T.to_matrix r' c < 0 →
  abs (T.offset r 0 / T.to_matrix r c) ≤ abs (T.offset r' 0 / T.to_matrix r' c)) :=
by simp only [list.mem_argmin_iff, list.mem_filter, find_pivot_row,
    list.mem_fin_range, true_and, and_imp]; tauto

lemma find_pivot_row_eq_none_aux {T : tableau m n} {obj : fin m} {c : fin n}
  (hrow : find_pivot_row T obj c = none) (hs : c ∈ find_pivot_column T obj) :
  ∀ r, obj ≠ r → T.to_partition.rowg r ∈ T.restricted → 0 ≤ T.to_matrix obj c / T.to_matrix r c :=
by simpa [find_pivot_row, list.filter_eq_nil] using hrow

lemma find_pivot_row_eq_none {T : tableau m n} {obj : fin m} {c : fin n} (hT : T.feasible)
  (hrow : find_pivot_row T obj c = none) (hs : c ∈ find_pivot_column T obj) :
  T.is_unbounded_above (T.to_partition.rowg obj) :=
have hrow : ∀ r, obj ≠ r → T.to_partition.rowg r ∈ T.restricted →
    0 ≤ T.to_matrix obj c / T.to_matrix r c,
  from find_pivot_row_eq_none_aux hrow hs,
have hc : (T.to_matrix obj c ≠ 0 ∧ T.to_partition.colg c ∉ T.restricted)
    ∨ (0 < T.to_matrix obj c ∧ T.to_partition.colg c ∈ T.restricted),
  from find_pivot_column_spec hs,
have hToc : T.to_matrix obj c ≠ 0, from λ h, by simpa [h, lt_irrefl] using hc,
(lt_or_gt_of_ne hToc).elim
  (λ hToc : T.to_matrix obj c < 0, is_unbounded_above_rowg_of_nonpos hT c
    (hc.elim and.right (λ h, (not_lt_of_gt hToc h.1).elim))
    (λ i hi, classical.by_cases
      (λ hoi : obj = i, le_of_lt (hoi ▸ hToc))
      (λ hoi : obj ≠ i, inv_nonpos.1 $ nonpos_of_mul_nonneg_right (hrow _ hoi hi) hToc))
    hToc)
  (λ hToc : 0 < T.to_matrix obj c, is_unbounded_above_rowg_of_nonneg hT c
    (λ i hi, classical.by_cases
      (λ hoi : obj = i, le_of_lt (hoi ▸ hToc))
      (λ hoi : obj ≠ i, inv_nonneg.1 $ nonneg_of_mul_nonneg_left (hrow _ hoi hi) hToc))
    hToc)

def feasible_of_mem_pivot_row_and_column {T : tableau m n} {obj : fin m} (hT : T.feasible) {c}
  (hc : c ∈ find_pivot_column T obj) {r} (hr : r ∈ find_pivot_row T obj c) :
  feasible (T.pivot r c) :=
begin
  have := find_pivot_column_spec hc,
  have := find_pivot_row_spec hr,
  have := @feasible_pivot _ _ _ obj hT r c,
  tauto
end

inductive termination : Type
| while     : termination
| unbounded : termination
| maximised : termination

instance termination.decidable_eq : decidable_eq termination := by tactic.mk_dec_eq_instance

instance : has_repr termination := ⟨λ t, termination.cases_on t "while" "unbounded" "maximised"⟩

end simplex

open simplex simplex.termination

/-- The simplex algorithm -/
def simplex (w : tableau m n → bool) : Π (T : tableau m n) (hT : feasible T) (obj : fin m),
  tableau m n × termination
| T hT obj := cond (w T)
  (match find_pivot_column T obj, @feasible_of_mem_pivot_row_and_column _ _ _ obj hT with
    | none,   hc := (T, maximised)
    | some c, hc :=
      match find_pivot_row T obj c, @hc _ rfl with
      | none,   hr := (T, unbounded)
      | some r, hr := have wf : tableau.sizeof m n (pivot T r c) < tableau.sizeof m n T, from sorry,
        simplex (T.pivot r c) (hr rfl) obj
      end
    end)
  (T, while)

namespace simplex

lemma simplex_pivot {w : tableau m n → bool} {T : tableau m n} (hT : feasible T)
  (hw : w T = tt) {obj : fin m} {r : fin m} {c : fin n}
  (hc : c ∈ find_pivot_column T obj) (hr : r ∈ find_pivot_row T obj c) :
  (T.pivot r c).simplex w (feasible_of_mem_pivot_row_and_column hT hc hr) obj =
  T.simplex w hT obj :=
by conv_rhs { rw simplex };
  simp [hw, show _ = _, from hr, show _ = _, from hc, _match_1, _match_2]

lemma simplex_spec_aux (w : tableau m n → bool) : Π (T : tableau m n) (hT : feasible T)
  (obj : fin m),
  ((T.simplex w hT obj).2 = while ∧ w (T.simplex w hT obj).1 = ff) ∨
  ((T.simplex w hT obj).2 = maximised ∧ w (T.simplex w hT obj).1 = tt ∧
    find_pivot_column (T.simplex w hT obj).1 obj = none) ∨
  ((T.simplex w hT obj).2 = unbounded ∧ w (T.simplex w hT obj).1 = tt ∧
    ∃ c, c ∈ find_pivot_column (T.simplex w hT obj).1 obj ∧
    find_pivot_row (T.simplex w hT obj).1 obj c = none)
| T hT obj :=
  begin
    cases hw : w T,
    { rw simplex, simp [hw] },
    { cases hc : find_pivot_column T obj with c,
      { rw simplex, simp [hc, hw, _match_1] },
      { cases hr : find_pivot_row T obj c with r,
        { rw simplex, simp [hr, hc, hw, _match_1, _match_2] },
        { rw [← simplex_pivot hT hw hc hr],
          exact have wf : tableau.sizeof m n (pivot T r c) < tableau.sizeof m n T, from sorry,
            simplex_spec_aux _ _ _ } } }
  end

lemma simplex_while_eq_ff {w : tableau m n → bool} {T : tableau m n} {hT : feasible T}
  {obj : fin m} (hw : w T = ff) : T.simplex w hT obj = (T, while) :=
by rw [simplex, hw]; refl

lemma simplex_find_pivot_column_eq_none {w : tableau m n → bool} {T : tableau m n} {hT : feasible T}
  (hw : w T = tt) {obj : fin m} (hc : find_pivot_column T obj = none) :
  T.simplex w hT obj = (T, maximised) :=
by rw simplex; simp [hc, hw, _match_1]

lemma simplex_find_pivot_row_eq_none {w : tableau m n → bool} {T : tableau m n} {hT : feasible T}
  {obj : fin m} (hw : w T = tt) {c} (hc : c ∈ find_pivot_column T obj)
  (hr : find_pivot_row T obj c = none) : T.simplex w hT obj = (T, unbounded) :=
by rw simplex; simp [hw, show _ = _, from hc, hr, _match_1, _match_2]

lemma simplex_induction (P : tableau m n → Prop) (w : tableau m n → bool) : Π {T : tableau m n}
  (hT : feasible T) (obj : fin m) (h0 : P T)
  (hpivot : ∀ {T' r c}, w T' = tt → c ∈ find_pivot_column T' obj → r ∈ find_pivot_row T' obj c
    → feasible T' → P T' → P (T'.pivot r c)),
  P (simplex w T hT obj).1
| T hT obj h0 hpivot :=
  begin
    cases hw : w T,
    { rwa [simplex_while_eq_ff hw] },
    { cases hc : find_pivot_column T obj with c,
      { rwa [simplex_find_pivot_column_eq_none hw hc] },
      { cases hr : find_pivot_row T obj c with r,
        { rwa simplex_find_pivot_row_eq_none hw hc hr },
        { rw [← simplex_pivot _ hw hc hr],
          exact have wf : tableau.sizeof m n (pivot T r c) < tableau.sizeof m n T, from sorry,
            simplex_induction (feasible_of_mem_pivot_row_and_column hT hc hr) _
              (hpivot hw hc hr hT h0) @hpivot } } }
  end

lemma feasible_simplex {w : tableau m n → bool} {T : tableau m n}
  {hT : feasible T} {obj : fin m} : feasible (T.simplex w hT obj).1 :=
simplex_induction feasible _ hT _ hT
  (λ _ _ _ _ hc hr _ hT', feasible_of_mem_pivot_row_and_column hT' hc hr)

lemma simplex_simplex {w : tableau m n → bool} {T : tableau m n} {hT : feasible T} {obj : fin m} :
  (T.simplex w hT obj).1.simplex w feasible_simplex obj = T.simplex w hT obj :=
simplex_induction (λ T', ∀ (hT' : feasible T'), T'.simplex w hT' obj = T.simplex w hT obj) w _ _
  (λ _, rfl) (λ T' r c hw hc hr hT' ih hpivot, by rw [simplex_pivot hT' hw hc hr, ih]) _

/-- `simplex` does not move the row variable it is trying to maximise. -/
@[simp] lemma rowg_simplex (T : tableau m n) (hT : feasible T) (w : tableau m n → bool)
  (obj : fin m) : (T.simplex w hT obj).1.to_partition.rowg obj = T.to_partition.rowg obj :=
simplex_induction (λ T', T'.to_partition.rowg obj = T.to_partition.rowg obj) _ _ _ rfl
  (λ T' r c hw hc hr, by simp [rowg_swap_of_ne _ (find_pivot_row_spec hr).1])

@[simp] lemma flat_simplex (T : tableau m n) (hT : feasible T) (w : tableau m n → bool)
  (obj : fin m) : (T.simplex w hT obj).1.flat = T.flat :=
simplex_induction (λ T', T'.flat = T.flat) w _ obj rfl
  (λ T' r c hw hc hr hT' ih,
    have T'.to_matrix r c ≠ 0,
      from λ h, by simpa [h, lt_irrefl] using find_pivot_row_spec hr,
    by rw [flat_pivot this, ih])

@[simp] lemma restricted_simplex (T : tableau m n) (hT : feasible T) (w : tableau m n → bool)
  (obj : fin m) : (T.simplex w hT obj).1.restricted = T.restricted :=
simplex_induction (λ T', T'.restricted = T.restricted) _ _ _ rfl (by simp { contextual := tt })

@[simp] lemma sol_set_simplex (T : tableau m n) (hT : feasible T) (w : tableau m n → bool)
  (obj : fin m) : (T.simplex w hT obj).1.sol_set = T.sol_set :=
by simp [sol_set]

@[simp] lemma is_unbounded_above_simplex {T : tableau m n} {hT : feasible T} {w : tableau m n → bool}
  {obj : fin m} {v : fin (m + n)} : is_unbounded_above (T.simplex w hT obj).1 v ↔
  is_unbounded_above T v := by simp [is_unbounded_above]

@[simp] lemma is_maximised_simplex {T : tableau m n} {hT : feasible T} {w : tableau m n → bool}
  {obj : fin m} {x : cvec (m + n)} {v : fin (m + n)} : is_maximised (T.simplex w hT obj).1 x v ↔
  is_maximised T x v := by simp [is_maximised]

lemma termination_eq_while_iff {T : tableau m n} {hT : feasible T} {w : tableau m n → bool}
  {obj : fin m} : (T.simplex w hT obj).2 = while ↔ w (T.simplex w hT obj).1 = ff :=
by have := simplex_spec_aux w T hT obj; finish

lemma termination_eq_maximised_iff_find_pivot_column_eq_none {T : tableau m n}
  {hT : feasible T} {w : tableau m n → bool} {obj : fin m} : (T.simplex w hT obj).2 = maximised ↔
  w (T.simplex w hT obj).1 = tt ∧ find_pivot_column (T.simplex w hT obj).1 obj = none :=
by have := simplex_spec_aux w T hT obj; finish

lemma termination_eq_unbounded_iff_find_pivot_row_eq_none {T : tableau m n} {hT : feasible T}
  {w : tableau m n → bool} {obj : fin m} : (T.simplex w hT obj).2 = unbounded ↔
  w (T.simplex w hT obj).1 = tt ∧ ∃ c, c ∈ find_pivot_column (T.simplex w hT obj).1 obj ∧
  find_pivot_row (T.simplex w hT obj).1 obj c = none :=
by have := simplex_spec_aux w T hT obj; finish

lemma termination_eq_unbounded_iff_aux {T : tableau m n} {hT : feasible T}
  {w : tableau m n → bool} {obj : fin m} : (T.simplex w hT obj).2 = unbounded →
  w (T.simplex w hT obj).1 = tt ∧
  is_unbounded_above T (T.to_partition.rowg obj) :=
begin
  rw termination_eq_unbounded_iff_find_pivot_row_eq_none,
  rintros ⟨_, c, hc⟩,
  simpa * using find_pivot_row_eq_none feasible_simplex hc.2 hc.1
end

lemma termination_eq_maximised_iff {T : tableau m n} {hT : feasible T}
  {w : tableau m n → bool} {obj : fin m} : (T.simplex w hT obj).2 = maximised ↔
  w (T.simplex w hT obj).1 = tt ∧
  is_maximised T ((T.simplex w hT obj).1.of_col 0) (T.to_partition.rowg obj) :=
begin
  rw [termination_eq_maximised_iff_find_pivot_column_eq_none],
  split,
  { rintros ⟨_, hc⟩,
    simpa * using find_pivot_column_eq_none feasible_simplex hc },
  { cases ht : (T.simplex w hT obj).2,
    { simp [*, termination_eq_while_iff] at * },
    { cases termination_eq_unbounded_iff_aux ht,
      simp [*, not_maximised_of_unbounded_above right] },
    { simp [*, termination_eq_maximised_iff_find_pivot_column_eq_none] at * } }
end

lemma termination_eq_unbounded_iff {T : tableau m n} {hT : feasible T}
  {w : tableau m n → bool} {obj : fin m} : (T.simplex w hT obj).2 = unbounded ↔
  w (T.simplex w hT obj).1 = tt ∧ is_unbounded_above T (T.to_partition.rowg obj) :=
⟨termination_eq_unbounded_iff_aux,
  begin
    have := @not_maximised_of_unbounded_above m n (T.simplex w hT obj).1 (T.to_partition.rowg obj)
      ((T.simplex w hT obj).1.of_col 0),
    cases ht : (T.simplex w hT obj).2;
    simp [termination_eq_maximised_iff, termination_eq_while_iff, *] at *
  end⟩

end simplex

section add_row

/-- adds a new row without making it a restricted variable. -/
def add_row (T : tableau m n) (fac : rvec (m + n)) (const : ℚ) : tableau (m + 1) n :=
{ to_matrix := λ i j, if hm : i.1 < m
    then T.to_matrix (fin.cast_lt i hm) j
    else fac 0 (T.to_partition.colg j) +
      univ.sum (λ i' : fin m, fac 0 (T.to_partition.rowg i') * T.to_matrix i' j),
  offset := λ i j, if hm : i.1 < m
    then T.offset (fin.cast_lt i hm) j
    else const +
      univ.sum (λ i' : fin m, fac 0 (T.to_partition.rowg i') * T.offset i' 0),
  to_partition := T.to_partition.add_row,
  restricted := T.restricted.map ⟨fin.castp,
    λ ⟨_, _⟩ ⟨_, _⟩ h, fin.eq_of_veq (fin.veq_of_eq h : _)⟩ }

@[simp] lemma add_row_to_partition (T : tableau m n) (fac : rvec (m + n)) (const : ℚ) :
  (T.add_row fac const).to_partition = T.to_partition.add_row := rfl

lemma add_row_to_matrix (T : tableau m n) (fac : rvec (m + n)) (const : ℚ) :
  (T.add_row fac const).to_matrix = λ i j, if hm : i.1 < m
    then T.to_matrix (fin.cast_lt i hm) j else fac 0 (T.to_partition.colg j) +
      univ.sum (λ i' : fin m, fac 0 (T.to_partition.rowg i') * T.to_matrix i' j) := rfl

lemma add_row_offset (T : tableau m n) (fac : rvec (m + n)) (const : ℚ) :
  (T.add_row fac const).offset = λ i j, if hm : i.1 < m
    then T.offset (fin.cast_lt i hm) j else const +
    univ.sum (λ i' : fin m, fac 0 (T.to_partition.rowg i') * T.offset i' 0) := rfl

lemma add_row_restricted (T : tableau m n) (fac : rvec (m + n)) (const : ℚ) :
  (T.add_row fac const).restricted = T.restricted.image fin.castp :=
by simp [add_row, map_eq_image]

@[simp] lemma fin.cast_lt_cast_succ {n : ℕ} (a : fin n) (h : a.1 < n) :
  a.cast_succ.cast_lt h = a := by cases a; refl

lemma minor_mem_flat_of_mem_add_row_flat {T : tableau m n} {fac : rvec (m + n)} {const : ℚ}
  {x : cvec (m + 1 + n)} : x ∈ (T.add_row fac const).flat → minor x fin.castp id ∈ T.flat :=
begin
  rw [mem_flat_iff, mem_flat_iff],
  intros h r,
  have := h (fin.cast_succ r),
  simp [add_row_rowg_cast_succ, add_row_offset, add_row_to_matrix,
    (show (fin.cast_succ r).val < m, from r.2), add_row_colg] at this,
  simpa
end

lemma minor_mem_sol_set_of_mem_add_row_sol_set {T : tableau m n} {fac : rvec (m + n)} {const : ℚ}
  {x : cvec (m + 1 + n)} : x ∈ (T.add_row fac const).sol_set → minor x fin.castp id ∈ T.sol_set :=
and_implies minor_mem_flat_of_mem_add_row_flat begin
  assume h v,
  simp only [set.mem_set_of_eq, add_row_restricted, mem_image, exists_imp_distrib] at h,
  simpa [add_row_restricted, matrix.minor, id.def] using h (fin.castp v) v
end

lemma add_row_new_eq_sum_fac (T : tableau m n) (fac : rvec (m + n)) (const : ℚ)
  (x : cvec (m + 1 + n)) (hx : x ∈ (T.add_row fac const).flat) :
  x fin.lastp 0 = univ.sum (λ v : fin (m + n), fac 0 v * x (fin.castp v) 0) + const :=
calc x fin.lastp 0 = x ((T.add_row fac const).to_partition.rowg (fin.last _)) 0 :
  by simp [add_row_rowg_last]
... = univ.sum (λ j : fin n, _) + (T.add_row fac const).offset _ _ : mem_flat_iff.1 hx _
... = const +
  univ.sum (λ j, (fac 0 (T.to_partition.colg j) * x (T.to_partition.add_row.colg j) 0)) +
  (univ.sum (λ j, univ.sum (λ i, fac 0 (T.to_partition.rowg i) * T.to_matrix i j *
      x (T.to_partition.add_row.colg j) 0))
    + univ.sum (λ i, fac 0 (T.to_partition.rowg i) * T.offset i 0)) :
  by simp [add_row_to_matrix, add_row_offset, fin.last, add_mul, sum_add_distrib, sum_mul]
... = const +
  univ.sum (λ j, (fac 0 (T.to_partition.colg j) * x (T.to_partition.add_row.colg j) 0)) +
  (univ.sum (λ i, univ.sum (λ j, fac 0 (T.to_partition.rowg i) * T.to_matrix i j *
    x (T.to_partition.add_row.colg j) 0))
    + univ.sum (λ i, fac 0 (T.to_partition.rowg i) * T.offset i 0)) : by rw [sum_comm]
... = const +
  univ.sum (λ j, (fac 0 (T.to_partition.colg j) * x (T.to_partition.add_row.colg j) 0)) +
  univ.sum (λ i : fin m, (fac 0 (T.to_partition.rowg i) * x (fin.castp (T.to_partition.rowg i)) 0)) :
begin
  rw [← sum_add_distrib],
  have : ∀ r : fin m, x (fin.castp (T.to_partition.rowg r)) 0 =
    sum univ (λ (c : fin n), T.to_matrix r c * x (fin.castp (T.to_partition.colg c)) 0) +
    T.offset r 0, from mem_flat_iff.1 (minor_mem_flat_of_mem_add_row_flat hx),
  simp [this, mul_add, add_row_colg, mul_sum, mul_assoc]
end
... = ((univ.image T.to_partition.colg).sum (λ v, (fac 0 v * x (fin.castp v) 0)) +
  (univ.image T.to_partition.rowg).sum (λ v, (fac 0 v * x (fin.castp v) 0))) + const :
  by rw [sum_image, sum_image];
    simp [add_row_rowg_cast_succ, add_row_colg, T.to_partition.injective_rowg.eq_iff,
      T.to_partition.injective_colg.eq_iff]
... = _ : begin
  rw [← sum_union],
  congr,
  simpa [finset.ext, eq_comm] using T.to_partition.eq_rowg_or_colg,
  { simp [finset.ext, eq_comm, T.to_partition.rowg_ne_colg] {contextual := tt} }
end

end add_row

open tableau.simplex

/-- Boolean returning whether or not it is consistent to make `i` nonnegative. Only makes sense for
  feasible tableaux. Wrong in unbounded case -/
def max_nonneg (T : tableau m n) (i : fin m) : bool :=
0 ≤ (simplex T i).offset i 0
#print option.get

lemma max_nonneg_iff (T : tableau m n) (hT : T.feasible) (i : fin m) :
  T.max_nonneg i ↔ ∃ x : cvec (m + n), x ∈ T.sol_set ∧ 0 ≤ x (T.to_partition.rowg i) 0 :=
by simp [max_nonneg, bool.of_to_bool_iff]; exact
⟨λ h, ⟨(T.simplex i).of_col 0, by rw [← simplex_sol_set i,
    ← feasible_iff_of_col_zero_mem_sol_set]; exact simplex_feasible hT _,
  by rw [← rowg_simplex]; simpa [of_col_rowg]⟩,
λ ⟨x, hx⟩, (simplex_unbounded_or_maximised hT i).elim
  (λ h, le_trans hx.2 (begin
      have := h x (by simpa using hx.1),
      rw [← rowg_simplex _ i, of_col_rowg] at this,
      simpa [rowg_simplex] using this
    end))
  (λ h, begin
    cases h 0 with x hx,


  end)⟩


section assertge






end assertge


end tableau

section test

open tableau tableau.simplex

def list.to_matrix (m :ℕ) (n : ℕ) (l : list (list ℚ)) : matrix (fin m) (fin n) ℚ :=
λ i j, (l.nth_le i sorry).nth_le j sorry

instance has_repr_fin_fun {n : ℕ} {α : Type*} [has_repr α] : has_repr (fin n → α) :=
⟨λ f, repr (vector.of_fn f).to_list⟩

instance {m n} : has_repr (matrix (fin m) (fin n) ℚ) := has_repr_fin_fun

-- def T : tableau 4 5 :=
-- { to_matrix := list.to_matrix 4 5 [[1, 3/4, -20, 1/2, -6], [0, 1/4, -8, -1, 9],
--     [0, 1/2, -12, 1/2, 3], [0,0,0,1,0]],
--   offset := (list.to_matrix 1 4 [[-3,0,0,1]])ᵀ,
--   to_partition := default _,
--   restricted := univ.erase 6 }

-- def T : tableau 4 5 :=
-- { to_matrix := list.to_matrix 4 5 [[1, 3/5, 20, 1/2, -6], [19, 1, -8, -1, 9],
--     [5, 1/2, -12, 1/2, 3], [13,0.1,11,21,0]],
--   offset := (list.to_matrix 1 4 [[3,1,51,1]])ᵀ,
--   to_partition := default _,
--   restricted := univ }
set_option profiler true
#print algebra.sub
def T : tableau 25 10 :=
{ to_matrix := list.to_matrix 25 10
    [[-1,0,-1,-1,1,1,1,1,1,1],
    [0,0,-1,0,0,0,0,0,0,-1],
    [0,0,-1,0,0,0,-1,-1,-1,0],
    [0,0,-1,0,-1,-1,0,1,-1,-1],
    [0,-0,0,0,0,-1,0,-1,0,-1],
    [0,0,0,0,-1,0,0,-1,0,0],
    [0,0,0,0,0,0,0,0,-1,-1],
    [0,0,-1,0,0,0,0,0,0,-1],
    [0,0,0,0,0,-1,0,0,-1,-1],
    [0,-1,0,0,0,-1,-1,1,0,0],
    [0,-1,-1,0,0,0,0,-1,1,0],
    [0,0,0,0,-1,0,-1,0,-1,-1],
    [0,0,-1,0,-1,0,0,-1,-1,-1],
    [-1,0,0,0,0,0,0,0,-1,-1],
    [0,-1,0,0,-1,-1,0,0,-1,-1],
    [-1,-1,0,00,0,0,-1,0,-1,0],
    [0,0,-1,0,0,0,0,-1,0,0],
    [-1,0,0,0,0,0,0,0,0,-1],
    [-1,0,-1,0,0,0,-1,0,0,-1],
    [0,1,0,0,-1,0,0,-1,-1,-1],
    [-1,-1,0,0,0,0,0,0,-1,0],
    [0,0,0,0,-1,0,0,0,0,-1],
    [0,0,0,0,-1,0,0,0,1,0],
    [0,0,-1,0,-1,0,-1,0,-1,-1],
    [0,0,0,0,0,-1,0,0,-1,-1]],
  offset := λ i _, 1,
  to_partition := default _,
  restricted := univ }
#eval tableau.sizeof _ _ T
#print tc.rec

#eval let s := T.simplex (λ _, tt) dec_trivial 0 in
(s.2, s.1.offset 0 0, s.1.to_partition.row_indices.1)

end test
