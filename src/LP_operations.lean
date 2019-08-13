import data.matrix.pequiv data.rat.basic tactic.fin_cases .misc .argmin .partition

open matrix fintype finset function pequiv

variables {m n : ℕ}

local notation `rvec`:2000 n := matrix (fin 1) (fin n) ℚ
local notation `cvec`:2000 m := matrix (fin m) (fin 1) ℚ
local infix ` ⬝ `:70 := matrix.mul
local postfix `ᵀ` : 1500 := transpose
local attribute [instance] matrix.partial_order
local attribute [instance, priority 0] algebra.has_scalar

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

abbreviation rowi := T.to_partition.rowg

/-- The affine subspace represented by the tableau ignoring nonnegativity restrictiions -/
def flat : set (cvec (m + n)) := { x | T.to_partition.rowp.to_matrix ⬝ x =
  T.to_matrix ⬝ T.to_partition.colp.to_matrix ⬝ x + T.offset }

/-- The sol_set is the subset of ℚ^(m+n) that satisifies the tableau -/
def sol_set : set (cvec (m + n)) :=
  flat T ∩ { x | ∀ i, i ∈ T.restricted → 0 ≤ x i 0 }

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
def of_col (T : tableau m n) (c : cvec n) : cvec (m + n) :=
T.to_partition.colp.to_matrixᵀ ⬝ c + T.to_partition.rowp.to_matrixᵀ ⬝
  (T.to_matrix ⬝ c + T.offset)

/-- A `tableau` is feasible if its `offset` column is nonnegative in restricted rows -/
def feasible : Prop :=
∀ i, T.to_partition.rowg i ∈ T.restricted → 0 ≤ T.offset i 0

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
  restricted := T.restricted  }

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

/- Belongs in mathlib -/
lemma le_div_iff_of_neg {α : Type*} [linear_ordered_field α] {a b c : α}
  (hc : c < 0) : a ≤ b / c ↔ b ≤ a * c :=
by rw [← neg_neg c, mul_neg_eq_neg_mul_symm, div_neg _ (ne_of_gt (neg_pos.2 hc)), le_neg,
    div_le_iff (neg_pos.2 hc), neg_mul_eq_neg_mul_symm]

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
      simp [_root_.mul_add, _root_.add_mul, mul_comm, mul_assoc, mul_left_comm]),
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
    simp [row_sum_erase_eq hx, _root_.mul_add, _root_.add_mul,
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

/-- definition used to define well-foundedness of a pivot rule -/
inductive rel_gen {α : Type*} (f : α → option α) : α → α → Prop
| of_mem : ∀ {x y}, x ∈ f y → rel_gen x y
| trans : ∀ {x y z}, rel_gen x y → rel_gen y z → rel_gen x z

/-- A pivot rule is a function that selects a nonzero pivot, given a tableau, such that
  iterating using this pivot rule terminates. -/
structure pivot_rule (m n : ℕ) : Type :=
(pivot_indices : tableau m n → option (fin m × fin n))
(well_founded : well_founded (rel_gen (λ T, pivot_indices T >>= λ i, T.pivot i.1 i.2)))
(ne_zero : ∀ {T r s}, (r, s) ∈ pivot_indices T → T.to_matrix r s ≠ 0)

def pivot_rule.rel (p : pivot_rule m n) : tableau m n → tableau m n → Prop :=
rel_gen (λ T, p.pivot_indices T >>= λ i, T.pivot i.1 i.2)

lemma pivot_rule.rel_wf (p : pivot_rule m n) : well_founded p.rel := p.well_founded

def iterate (p : pivot_rule m n) : tableau m n → tableau m n
| T :=
have ∀ (r : fin m) (s : fin n), (r, s) ∈ p.pivot_indices T → p.rel (T.pivot r s) T,
  from λ r s hrs, rel_gen.of_mem $ by rw option.mem_def.1 hrs; exact rfl,
option.cases_on (p.pivot_indices T) (λ _, T)
  (λ i this,
    have wf : p.rel (T.pivot i.1 i.2) T, from this _ _ (by cases i; exact rfl),
    iterate (T.pivot i.1 i.2))
  this
using_well_founded { rel_tac := λ _ _, `[exact ⟨_, p.rel_wf⟩],
  dec_tac := tactic.assumption }

lemma iterate_pivot {p : pivot_rule m n} {T : tableau m n} {r : fin m} {s : fin n}
  (hrs : (r, s) ∈ p.pivot_indices T) : (T.pivot r s).iterate p = T.iterate p :=
by conv_rhs {rw iterate}; simp [option.mem_def.1 hrs]

@[simp] lemma pivot_indices_iterate (p : pivot_rule m n) : ∀ (T : tableau m n),
  p.pivot_indices (T.iterate p) = none
| T :=
have ∀ r s, (r, s) ∈ p.pivot_indices T → p.rel (T.pivot r s) T,
  from λ r s hrs, rel_gen.of_mem $ by rw option.mem_def.1 hrs; exact rfl,
begin
  rw iterate,
  cases h : p.pivot_indices T with i,
  { simp [h] },
  { cases i with r s,
    simp [h, pivot_indices_iterate (T.pivot r s)] }
end
using_well_founded { rel_tac := λ _ _, `[exact ⟨_, p.rel_wf⟩], dec_tac := `[tauto] }

/- Is there some nice elaborator attribute for this, to avoid `P` having to be explicit? -/
lemma iterate_induction_on (P : tableau m n → Prop) (p : pivot_rule m n) :
  ∀ T : tableau m n, P T → (∀ T' r s, P T' → (r, s) ∈ p.pivot_indices T'
    → P (T'.pivot r s)) → P (T.iterate p)
| T := λ hT ih,
have ∀ r s, (r, s) ∈ p.pivot_indices T → p.rel (T.pivot r s) T,
  from λ r s hrs, rel_gen.of_mem $ by rw option.mem_def.1 hrs; exact rfl,
begin
  rw iterate,
  cases h : p.pivot_indices T with i,
  { simp [hT, h] },
  { cases i with r s,
    simp [h, iterate_induction_on _ (ih _ _ _ hT h) ih] }
end
using_well_founded { rel_tac := λ _ _, `[exact ⟨_, p.rel_wf⟩], dec_tac := `[tauto] }

@[simp] lemma iterate_flat (p : pivot_rule m n) (T : tableau m n) :
  (T.iterate p).flat = T.flat :=
iterate_induction_on (λ T', T'.flat = T.flat) p T rfl $
  assume T' r s (hT' : T'.flat = T.flat) hrs, by rw [← hT', flat_pivot (p.ne_zero hrs)]

@[simp] lemma iterate_sol_set (p : pivot_rule m n) (T : tableau m n) :
  (T.iterate p).sol_set = T.sol_set :=
iterate_induction_on (λ T', T'.sol_set = T.sol_set) p T rfl $
  assume T' r s (hT' : T'.sol_set = T.sol_set) hrs,
    by rw [← hT', sol_set_pivot (p.ne_zero hrs)]

namespace simplex

def find_pivot_column (T : tableau m n) (i : fin m) : option (fin n) :=
option.cases_on (fin.find (λ s : fin n, T.to_matrix i s ≠ 0 ∧ T.to_partition.colg s ∉ T.restricted))
  (fin.find (λ s : fin n, 0 < T.to_matrix i s))
  some

def find_pivot_row (T : tableau m n) (i : fin m) (s : fin n) : option (fin m) :=
let l := (list.fin_range m).filter (λ r : fin m, i ≠ r ∧ T.to_partition.rowg r ∈ T.restricted
  ∧ T.to_matrix i s / T.to_matrix r s < 0) in
l.argmin (λ r', abs (T.offset r' 0 / T.to_matrix r' s))

/-- Belongs elsewhere -/
lemma mem_find_iff {p : fin n → Prop} [decidable_pred p] {i : fin n} :
  i ∈ fin.find p ↔ p i ∧ ∀ j, p j → i ≤ j :=
sorry

/-- Belongs elsewhere -/
lemma find_eq_some_iff {p : fin n → Prop} {h : decidable_pred p} {i : fin n} :
  fin.find p = some i ↔ p i ∧ ∀ j, p j → i ≤ j := sorry

lemma find_pivot_column_spec {T : tableau m n} {i : fin m} {s : fin n} :
  s ∈ find_pivot_column T i → (T.to_matrix i s ≠ 0 ∧ T.to_partition.colg s ∉ T.restricted)
  ∨ (0 < T.to_matrix i s ∧ T.to_partition.colg s ∈ T.restricted) :=
begin
  simp [find_pivot_column],
  cases h : fin.find (λ s : fin n, T.to_matrix i s ≠ 0 ∧ T.to_partition.colg s ∉ T.restricted),
  { finish [h, find_eq_some_iff, fin.find_eq_none_iff, lt_irrefl (0 : ℚ)] },
  { finish [find_eq_some_iff] }
end

-- lemma find_pivot_column_eq_none_aux {T : tableau m n} {i : fin m} {s : fin n} :
--   find_pivot_column T i = none ↔ (∀ s, T.to_matrix i s ≤ 0) :=
-- begin
--   simp [find_pivot_column, fin.find_eq_none_iff],
--   cases h : fin.find (λ s : fin n, T.to_matrix i s ≠ 0 ∧ T.to_partition.colg s ∉ T.restricted),
--   { finish [fin.find_eq_none_iff] },
--   { simp [find_eq_some_iff] at *, }


-- end

lemma find_pivot_column_eq_none {T : tableau m n} {i : fin m} (hT : T.feasible)
  (h : find_pivot_column T i = none) : T.is_maximised (T.of_col 0) (T.to_partition.rowg i) :=
is_maximised_of_col_zero hT
begin
  revert h,
  simp [find_pivot_column],
  cases h : fin.find (λ s : fin n, T.to_matrix i s ≠ 0 ∧ T.to_partition.colg s ∉ T.restricted),
  { finish [fin.find_eq_none_iff] },
  { simp [h] }
end

lemma find_pivot_row_spec {T : tableau m n} {i r : fin m} {s : fin n} :
  r ∈ find_pivot_row T i s →
  i ≠ r ∧ T.to_partition.rowg r ∈ T.restricted ∧
  T.to_matrix i s / T.to_matrix r s < 0 ∧
  (∀ r' : fin m, i ≠ r' → T.to_partition.rowg r' ∈ T.restricted →
    T.to_matrix i s / T.to_matrix r' s < 0 →
  abs (T.offset r 0 / T.to_matrix r s) ≤ abs (T.offset r' 0 / T.to_matrix r' s)) :=
by simp only [list.mem_argmin_iff, list.mem_filter, find_pivot_row,
    list.mem_fin_range, true_and, and_imp]; tauto

lemma find_pivot_row_eq_none_aux {T : tableau m n} {i : fin m} {s : fin n}
  (hrow : find_pivot_row T i s = none) (hs : s ∈ find_pivot_column T i) :
  ∀ r, i ≠ r → T.to_partition.rowg r ∈ T.restricted → 0 ≤ T.to_matrix i s / T.to_matrix r s :=
by simpa [find_pivot_row, list.filter_eq_nil] using hrow

lemma find_pivot_row_eq_none {T : tableau m n} {i : fin m} {s : fin n} (hT : T.feasible)
  (hrow : find_pivot_row T i s = none) (hs : s ∈ find_pivot_column T i) :
  T.is_unbounded_above (T.to_partition.rowg i) :=
have hrow : ∀ r, i ≠ r → T.to_partition.rowg r ∈ T.restricted → 0 ≤ T.to_matrix i s / T.to_matrix r s,
  from find_pivot_row_eq_none_aux hrow hs,
have hs : (T.to_matrix i s ≠ 0 ∧ T.to_partition.colg s ∉ T.restricted)
  ∨ (0 < T.to_matrix i s ∧ T.to_partition.colg s ∈ T.restricted),
  from find_pivot_column_spec hs,
have hTis : T.to_matrix i s ≠ 0, from λ h, by simpa [h, lt_irrefl] using hs,
(lt_or_gt_of_ne hTis).elim
  (λ hTis : T.to_matrix i s < 0, is_unbounded_above_rowg_of_nonpos hT s
    (hs.elim and.right (λ h, (not_lt_of_gt hTis h.1).elim))
    (λ i' hi', classical.by_cases
      (λ hii' : i = i', le_of_lt (hii' ▸ hTis))
      (λ hii' : i ≠ i', inv_nonpos.1 $ nonpos_of_mul_nonneg_right (hrow _ hii' hi') hTis))
    hTis)
  (λ hTis : 0 < T.to_matrix i s, is_unbounded_above_rowg_of_nonneg hT s
    (λ i' hi', classical.by_cases
      (λ hii' : i = i', le_of_lt (hii' ▸ hTis))
      (λ hii' : i ≠ i', inv_nonneg.1 $ nonneg_of_mul_nonneg_left (hrow _ hii' hi') hTis))
    hTis)

/-- This `pivot_rule` maximises the sample value of `i` -/
def simplex_pivot_rule (i : fin m) : pivot_rule m n :=
{ pivot_indices := λ T, find_pivot_column T i >>= λ s,
    find_pivot_row T i s >>= λ r, some (r, s),
  well_founded := sorry,
  ne_zero := λ T r s, begin
    simp only [option.mem_def, option.bind_eq_some,
      find_pivot_row, list.argmin_eq_some_iff, and_imp,
      exists_imp_distrib, prod.mk.inj_iff, list.mem_filter],
    intros,
    substs x r,
    assume h,
    simp [h, lt_irrefl, *] at *
  end  }

end simplex

def simplex (T : tableau m n) (i : fin m) : tableau m n :=
T.iterate (simplex.simplex_pivot_rule i)

namespace simplex

/-- The simplex algorithm does not pivot the variable it is trying to optimise -/
lemma simplex_pivot_indices_ne {T : tableau m n} {i : fin m} {r s} :
  (r, s) ∈ (simplex_pivot_rule i).pivot_indices T → i ≠ r :=
by simp only [simplex_pivot_rule, find_pivot_row, find_eq_some_iff, option.mem_def, list.mem_filter,
  option.bind_eq_some, prod.mk.inj_iff, exists_imp_distrib, and_imp, list.argmin_eq_some_iff,
  @forall_swap _ (_ = r), @forall_swap (_ ≠ r), imp_self, forall_true_iff] {contextual := tt}

/-- `simplex` does not move the row variable it is trying to maximise. -/
lemma rowg_simplex (T : tableau m n) (i : fin m) :
  (T.simplex i).to_partition.rowg i = T.to_partition.rowg i :=
iterate_induction_on (λ T', T'.to_partition.rowg i = T.to_partition.rowg i) _ _ rfl $
  assume T' r s (hT' : T'.to_partition.rowg i = T.to_partition.rowg i) hrs,
    by rw [to_partition_pivot, rowg_swap_of_ne _ (simplex_pivot_indices_ne hrs), hT']

theorem bind_eq_none' {α β : Type*} {o : option α} {f : α → option β} :
  o >>= f = none ↔ (∀ b a, a ∈ o → b ∉ f a) :=
option.bind_eq_none

lemma simplex_pivot_rule_eq_none {T : tableau m n} {i : fin m} (hT : T.feasible)
  (h : (simplex_pivot_rule i).pivot_indices T = none) :
  is_maximised T (T.of_col 0) (T.to_partition.rowg i) ∨
    is_unbounded_above T (T.to_partition.rowg i) :=
begin
  cases hs : find_pivot_column T i with s,
  { exact or.inl (find_pivot_column_eq_none hT hs) },
  { dsimp [simplex_pivot_rule] at h,
    rw [hs, option.some_bind, bind_eq_none'] at h,
    have : find_pivot_row T i s = none,
    { exact option.eq_none_iff_forall_not_mem.2 (λ r, by simpa using h (r, s) r) },
    exact or.inr (find_pivot_row_eq_none hT this hs) }
end

@[simp] lemma mem_simplex_pivot_rule_indices {T : tableau m n} {i : fin m} {r s} :
  (r, s) ∈ (simplex_pivot_rule i).pivot_indices T ↔
  s ∈ find_pivot_column T i ∧ r ∈ find_pivot_row T i s :=
begin
  simp only [simplex_pivot_rule,  option.mem_def, option.bind_eq_some,
    prod.mk.inj_iff, and_comm _ (_ = r), @and.left_comm _ (_ = r), exists_eq_left, and.assoc],
  simp only [and_comm _ (_ = s), @and.left_comm _ (_ = s), exists_eq_left]
end

lemma simplex_pivot_rule_feasible {T : tableau m n} {i : fin m} (hT : T.feasible)
  {r s} (hrs : (r, s) ∈ (simplex_pivot_rule i).pivot_indices T) : (T.pivot r s).feasible :=
λ i' hi', begin
  rw [mem_simplex_pivot_rule_indices] at hrs,
  have hs := find_pivot_column_spec hrs.1,
  have hr := find_pivot_row_spec hrs.2,
  dsimp only [pivot],
  by_cases hir : i' = r,
  { subst i',
    rw [if_pos rfl, neg_mul_eq_neg_mul_symm, neg_nonneg],
    exact mul_nonpos_of_nonneg_of_nonpos (hT _ hr.2.1)
      (le_of_lt (neg_of_mul_neg_left hr.2.2.1 (le_of_lt (by simp * at *)))) },
  { rw if_neg hir,
    rw [to_partition_pivot, rowg_swap_of_ne _ hir, restricted_pivot] at hi',
    by_cases hii : i = i',
    { subst i',
      refine add_nonneg (hT _ hi') (neg_nonneg.2 _),
      rw [mul_assoc, mul_left_comm],
      exact mul_nonpos_of_nonneg_of_nonpos (hT _ hr.2.1) (le_of_lt hr.2.2.1) },
    { by_cases hTi'r : 0 < T.to_matrix i' s / T.to_matrix r s,
      { have hTi's0 : T.to_matrix i' s ≠ 0, from λ h, by simpa [h, lt_irrefl] using hTi'r,
        have hTrs0 : T.to_matrix r s ≠ 0, from λ h, by simpa [h, lt_irrefl] using hTi'r,
        have hTii' : T.to_matrix i s / T.to_matrix i' s < 0,
        { suffices : (T.to_matrix i s / T.to_matrix r s) / (T.to_matrix i' s / T.to_matrix r s) < 0,
          { simp only [div_eq_mul_inv, mul_assoc, mul_inv', inv_inv',
              mul_left_comm (T.to_matrix r s), mul_left_comm (T.to_matrix r s)⁻¹,
              mul_comm (T.to_matrix r s), inv_mul_cancel hTrs0, mul_one] at this,
            simpa [mul_comm, div_eq_mul_inv] },
        { exact div_neg_of_neg_of_pos hr.2.2.1 hTi'r } },
        have := hr.2.2.2 _ hii hi' hTii',
        rwa [abs_div, abs_div, abs_of_nonneg (hT _ hr.2.1), abs_of_nonneg (hT _ hi'),
          le_div_iff (abs_pos_iff.2 hTi's0), div_eq_mul_inv, mul_right_comm,
          ← abs_inv, mul_assoc, ← abs_mul, ← div_eq_mul_inv,
          abs_of_nonneg (le_of_lt hTi'r), ← sub_nonneg, ← mul_div_assoc, div_eq_mul_inv,
          mul_comm (T.offset r 0)] at this },
      { refine add_nonneg (hT _ hi') (neg_nonneg.2 _),
        rw [mul_assoc, mul_left_comm],
        exact mul_nonpos_of_nonneg_of_nonpos (hT _ hr.2.1) (le_of_not_gt hTi'r) } } }
end

lemma simplex_feasible {T : tableau m n} (hT : T.feasible) (i : fin m) : (simplex T i).feasible :=
iterate_induction_on feasible _ _ hT (λ _ _ _ hT, simplex_pivot_rule_feasible hT)

lemma simplex_unbounded_or_maximised {T : tableau m n} (hT : T.feasible) (i : fin m) :
  is_maximised (simplex T i) ((simplex T i).of_col 0) (T.to_partition.rowg i) ∨
    is_unbounded_above (simplex T i) (T.to_partition.rowg i) :=
by rw ← rowg_simplex;
  exact simplex_pivot_rule_eq_none (simplex_feasible hT i) (pivot_indices_iterate _ _)

end simplex

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

/-- Takes a long time on this example -/
def T : tableau 20 7 :=
{ to_matrix := list.to_matrix 20 7
  [[66936 , -86739 , -127253 , 109971 , 107521 , -75883 , -7806],[41425 , -48734 , -118695 , -117250 , 85865 , -135995 , -20127],[-84630 , -134084 , -56601 , 11315 , 44203 , -110666 , 59955],[126807 , 103566 , -26027 , 91856 , 65208 , -61603 , 77039],[97698 , -69297 , -74944 , -65503 , 30390 , 88977 , 18950],[-2974 , -4253 , 74595 , -93148 , -33997 , 79545 , 9612],[118718 , 15760 , -54446 , 61921 , 87477 , -26800 , 3196],[-105941 , 31785 , -126601 , -49302 , -119796 , 101999 , 40688],[-132477 , 30593 , -93376 , 88437 , -46159 , -145283 , -6812],[81681 , -46389 , 11505 , 106846 , 141938 , 65574 , 120459],[-87352 , -17470 , -55685 , 103269 , 24211 , -128765 , 115308],[-30856 , 97040 , -108908 , -10102 , -7116 , -20331 , -54441],[-38914 , -118878 , -140982 , -145270 , -37438 , -142738 , 92027],[103975 , 100096 , -46322 , -5789 , 55040 , 17044 , 95243],[-31968 , -128908 , 90790 , 22690 , -108755 , -16227 , 134028],[109232 , 132296 , -3463 , 87319 , -31887 , 93336 , -22901],[121103 , 129374 , -48880 , -142151 , -65764 , 108725 , 78628],[21259 , 33547 , -95208 , -140857 , 133895 , 53844 , 76271],[11897 , 37281 , -24593 , -7054 , 52038 , 117349 , -25266],[12768 , 95427 , -2914 , -13272 , -57087 , -142411 , -136795]],
  offset := list.to_matrix 20 1 [[85612],[8154],[-31061],[94904],[-36658],[34776],[-9298],[85857],[136400],[131547],[64042],[-136527],[-16216],[108134],[30424],[-142642],[39431],[-67942],[-25233],[19458]],
  to_partition := default _,
  restricted := univ \ {20,21,22,23,24,25,26} }

#eval let s := T.simplex 0 in
  (s.offset, (list.fin_range 20).map
    (λ i, (s.to_partition.rowg i ∈ s.restricted : bool)), s.to_matrix,
      find_pivot_column s 0, s.to_partition.rowg)

end test