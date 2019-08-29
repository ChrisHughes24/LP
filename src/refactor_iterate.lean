import data.matrix.pequiv data.rat.basic tactic.fin_cases data.list.min_max .partition2
import order.lexicographic

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
  offset := λ i k, let offr := T.offset r k in
    if i = r
      then -offr * p
      else T.offset i k - T.to_matrix i c * offr * p,
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

lemma of_col_rowg (c : cvec n) (r : fin m) :
  of_col T c (T.to_partition.rowg r) = (T.to_matrix ⬝ c + T.offset) r :=
funext $ λ v,
  calc of_col T c (T.to_partition.rowg r) v =
      (T.to_partition.rowp.to_matrix ⬝ of_col T c) r v :
    by rw [mul_matrix_apply, rowp_eq_some_rowg]
  ... = (T.to_matrix ⬝ c + T.offset) r v : by rw [rowp_mul_of_col]

variable {T}

lemma of_col_single_rowg {q : ℚ} {r c} {k} :
  T.of_col (q • (single c 0).to_matrix) (T.to_partition.rowg r) k =
    q * T.to_matrix r c + T.offset r k:=
begin
  fin_cases k,
  erw [of_col_rowg, matrix.mul_smul, matrix.add_val, matrix.smul_val,
    matrix_mul_apply, pequiv.symm_single_apply]
end

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
      rw [of_col_single_rowg],
      exact add_nonneg (hi _ hres) (hT _ hres)
    end
    begin
      rintros ⟨j, hj⟩ hres,
      subst hj,
      simp [of_col_colg, smul_val, pequiv.single, pequiv.to_matrix],
      by_cases hjc : j = c; simp [*, le_refl] at *
    end⟩

@[simp] lemma of_col_zero_mem_sol_set_iff : T.of_col 0 ∈ T.sol_set ↔ T.feasible :=
suffices (∀ v : fin (m + n), v ∈ T.restricted → (0 : ℚ) ≤ T.of_col 0 v 0) ↔
    (∀ i : fin m, T.to_partition.rowg i ∈ T.restricted → 0 ≤ T.offset i 0),
  by simpa [sol_set, feasible, of_col_mem_flat],
⟨λ h i hi, by simpa [of_col_rowg] using h _ hi,
  λ h v hv, (T.to_partition.eq_rowg_or_colg v).elim
    (by rintros ⟨i, hi⟩; subst hi; simp [of_col_rowg]; tauto)
    (by rintros ⟨j, hj⟩; subst hj; simp)⟩

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
    x (T.to_partition.rowg r) 0 - T.offset r 0 - T.to_matrix r s * x (T.to_partition.colg s) 0 :=
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
    by simpa [of_col_rowg] using h (T.of_col 0) (of_col_mem_flat _ _),
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

lemma mul_single_ext {R : Type*} {m n : ℕ} [semiring R]
  {A B : matrix (fin m) (fin n) R} (h : ∀ j : fin n, A ⬝ (single j (0 : fin 1)).to_matrix = B ⬝
    (single j (0 : fin 1)).to_matrix) : A = B :=
by ext i j; simpa [matrix_mul_apply] using congr_fun (congr_fun (h j) i) 0

lemma single_mul_ext {R : Type*} {m n : ℕ} [semiring R]
  {A B : matrix (fin m) (fin n) R} (h : ∀ i, (single (0 : fin 1) i).to_matrix ⬝ A =
    (single (0 : fin 1) i).to_matrix ⬝ B) : A = B :=
by ext i j; simpa [mul_matrix_apply] using congr_fun (congr_fun (h i) 0) j

lemma ext {T₁ T₂ : tableau m n} (hflat : T₁.flat = T₂.flat)
  (hpartition : T₁.to_partition = T₂.to_partition)
  (hres : T₁.restricted = T₂.restricted) : T₁ = T₂ :=
have hoffset : T₁.offset = T₂.offset,
  by rw [set.ext_iff] at hflat; simpa [of_col, flat, hpartition, matrix.mul_assoc,
    mul_right_eq_of_mul_eq (rowp_mul_rowp_transpose _),
    mul_right_eq_of_mul_eq (colp_mul_rowp_transpose _)] using
  (hflat (T₁.of_col 0)).1 (of_col_mem_flat _ _),
have hmatrix : T₁.to_matrix = T₂.to_matrix,
  from mul_single_ext $ λ j, begin
    rw [set.ext_iff] at hflat,
    have := (hflat (T₁.of_col (single j 0).to_matrix)).1 (of_col_mem_flat _ _),
    simpa [of_col, hoffset, hpartition, flat, matrix.mul_add, matrix.mul_assoc,
      mul_right_eq_of_mul_eq (rowp_mul_rowp_transpose _),
      mul_right_eq_of_mul_eq (colp_mul_rowp_transpose _),
      mul_right_eq_of_mul_eq (colp_mul_colp_transpose _),
      mul_right_eq_of_mul_eq (rowp_mul_colp_transpose _)] using
      (hflat (T₁.of_col (single j 0).to_matrix)).1 (of_col_mem_flat _ _)
  end,
by cases T₁; cases T₂; simp * at *

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
lemma feasible_pivot {T : tableau m n} (hT : T.feasible) {r c}
  (hres : T.to_partition.rowg r ∈ T.restricted)
  (hpos : T.to_partition.colg c ∈ T.restricted → T.to_matrix r c < 0)
  (hrmin : ∀ (i : fin m), T.to_partition.rowg i ∈ T.restricted →
          0 < T.to_matrix i c / T.to_matrix r c →
          abs (T.offset r 0 / T.to_matrix r c) ≤ abs (T.offset i 0 / T.to_matrix i c)) :
  (T.pivot r c).feasible :=
begin
  assume i hi,
  dsimp only [pivot],
  by_cases hir : i = r,
  { subst i,
    rw [if_pos rfl, neg_mul_eq_neg_mul_symm, neg_nonneg],
    exact mul_nonpos_of_nonneg_of_nonpos (hT _ hres) (inv_nonpos.2 $ le_of_lt (by simp * at *)) },
  { rw if_neg hir,
    rw [to_partition_pivot, rowg_swap_of_ne _ hir, restricted_pivot] at hi,
    by_cases hTir : 0 < T.to_matrix i c / T.to_matrix r c,
    { have hTic0 : T.to_matrix i c ≠ 0, from λ h, by simpa [h, lt_irrefl] using hTir,
      have hTrc0 : T.to_matrix r c ≠ 0, from λ h, by simpa [h, lt_irrefl] using hTir,
      have := hrmin _ hi hTir,
      rwa [abs_div, abs_div, abs_of_nonneg (hT _ hres), abs_of_nonneg (hT _ hi),
        le_div_iff (abs_pos_iff.2 hTic0), div_eq_mul_inv, mul_right_comm, ← abs_inv, mul_assoc,
        ← abs_mul, ← div_eq_mul_inv, abs_of_nonneg (le_of_lt hTir), ← sub_nonneg,
        ← mul_div_assoc, div_eq_mul_inv, mul_comm (T.offset r 0)] at this },
    { refine add_nonneg (hT _ hi) (neg_nonneg.2 _),
      rw [mul_assoc, mul_left_comm],
      exact mul_nonpos_of_nonneg_of_nonpos (hT _ hres) (le_of_not_gt hTir) } }
end

lemma feasible_simplex_pivot {T : tableau m n} {obj : fin m} (hT : T.feasible) {r c}
  (hres : T.to_partition.rowg r ∈ T.restricted)
  (hrneg : T.to_matrix obj c / T.to_matrix r c < 0)
  (hrmin : ∀ (r' : fin m), obj ≠ r' → T.to_partition.rowg r' ∈ T.restricted →
          T.to_matrix obj c / T.to_matrix r' c < 0 →
          abs (T.offset r 0 / T.to_matrix r c) ≤ abs (T.offset r' 0 / T.to_matrix r' c))
  (hc : T.to_partition.colg c ∈ T.restricted → 0 < T.to_matrix obj c) :
  (T.pivot r c).feasible :=
feasible_pivot hT hres (λ hcres, inv_neg'.1 (neg_of_mul_neg_left hrneg (le_of_lt (hc hcres))))
  (λ i hires hir,
    have hobji : obj ≠ i,
      from λ hobji, not_lt_of_gt hir (hobji ▸ hrneg),
    (hrmin _ hobji hires $
      have hTrc0 : T.to_matrix r c ≠ 0, from λ _, by simp [*, lt_irrefl] at *,
      suffices (T.to_matrix obj c / T.to_matrix r c) / (T.to_matrix i c / T.to_matrix r c) < 0,
        by rwa [div_div_div_cancel_right _ _ hTrc0] at this,
      div_neg_of_neg_of_pos hrneg hir))

lemma simplex_offset_obj_le {T : tableau m n} {obj : fin m} (hT : T.feasible) {r c}
  (hres : T.to_partition.rowg r ∈ T.restricted)
  (hrneg : T.to_matrix obj c / T.to_matrix r c < 0) :
  T.offset obj 0 ≤ (T.pivot r c).offset obj 0 :=
have obj ≠ r, from λ hor, begin
  subst hor,
  by_cases h0 : T.to_matrix obj c = 0,
  { simp [lt_irrefl, *] at * },
  { simp [div_self h0, not_lt_of_le zero_le_one, *] at * }
end,
by simp only [le_add_iff_nonneg_right, sub_eq_add_neg, neg_nonneg, mul_assoc, div_eq_mul_inv,
    mul_left_comm (T.to_matrix obj c), offset_pivot_of_ne _ this];
  exact mul_nonpos_of_nonneg_of_nonpos (hT _ hres) (le_of_lt hrneg)

lemma offset_eq_zero_of_offset_obj_eq {T : tableau m n} {obj : fin m} (hT : T.feasible) {r c}
  (hc : T.to_matrix obj c ≠ 0) (hrc : T.to_matrix r c ≠ 0) (hobjr : obj ≠ r)
  (hobj : (T.pivot r c).offset obj 0 = T.offset obj 0) :
  T.offset r 0 = 0 :=
by rw [offset_pivot_of_ne _ hobjr, sub_eq_iff_eq_add, ← sub_eq_iff_eq_add', sub_self,
    eq_comm, div_eq_mul_inv, mul_eq_zero, mul_eq_zero, inv_eq_zero] at hobj;
  tauto

namespace simplex

def pivot_linear_order (T : tableau m n) : decidable_linear_order (fin n) :=
decidable_linear_order.lift T.to_partition.colg (injective_colg _) (by apply_instance)

def find_pivot_column (T : tableau m n) (obj : fin m) : option (fin n) :=
option.cases_on
  (fin.find (λ c : fin n, T.to_matrix obj c ≠ 0 ∧ T.to_partition.colg c ∉ T.restricted))
  (((list.fin_range n).filter (λ c : fin n, 0 < T.to_matrix obj c)).argmin
    T.to_partition.colg)
  some

lemma injective_prod_mk_left {α β γ : Type*} {f : γ → α × β} (hf : injective (prod.fst ∘ f)) :
  injective f :=
λ x y hxy, hf (congr_arg prod.fst hxy : _)

lemma injective_prod_mk_right {α β γ : Type*} {f : γ → α × β} (hf : injective (prod.snd ∘ f)) :
  injective f :=
λ x y hxy, hf (congr_arg prod.snd hxy : _)

def pivot_row_linear_order (T : tableau m n) (c : fin n) : decidable_linear_order (fin m) :=
decidable_linear_order.lift
  (show fin m → lex ℚ (fin (m + n)),
    from λ r', (abs (T.offset r' 0 / T.to_matrix r' c), T.to_partition.rowg r'))
  (injective_prod_mk_right (injective_rowg _))
  (by apply_instance)

section
local attribute [instance, priority 0] fin.has_le fin.decidable_linear_order

lemma pivot_row_linear_order_le_def (T : tableau m n) (c : fin n) :
  @has_le.le (fin m)
  (by haveI := pivot_row_linear_order T c; apply_instance) =
  (λ i i', abs (T.offset i 0 / T.to_matrix i c) < abs (T.offset i' 0 / T.to_matrix i' c) ∨
    (abs (T.offset i 0 / T.to_matrix i c) = abs (T.offset i' 0 / T.to_matrix i' c) ∧
    T.to_partition.rowg i ≤ T.to_partition.rowg i')) :=
funext $ λ i, funext $ λ i', propext $ prod.lex_def _ _

end

-- @[simp] lemma pivot_row_linear_order_le_def (T : tableau m n) (c : fin n) (i i' : fin m) :
--   pivot_row_le T c i i' ↔
--   abs (T.offset i 0 / T.to_matrix i c) < abs (T.offset i' 0 / T.to_matrix i' c) ∨
--     (abs (T.offset i 0 / T.to_matrix i c) = abs (T.offset i' 0 / T.to_matrix i' c) ∧
--     T.to_partition.rowg i ≤ T.to_partition.rowg i') :=
-- prod.lex_def _ _

def find_pivot_row (T : tableau m n) (obj: fin m) (c : fin n) : option (fin m) :=
let l := (list.fin_range m).filter (λ r : fin m, obj ≠ r ∧ T.to_partition.rowg r ∈ T.restricted
  ∧ T.to_matrix obj c / T.to_matrix r c < 0) in
@list.minimum _ (pivot_row_linear_order T c) l

lemma find_pivot_column_spec {T : tableau m n} {obj : fin m} {s : fin n} :
  s ∈ find_pivot_column T obj → (T.to_matrix obj s ≠ 0 ∧ T.to_partition.colg s ∉ T.restricted)
  ∨ (0 < T.to_matrix obj s ∧ T.to_partition.colg s ∈ T.restricted) :=
begin
  simp [find_pivot_column],
  cases h : fin.find (λ s : fin n, T.to_matrix obj s ≠ 0 ∧ T.to_partition.colg s ∉ T.restricted),
  { finish [h, fin.find_eq_some_iff, fin.find_eq_none_iff, lt_irrefl (0 : ℚ),
      list.argmin_eq_some_iff] },
  { finish [fin.find_eq_some_iff] }
end

lemma find_pivot_column_eq_none {T : tableau m n} {obj : fin m} (hT : T.feasible)
  (h : find_pivot_column T obj = none) : T.is_maximised (T.of_col 0) (T.to_partition.rowg obj) :=
is_maximised_of_col_zero hT
begin
  revert h,
  simp [find_pivot_column],
  cases h : fin.find (λ c : fin n, T.to_matrix obj c ≠ 0 ∧ T.to_partition.colg c ∉ T.restricted),
  { finish [fin.find_eq_none_iff, list.argmin_eq_some_iff, list.filter_eq_nil] },
  { simp [h] }
end

lemma find_pivot_row_spec {T : tableau m n} {obj r : fin m} {c : fin n} :
  r ∈ find_pivot_row T obj c →
  obj ≠ r ∧ T.to_partition.rowg r ∈ T.restricted ∧
  T.to_matrix obj c / T.to_matrix r c < 0 ∧
  (∀ r' : fin m, obj ≠ r' → T.to_partition.rowg r' ∈ T.restricted →
    T.to_matrix obj c / T.to_matrix r' c < 0 →
  abs (T.offset r 0 / T.to_matrix r c) ≤ abs (T.offset r' 0 / T.to_matrix r' c)) :=
begin
  simp only [list.mem_filter, find_pivot_row, option.mem_def, with_bot.some_eq_coe,
    list.minimum_eq_coe_iff, list.mem_fin_range, true_and, and_imp],
  rw [pivot_row_linear_order_le_def],
  intros hor hres hr0 h,
  simp only [*, true_and, ne.def, not_false_iff],
  intros r' hor' hres' hr0',
  cases h r' hor' hres' hr0',
  { exact le_of_lt (by assumption) },
  { exact le_of_eq (by tauto) }
end

lemma ne_zero_of_mem_find_pivot_row {T : tableau m n} {obj r : fin m} {c : fin n}
  (hr : r ∈ find_pivot_row T obj c) : T.to_matrix r c ≠ 0 :=
assume hrc, by simpa [lt_irrefl, hrc] using find_pivot_row_spec hr

lemma ne_zero_of_mem_find_pivot_column {T : tableau m n} {obj : fin m} {c : fin n}
  (hc : c ∈ find_pivot_column T obj) : T.to_matrix obj c ≠ 0 :=
λ h, by simpa [h, lt_irrefl] using find_pivot_column_spec hc

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
  have := @feasible_simplex_pivot _ _ _ obj hT r c,
  tauto
end

section blands_rule

lemma option.eq_some_iff_get_eq {α : Type*} {o : option α} {a : α} :
  o = some a ↔ ∃ h : o.is_some, option.get h = a :=
by cases o; simp

local attribute [instance, priority 0] classical.dec
variable (obj : fin m)

lemma not_unique_row_and_unique_col {T T' : tableau m n} {r c c'}
  (hcobj0 : 0 < T.to_matrix obj c)
  (hc'obj0 : 0 < T'.to_matrix obj c')
  (hrc0 : T.to_matrix r c < 0)
  (hflat : T.flat = T'.flat)
  (hs : T.to_partition.rowg r = T'.to_partition.colg c')
  (hrobj : T.to_partition.rowg obj = T'.to_partition.rowg obj)
  (hfickle : ∀ i, T.to_partition.rowg i ≠ T'.to_partition.rowg i → T.offset i 0 = 0)
  (hobj : T.offset obj 0 = T'.offset obj 0)
  (unique_col : ∀ j ≠ c', T'.to_matrix obj j ≤ 0)
  (unique_row : ∀ i ≠ r, T.offset i 0 = 0 → 0 ≤ T.to_matrix i c) :
  false :=
let objr := T.to_partition.rowg obj in
let x := λ y : ℚ, T.of_col (y • (single c 0).to_matrix) in
have hxflatT' : ∀ {y}, x y ∈ flat T', from hflat ▸ λ _, of_col_mem_flat _ _,
have hxrow : ∀ y i, x y (T.to_partition.rowg i) 0 = T.offset i 0 + y * T.to_matrix i c,
  by simp [x, of_col_single_rowg],
have hxcol : ∀ {y j}, j ≠ c → x y (T.to_partition.colg j) 0 = 0,
  from λ y j hjc, by simp [x, of_col_colg, pequiv.to_matrix, single_apply_of_ne hjc.symm],
have hxcolc : ∀ {y}, x y (T.to_partition.colg c) 0 = y, by simp [x, of_col_colg, pequiv.to_matrix],
let c_star : fin (m + n) → ℚ := λ v, option.cases_on (T'.to_partition.colp.symm v) 0
  (T'.to_matrix obj) in
have hxobj : ∀ y, x y objr 0 = T.offset obj 0 + y * T.to_matrix obj c, from λ y, hxrow _ _,
have hgetr : ∀ {y v}, c_star v * x y v 0 ≠ 0 → (T'.to_partition.colp.symm v).is_some,
  from λ y v, by cases h : T'.to_partition.colp.symm v; dsimp [c_star]; rw h; simp,
have c_star_eq_get : ∀ {v} (hv : (T'.to_partition.colp.symm v).is_some),
    c_star v = T'.to_matrix obj (option.get hv),
  from λ v hv, by dsimp only [c_star]; conv_lhs{rw [← option.some_get hv]}; refl,
have hsummmn : ∀ {y}, sum univ (λ j, T'.to_matrix obj j * x y (T'.to_partition.colg j) 0) =
    sum univ (λ v, c_star v * x y v 0),
  from λ y, sum_bij_ne_zero (λ j _ _, T'.to_partition.colg j) (λ _ _ _, mem_univ _)
    (λ _ _ _ _ _ _ h, T'.to_partition.injective_colg h)
    (λ v _ h0, ⟨option.get (hgetr h0), mem_univ _,
      by rw [← c_star_eq_get (hgetr h0)]; simpa using h0, by simp⟩)
    (λ _ _ h0, by dsimp [c_star]; rw [colp_colg]),
have hgetc : ∀ {y v}, c_star v * x y v 0 ≠ 0 → v ≠ T.to_partition.colg c →
    (T.to_partition.rowp.symm v).is_some,
  from λ y v, (eq_rowg_or_colg T.to_partition v).elim
    (λ ⟨i, hi⟩, by rw [hi, rowp_rowg]; simp)
    (λ ⟨j, hj⟩ h0 hvc,
      by rw [hj, hxcol (mt (congr_arg T.to_partition.colg) (hvc ∘ hj.trans)), mul_zero] at h0;
        exact (h0 rfl).elim),
have hsummmnn : ∀ {y}, (univ.erase (T.to_partition.colg c)).sum (λ v, c_star v * x y v 0) =
    univ.sum (λ i, c_star (T.to_partition.rowg i) * x y (T.to_partition.rowg i) 0),
  from λ y, eq.symm $ sum_bij_ne_zero (λ i _ _, T.to_partition.rowg i) (by simp)
    (λ _ _ _ _ _ _ h, T.to_partition.injective_rowg h)
    (λ v hvc h0, ⟨option.get (hgetc h0 (mem_erase.1 hvc).1), mem_univ _, by simpa using h0⟩)
    (by intros; refl),
have hsumm : ∀ {y}, univ.sum (λ i, c_star (T.to_partition.rowg i) * x y (T.to_partition.rowg i) 0) =
    univ.sum (λ i, c_star (T.to_partition.rowg i) * T.offset i 0) +
    y * univ.sum (λ i, c_star (T.to_partition.rowg i) * T.to_matrix i c),
  from λ y, by simp only [hxrow, mul_add, add_mul, sum_add_distrib, mul_assoc,
    mul_left_comm _ y, mul_sum.symm],
have hxobj' : ∀ y, x y objr 0 = univ.sum (λ v, c_star v * x y v 0) + T'.offset obj 0,
  from λ y, by dsimp [objr]; rw [hrobj, mem_flat_iff.1 hxflatT', hsummmn],
have hy : ∀ {y}, y * T.to_matrix obj c = c_star (T.to_partition.colg c) * y +
    univ.sum (λ i, c_star (T.to_partition.rowg i) * T.offset i 0) +
      y * univ.sum (λ i, c_star (T.to_partition.rowg i) * T.to_matrix i c),
  from λ y, by rw [← add_left_inj (T.offset obj 0), ← hxobj, hxobj',
    ← insert_erase (mem_univ (T.to_partition.colg c)), sum_insert (not_mem_erase _ _),
    hsummmnn, hobj, hsumm, hxcolc]; simp,
have hy' : ∀ (y), y * (T.to_matrix obj c - c_star (T.to_partition.colg c) -
    univ.sum (λ i, c_star (T.to_partition.rowg i) * T.to_matrix i c)) =
    univ.sum (λ i, c_star (T.to_partition.rowg i) * T.offset i 0),
  from λ y, by rw [mul_sub, mul_sub, hy]; simp [mul_comm, mul_assoc, mul_left_comm],
have h0 : T.to_matrix obj c - c_star (T.to_partition.colg c) -
    univ.sum (λ i, c_star (T.to_partition.rowg i) * T.to_matrix i c) = 0,
  by rw [← (domain.mul_left_inj (@one_ne_zero ℚ _)), hy', ← hy' 0, zero_mul, mul_zero],
have hcolnec' : T'.to_partition.colp.symm (T.to_partition.colg c) ≠ some c',
  from λ h,
    by simpa [hs.symm] using congr_arg T'.to_partition.colg (option.eq_some_iff_get_eq.1 h).snd,
have eq_of_roweqc' : ∀ {i}, T'.to_partition.colp.symm (T.to_partition.rowg i) = some c' → i = r,
  from λ i h, by simpa [hs.symm, T.to_partition.injective_rowg.eq_iff] using
    congr_arg T'.to_partition.colg (option.eq_some_iff_get_eq.1 h).snd,
have sumpos : 0 < univ.sum (λ i, c_star (T.to_partition.rowg i) * T.to_matrix i c),
  by rw [← sub_eq_zero.1 h0]; exact add_pos_of_pos_of_nonneg hcobj0
    (begin
      simp only [c_star, neg_nonneg],
      cases h : T'.to_partition.colp.symm (T.to_partition.colg c) with j,
      { refl },
      { exact unique_col _ (λ hjc', hcolnec' $ hjc' ▸ h) }
    end),
have hexi : ∃ i, 0 < c_star (T.to_partition.rowg i) * T.to_matrix i c,
  from imp_of_not_imp_not _ _ (by simpa using @sum_nonpos _ _ (@univ (fin m) _)
    (λ i, c_star (T.to_partition.rowg i) * T.to_matrix i c) _ _) sumpos,
let ⟨i, hi⟩ := hexi in
have hi0 : T.offset i 0 = 0, from hfickle i
  (λ h, by dsimp [c_star] at hi; rw [h, colp_rowg_eq_none] at hi; simpa [lt_irrefl] using hi),
have hi_some : (T'.to_partition.colp.symm (T.to_partition.rowg i)).is_some,
  from option.ne_none_iff_is_some.1 (λ h, by dsimp only [c_star] at hi; rw h at hi;
    simpa [lt_irrefl] using hi),
have hi' : 0 < T'.to_matrix obj (option.get hi_some) * T.to_matrix i c,
  by dsimp only [c_star] at hi; rwa [← option.some_get hi_some] at hi,
have hir : i ≠ r, from λ hir, begin
    have : option.get hi_some = c', from T'.to_partition.injective_colg
      (by rw [colg_get_colp_symm, ← hs, hir]),
    rw [this, hir] at hi',
    exact not_lt_of_gt hi' (mul_neg_of_pos_of_neg hc'obj0 hrc0)
  end,
have hnec' : option.get hi_some ≠ c',
  from λ eq_c', hir $ @eq_of_roweqc' i (eq_c' ▸ by simp),
have hic0 : T.to_matrix i c < 0, from neg_of_mul_pos_right hi' (unique_col _ hnec'),
not_le_of_gt hic0 (unique_row i hir hi0)

inductive rel : tableau m n → tableau m n → Prop
| pivot : ∀ {T r c}, feasible T → c ∈ find_pivot_column T obj →
  r ∈ find_pivot_row T obj c → rel (T.pivot r c) T
| trans_pivot : ∀ {T₁ T₂ r c}, rel T₁ T₂ → c ∈ find_pivot_column T₁ obj →
  r ∈ find_pivot_row T₁ obj c → rel (T₁.pivot r c) T₂

lemma feasible_of_rel_right {T T' : tableau m n} (h : rel obj T' T) : T.feasible :=
rel.rec_on h (by tauto) (by tauto)

lemma feasible_of_rel_left {T T' : tableau m n} (h : rel obj T' T) : T'.feasible :=
rel.rec_on h (λ _ _ _ hT hc hr, feasible_of_mem_pivot_row_and_column hT hc hr)
  (λ _ _ _ _ _ hc hr hT, feasible_of_mem_pivot_row_and_column hT hc hr)

/-- Slightly stronger recursor than the default recursor -/
@[elab_as_eliminator]
lemma rel.rec_on' {obj : fin m} {C : tableau m n → tableau m n → Prop} {T T' : tableau m n}
  (hrel : rel obj T T')
  (hpivot : ∀ {T : tableau m n} {r : fin m} {c : fin n},
     feasible T → c ∈ find_pivot_column T obj → r ∈ find_pivot_row T obj c → C (pivot T r c) T)
  (hpivot_trans : ∀ {T₁ T₂ : tableau m n} {r : fin m} {c : fin n},
    rel obj (T₁.pivot r c) T₁ → rel obj T₁ T₂ →
     c ∈ find_pivot_column T₁ obj →
     r ∈ find_pivot_row T₁ obj c → C (T₁.pivot r c) T₁ → C T₁ T₂ → C (pivot T₁ r c) T₂) :
  C T T' :=
rel.rec_on hrel @hpivot (λ T₁ T₂ r c hrelT₁₂ hc hr ih, hpivot_trans
  (rel.pivot (feasible_of_rel_left obj hrelT₁₂) hc hr) hrelT₁₂ hc hr
  (hpivot (feasible_of_rel_left obj hrelT₁₂) hc hr) ih)

lemma rel.trans {obj : fin m} {T₁ T₂ T₃ : tableau m n} (h₁₂ : rel obj T₁ T₂) :
  rel obj T₂ T₃ → rel obj T₁ T₃ :=
rel.rec_on h₁₂
  (λ T r c hT hc hr hrelT, rel.trans_pivot hrelT hc hr)
  (λ T₁ T₂ r c hrelT₁₂ hc hr ih hrelT₂₃, rel.trans_pivot (ih hrelT₂₃) hc hr)

instance : is_trans (tableau m n) (rel obj) := ⟨@rel.trans _ _ obj⟩

lemma flat_eq_of_rel {T T' : tableau m n} (h : rel obj T' T) : flat T' = flat T :=
rel.rec_on' h (λ _ _ _ _ _ hr, flat_pivot (ne_zero_of_mem_find_pivot_row hr))
  (λ _ _ _ _ _ _ _ _, eq.trans)

lemma exists_mem_pivot_row_column_of_rel {T T' : tableau m n} (h : rel obj T' T) :
  ∃ r c, c ∈ find_pivot_column T obj ∧ r ∈ find_pivot_row T obj c :=
rel.rec_on' h (λ _ r c _ hc hr, ⟨r, c, hc, hr⟩) (λ _ _ _ _ _ _ _ _ _, id)

lemma exists_mem_pivot_row_of_rel {T T' : tableau m n} (h : rel obj T' T) {c : fin n}
  (hc : c ∈ find_pivot_column T obj) : ∃ r, r ∈ find_pivot_row T obj c :=
let ⟨r, c', hc', hr⟩ := exists_mem_pivot_row_column_of_rel obj h in ⟨r, by simp * at *⟩

lemma colg_eq_or_exists_mem_pivot_column {T₁ T₂ : tableau m n} (h : rel obj T₂ T₁) {c : fin n} :
  T₁.to_partition.colg c = T₂.to_partition.colg c ∨
  ∃ T₃, (T₃ = T₁ ∨ rel obj T₃ T₁) ∧ (rel obj T₂ T₃) ∧ c ∈ find_pivot_column T₃ obj :=
rel.rec_on' h begin
    assume T r c' hT hc' hr,
    by_cases hcc : c = c',
    { subst hcc,
      exact or.inr ⟨T, or.inl rfl, rel.pivot hT hc' hr, hc'⟩ },
    { simp [colg_swap_of_ne _ hcc] }
  end
  (λ T₁ T₂ r c hrelp₁ hrel₁₂ hc hr ihp₁ ih₁₂,
    ihp₁.elim
      (λ ihp₁, ih₁₂.elim
        (λ ih₁₂, or.inl (ih₁₂.trans ihp₁))
        (λ ⟨T₄, hT₄⟩, or.inr ⟨T₄, hT₄.1, hrelp₁.trans hT₄.2.1, hT₄.2.2⟩))
      (λ ⟨T₄, hT₄⟩, or.inr ⟨T₄, hT₄.1.elim (λ h, h.symm ▸ or.inr hrel₁₂)
        (λ h, or.inr $ h.trans hrel₁₂), hT₄.2.1, hT₄.2.2⟩))

lemma rowg_eq_or_exists_mem_pivot_row {T₁ T₂ : tableau m n} (h : rel obj T₂ T₁) (r : fin m) :
  T₁.to_partition.rowg r = T₂.to_partition.rowg r ∨
  ∃ (T₃ : tableau m n) c, (T₃ = T₁ ∨ rel obj T₃ T₁) ∧ (rel obj T₂ T₃) ∧
    T₃.to_partition.rowg r = T₁.to_partition.rowg r ∧
    c ∈ find_pivot_column T₃ obj ∧ r ∈ find_pivot_row T₃ obj c :=
rel.rec_on' h
  begin
    assume T r' c hT hc hr',
    by_cases hrr : r = r',
    { subst hrr,
      exact or.inr ⟨T, c, or.inl rfl, rel.pivot hT hc hr', rfl, hc, hr'⟩ },
    { simp [rowg_swap_of_ne _ hrr] }
  end
  (λ T₁ T₂ r c hrelp₁ hrel₁₂ hc hr ihp₁ ih₁₂,
    ih₁₂.elim
      (λ ih₁₂, ihp₁.elim
        (λ ihp₁, or.inl $ ih₁₂.trans ihp₁)
        (λ ⟨T₃, c', hT₃⟩, or.inr ⟨T₃, c', hT₃.1.elim (λ h, h.symm ▸ or.inr hrel₁₂)
           (λ h, or.inr $ h.trans hrel₁₂), hT₃.2.1, ih₁₂.symm ▸ hT₃.2.2.1, hT₃.2.2.2⟩))
      (λ ⟨T₃, c', hT₃⟩, or.inr ⟨T₃, c', hT₃.1,
        (rel.pivot (feasible_of_rel_left _ hrel₁₂) hc hr).trans hT₃.2.1, hT₃.2.2⟩))

-- lemma rowg_eq_or_exists_mem_pivot_row' {T₁ T₂ : tableau m n} (h : rel obj T₂ T₁) (r : fin m) :
--   T₁.to_partition.rowg r = T₂.to_partition.rowg r ∨
--   ∃ (T₃ : tableau m n) c, (T₃ = T₁ ∨ rel obj T₃ T₁) ∧ (rel obj T₂ T₃) ∧
--     T₃.to_partition.rowg r = T₁.to_partition.rowg r ∧
--     c ∈ find_pivot_column T₃ obj ∧ r ∈ find_pivot_row T₃ obj c :=
-- rel.rec_on' h
--   begin
--     assume T r' c hT hc hr',
--     by_cases hrr : r = r',
--     { subst hrr,
--       exact or.inr ⟨T, c, or.inl rfl, rel.pivot hT hc hr', rfl, hc, hr'⟩ },
--     { simp [rowg_swap_of_ne _ hrr] }
--   end
--   (λ T₁ T₂ r c hrelp₁ hrel₁₂ hc hr ihp₁ ih₁₂,
--     ih₁₂.elim
--       (λ ih₁₂, ihp₁.elim
--         (λ ihp₁, or.inl $ ih₁₂.trans ihp₁)
--         (λ ⟨T₃, c', hT₃⟩, or.inr ⟨T₃, c', hT₃.1.elim (λ h, h.symm ▸ or.inr hrel₁₂)
--            (λ h, or.inr $ h.trans hrel₁₂), hT₃.2.1, ih₁₂.symm ▸ hT₃.2.2.1, hT₃.2.2.2⟩))
--       (λ ⟨T₃, c', hT₃⟩, or.inr ⟨T₃, c', hT₃.1,
--         (rel.pivot (feasible_of_rel_left _ hrel₁₂) hc hr).trans hT₃.2.1, hT₃.2.2⟩))

lemma eq_or_rel_pivot_of_rel {T₁ T₂ : tableau m n} (h : rel obj T₁ T₂) : ∀ {r c}
  (hc : c ∈ find_pivot_column T₂ obj) (hr : r ∈ find_pivot_row T₂ obj c),
  T₁ = T₂.pivot r c ∨ rel obj T₁ (T₂.pivot r c) :=
rel.rec_on' h (λ T r c hT hc hr r' c' hc' hr', by simp * at *)
  (λ T₁ T₂ r c hrelp₁ hrel₁₂ hc hr ihp₁ ih₁₂ r' c' hc' hr',
    (ih₁₂ hc' hr').elim
      (λ ih₁₂, or.inr $ ih₁₂ ▸ rel.pivot (feasible_of_rel_left _ hrel₁₂) hc hr)
      (λ ih₁₂, or.inr $ (rel.pivot (feasible_of_rel_left _ hrel₁₂) hc hr).trans ih₁₂))

lemma offset_obj_le_of_rel {T₁ T₂ : tableau m n} (h : rel obj T₁ T₂) :
  T₂.offset obj 0 ≤ T₁.offset obj 0 :=
rel.rec_on' h (λ T r c hT hc hr,
    have hr' : _ := find_pivot_row_spec hr,
    simplex_offset_obj_le hT (by tauto) (by tauto))
  (λ _ _ _ _ _ _ _ _ h₁ h₂, le_trans h₂ h₁)

lemma offset_obj_eq_of_rel_of_rel {T₁ T₂ : tableau m n} (h₁₂ : rel obj T₁ T₂)
  (h₂₁ : rel obj T₂ T₁) : T₁.offset obj 0 = T₂.offset obj 0 :=
le_antisymm (offset_obj_le_of_rel _ h₂₁) (offset_obj_le_of_rel _ h₁₂)

lemma offset_eq_offset_of_offset_obj_eq_zero {T₁ T₂ : tableau m n} (h₁₂ : rel obj T₁ T₂) :
  ∀ (hobj : T₁.offset obj 0 = T₂.offset obj 0) (i : fin m), T₁.offset i 0 = T₂.offset i 0 :=
rel.rec_on' h₁₂
  (λ T r c hfT hc hr hobj i,
    have hr0 : T.offset r 0 = 0, from offset_eq_zero_of_offset_obj_eq hfT
      (ne_zero_of_mem_find_pivot_column hc) (ne_zero_of_mem_find_pivot_row hr)
      (find_pivot_row_spec hr).1 hobj,
    if hir : i = r
      then by simp [hir, hr0]
      else by simp [offset_pivot_of_ne _ hir, hr0])
  (λ T₁ T₂ r c hrelp₁ hrel₁₂ hc hr ihp₁ ih₁₂ hobj i,
    have hobjp : (pivot T₁ r c).offset obj 0 = T₁.offset obj 0,
      from le_antisymm (hobj.symm ▸ offset_obj_le_of_rel _ hrel₁₂)
        (offset_obj_le_of_rel _ hrelp₁),
    by rw [ihp₁ hobjp, ih₁₂ (hobjp.symm.trans hobj)])

lemma offset_eq_zero_of_rel_of_rel_of_rel_of_rel {T₁ T₂ : tableau m n} (h₁₂ : rel obj T₁ T₂) :
  ∀ (h₂₁ : rel obj T₂ T₁) (T₃ : tableau m n)
  (h₁₃ : T₁ = T₃ ∨ rel obj T₁ T₃) (h₃₂ : T₃ = T₂ ∨ rel obj T₃ T₂)
  {r c} (hc : c ∈ find_pivot_column T₃ obj)
  (hr : r ∈ find_pivot_row T₃ obj c), T₃.offset r 0 = 0 :=
rel.rec_on' h₁₂
  (λ T r c hfT hc hr hrelp T₃ hrelp₃ hrel₃₁ r' c' hc' hr',
    have hfT₃ : feasible T₃, from hrel₃₁.elim (λ h, h.symm ▸ hfT) (feasible_of_rel_left _),
    offset_eq_zero_of_offset_obj_eq hfT₃ (ne_zero_of_mem_find_pivot_column hc')
      (ne_zero_of_mem_find_pivot_row hr')
      (find_pivot_row_spec hr').1
      (offset_obj_eq_of_rel_of_rel _
        (rel.pivot hfT₃ hc' hr')
        (hrel₃₁.elim (λ h, by simp * at *)
          (λ hrel₃₁, hrelp₃.elim
            (λ h, begin
                subst h,
                cases eq_or_rel_pivot_of_rel _ hrelp hc' hr',
                { rw ← h, exact rel.pivot hfT hc hr },
                { exact (rel.pivot hfT hc hr).trans h }
              end)
            (λ hrelp₃, hrel₃₁.trans ((eq_or_rel_pivot_of_rel _ hrelp₃ hc' hr').elim
              (λ h, h ▸ hrelp) hrelp.trans))))))
  (λ T₁ T₂ r c hrelp₁ hrel₁₂ hc hr ihp₁ ih₁₂ hrel₂p T₃ hrelp₁₃ hrel₃₂ r' c' hc' hr',
    ihp₁ (hrel₁₂.trans hrel₂p) _ hrelp₁₃
      (or.inr (hrel₃₂.elim (λ h, h.symm ▸ hrel₂p.trans hrelp₁)
        (λ h, h.trans (hrel₂p.trans hrelp₁))))
      hc' hr')

lemma offset_eq_zero_of_rel_of_rel_of_rel_of_rel {T₁ T₂ : tableau m n} (h₁₂ : rel obj T₁ T₂) :
  ∀ (h₂₁ : rel obj T₂ T₁) (T₃ : tableau m n)
  (h₁₃ : T₁ = T₃ ∨ rel obj T₁ T₃) (h₃₂ : T₃ = T₂ ∨ rel obj T₃ T₂)
  {r c} (hc : c ∈ find_pivot_column T₃ obj)
  (hr : r ∈ find_pivot_row T₃ obj c), T₁.offset r 0 = 0 :=
rel.rec_on' h₁₂
  (λ T r c hfT hc hr hrelp T₃ hrelp₃ hrel₃₁ r' c' hc' hr',
    hrelp₃.elim sorry _)
  (λ T₁ T₂ r c hrelp₁ hrel₁₂ hc hr ihp₁ ih₁₂ hrel₂p T₃ hrelp₁₃ hrel₃₂ r' c' hc' hr',
    ihp₁ (hrel₁₂.trans hrel₂p) _ hrelp₁₃
      (or.inr (hrel₃₂.elim (λ h, h.symm ▸ hrel₂p.trans hrelp₁)
        (λ h, h.trans (hrel₂p.trans hrelp₁))))
      hc' hr')

lemma offset_eq_zero_of_rowg_ne_of_rel_self {T T' : tableau m n} (hrelTT' : rel obj T T') : ∀
  (hrelT'T : rel obj T' T) (i : fin m) (hrow : T.to_partition.rowg i ≠ T'.to_partition.rowg i),
  T.offset i 0 = 0 :=
rel.rec_on' hrelTT'
  (begin
    intros,
    exact offset_eq_zero_of_rel_of_rel_of_rel_of_rel obj _ _ _ _ _ _ _,

  end)
  _


lemma offset_eq_zero_of_rowg_ne_of_offset_obj_eq {T₁ T₂ : tableau m n} (h₂₁ : rel obj T₂ T₁)
  (hobj : T₁.offset obj 0 = T₂.offset obj 0) (i : fin m)
  (hrow : T₁.to_partition.rowg i ≠ T₂.to_partition.rowg i) : T₁.offset i 0 = 0 :=
let ⟨T₃, c, hT₃₁, hT₃₂, hrow, hc, hi⟩ := (
  rowg_eq_or_exists_mem_pivot_row obj h₂₁ _).resolve_left hrow in
have h₃obj : (T₃.pivot i c).offset obj 0 = T₃.offset obj 0,
  from le_antisymm
    (calc (T₃.pivot i c).offset obj 0 ≤ T₂.offset obj 0 :
        (eq_or_rel_pivot_of_rel obj hT₃₂ hc hi).elim (λ h, h ▸ le_refl _)
          (offset_obj_le_of_rel _)
      ... = T₁.offset obj 0 : hobj.symm
      ... ≤ T₃.offset obj 0 : hT₃₁.elim (λ h, h ▸ le_refl _) (offset_obj_le_of_rel _))
    (offset_obj_le_of_rel _ (rel.pivot (feasible_of_rel_right _ hT₃₂) hc hi)),
have hT₃i : T₃.offset i 0 = 0, from offset_eq_zero_of_offset_obj_eq (feasible_of_rel_right _ hT₃₂)
  (ne_zero_of_mem_find_pivot_column hc) (ne_zero_of_mem_find_pivot_row hi)
  (find_pivot_row_spec hi).1 h₃obj,
rel.rec_on' (show rel obj T₁ T₃, from sorry) _
  begin
    assume T₁ T₂ r c hrelp₁ hrel₁₂ hc hr ihp₁ ih₁₂,

  end hrow hT₃i

lemma offset_eq_zero_of_rel_of_rel {T₁ T₂ : tableau m n} (h₂₁ : rel obj T₂ T₁) : ∀
  (h₁₂ : rel obj T₁ T₂) (i : fin m)
  (hrow : T₁.to_partition.rowg i ≠ T₂.to_partition.rowg i), T₁.offset i 0 = 0 :=
rel.rec_on' h₂₁
  (λ T r c hfT hc hr hrel₁p i hrow,
    have hir : i = r, from by_contradiction (λ hir, by simpa [rowg_swap_of_ne _ hir] using hrow),
    have hobjr : obj ≠ r, from (find_pivot_row_spec hr).1,
    hir.symm ▸ offset_eq_zero_of_offset_obj_eq hfT
      (λ h : T.to_matrix obj c = 0, by simpa [h, lt_irrefl] using find_pivot_column_spec hc)
      (ne_zero_of_mem_find_pivot_row hr) hobjr
        (offset_obj_eq_of_rel_of_rel _ (rel.pivot hfT hc hr) hrel₁p))
  (λ T₁ T₂ r c hrelp₁ hrel₁₂ hc hr  ihp₁ ih₁₂ h₁₂ i hrow,
    if hir : i = r
      then begin
        have := offset_obj_eq_of_rel_of_rel obj hrelp₁ (hrel₁₂.trans h₁₂),
        have := offset_eq_zero_of_offset_obj_eq _ _ _ _ this,

      end
      else _)

instance : is_irrefl (tableau m n) (rel obj) := is_irrefl.mk $
λ T1 hrelT1,
let ⟨rT1 , cT1, hrT1, hcT1⟩ := exists_mem_pivot_row_column_of_rel obj hrelT1 in
let ⟨t, ht⟩ := finset.max_of_mem
  (show T1.to_partition.colg cT1 ∈ univ.filter (λ v, ∃ (T' : tableau m n) (c : fin n),
      rel obj T' T' ∧ c ∈ find_pivot_column T' obj ∧ T'.to_partition.colg c = v),
    by simp only [true_and, mem_filter, mem_univ, exists_and_distrib_left];
      exact ⟨T1, hrelT1, cT1, hrT1, rfl⟩) in
let ⟨_, T', c', hrelTT'', hcT', hct⟩ := finset.mem_filter.1 (finset.mem_of_max ht) in
have htmax : ∀ (s : fin (m + n)) (T : tableau m n),
    rel obj T T → ∀ (j : fin n), find_pivot_column T obj = some j →
      T.to_partition.colg j = s → s ≤ t,
  by simpa using λ s (h : s ∈ _), finset.le_max_of_mem h ht,
let ⟨r, hrT'⟩ := exists_mem_pivot_row_of_rel obj hrelTT'' hcT' in
have hrelTT''p : rel obj T' (T'.pivot r c'),
  from (eq_or_rel_pivot_of_rel obj hrelTT'' hcT' hrT').elim (λ h, h ▸ hrelTT'') id,
let ⟨T, c, hTT', hrelT'T, hT'Tr, hc, hr⟩ := (rowg_eq_or_exists_mem_pivot_row obj
  hrelTT''p r).resolve_left (by simp) in
have hfT' : feasible T', from feasible_of_rel_left _ hrelTT'',
have hfT : feasible T, from feasible_of_rel_right _ hrelT'T,
have hrelT'pT' : rel obj (T'.pivot r c') T', from rel.pivot hfT' hcT' hrT',
have hrelTT' : rel obj T T', from hTT'.elim (λ h, h.symm ▸ hrelT'pT') (λ h, h.trans hrelT'pT'),
have hrelTT : rel obj T T, from hrelTT'.trans hrelT'T,
have hc't : T.to_partition.colg c ≤ t, from htmax _ T hrelTT _ hc rfl,
have hoT'T : T'.offset obj 0 = T.offset obj 0, from offset_obj_eq_of_rel_of_rel _ hrelT'T hrelTT',
begin
  clear_,
  clear hrelT1 hrT1 hcT1 T1 rT1 cT1 ht,
  subst hct,


end

end blands_rule

inductive termination : Type
| while     : termination
| unbounded : termination
| maximised : termination

open termination

instance termination.decidable_eq : decidable_eq termination := by tactic.mk_dec_eq_instance

instance : has_repr termination := ⟨λ t, termination.cases_on t "while" "unbounded" "maximised"⟩

instance : fintype termination := ⟨⟨quotient.mk [while, unbounded, maximised], dec_trivial⟩,
  λ x, by cases x; exact dec_trivial⟩

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

@[simp] lemma feasible_simplex {w : tableau m n → bool} {T : tableau m n}
  {hT : feasible T} {obj : fin m} : feasible (T.simplex w hT obj).1 :=
simplex_induction feasible _ hT _ hT
  (λ _ _ _ _ hc hr _ hT', feasible_of_mem_pivot_row_and_column hT' hc hr)

@[simp] lemma simplex_simplex {w : tableau m n → bool} {T : tableau m n} {hT : feasible T}
  {obj : fin m} : (T.simplex w hT obj).1.simplex w feasible_simplex obj = T.simplex w hT obj :=
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

@[simp] lemma of_col_simplex_zero_mem_sol_set {w : tableau m n → bool} {T : tableau m n}
  {hT : feasible T} {obj : fin m} : (T.simplex w hT obj).1.of_col 0 ∈ sol_set T :=
by rw [← sol_set_simplex, of_col_zero_mem_sol_set_iff]; exact feasible_simplex

@[simp] lemma of_col_simplex_rowg {w : tableau m n → bool} {T : tableau m n}
  {hT : feasible T} {obj : fin m} (x : cvec n) :
  (T.simplex w hT obj).1.of_col x (T.to_partition.rowg obj) =
  ((T.simplex w hT obj).1.to_matrix ⬝ x + (T.simplex w hT obj).1.offset) obj :=
by rw [← of_col_rowg (T.simplex w hT obj).1 x obj, rowg_simplex]

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

open tableau.simplex tableau.simplex.termination
#print acc
-- /-- Boolean returning whether or not it is consistent to make `obj` nonnegative.
--   Only makes sense for feasible tableaux. -/
-- def max_nonneg (T : tableau m n) (hT : feasible T) (obj : fin m) : bool :=
-- let T' := T.simplex (λ T', T'.offset obj 0 < 0) hT obj in
-- match T'.2 with
-- | while     := tt
-- | unbounded := tt
-- | maximised := ff
-- end

-- lemma max_nonneg_iff {T : tableau m n} {hT : T.feasible} {obj : fin m} :
--   max_nonneg T hT obj ↔ ∃ x : cvec (m + n), x ∈ T.sol_set ∧ 0 ≤ x (T.to_partition.rowg obj) 0 :=
-- let T' := T.simplex (λ T', T'.offset obj 0 < 0) hT obj in
-- begin
--   cases h : T'.2,
--   { simp only [max_nonneg, h, bool.coe_sort_tt, coe_tt, true_iff],
--     rw [termination_eq_while_iff] at h,
--     use T'.1.of_col 0,
--     simpa [T'] using h },
--   { simp only [max_nonneg, h, bool.coe_sort_tt, coe_tt, true_iff],
--     rw [termination_eq_unbounded_iff, is_unbounded_above] at h,
--     tauto },
--   { simp only [max_nonneg, h, not_exists, false_iff, not_and, bool.coe_sort_ff, not_le],
--     rw [termination_eq_maximised_iff, is_maximised, to_bool_iff] at h,
--     assume x hx,
--     refine lt_of_le_of_lt _ h.1,
--     simpa using h.2 x hx }
-- end

section sign_of_max_row

def sign_of_max_row (T : tableau m n) (hT : feasible T) (obj : fin m) : ℤ :=
let T' := T.simplex (λ T', T'.offset obj 0 ≤ 0) hT obj in
match T'.2 with
| while     := 1
| unbounded := 1
| maximised := if T'.1.offset obj 0 = 0 then 0 else -1
end

lemma sign_of_max_row_eq_zero {T : tableau m n} {hT : feasible T} {obj : fin m} :
  sign_of_max_row T hT obj = 0 ↔
    ∃ x : cvec (m + n), x ∈ sol_set T ∧ (x (T.to_partition.rowg obj) 0 = 0) ∧ is_maximised T x
      (T.to_partition.rowg obj) :=
let T' := T.simplex (λ T', T'.offset obj 0 ≤ 0) hT obj in
begin
  cases h : T'.2,
  { simp only [sign_of_max_row, *, termination_eq_while_iff, is_maximised, classical.not_forall,
      not_exists, exists_prop, false_iff, not_and, not_le, to_bool_ff_iff, one_ne_zero] at *,
    assume x hxs hx,
    use [T'.1.of_col 0],
    simpa [T', hx] },
  { simp only [sign_of_max_row, *, termination_eq_unbounded_iff, is_unbounded_above,
      classical.not_forall, not_exists, exists_prop, false_iff, not_and, not_le, to_bool_iff,
      one_ne_zero, is_maximised] at * {contextual := tt},
    cases h.2 1 with y hy,
    assume x hxs hx,
    use [y, hy.1],
    exact lt_of_lt_of_le zero_lt_one hy.2 },
  { simp only [sign_of_max_row, *, termination_eq_maximised_iff, is_unbounded_above,
      classical.not_forall, not_exists, exists_prop, false_iff, not_and, not_le, to_bool_iff,
      one_ne_zero] at * {contextual := tt},
    split_ifs with h0,
    { simp only [eq_self_iff_true, true_iff],
      refine ⟨_, _, _, h.2⟩;
      simp [h0] },
    { simp only [is_maximised, not_exists, neg_eq_zero, one_ne_zero, false_iff, not_and],
      assume x hsx hx,
      exact absurd (le_antisymm h.1 (by simpa [hx] using h.2 x hsx)) h0 } }
end

lemma sign_of_max_row_eq_one {T : tableau m n} {hT : feasible T} {obj : fin m} :
  sign_of_max_row T hT obj = 1 ↔
    ∃ x : cvec (m + n), x ∈ sol_set T ∧ 0 < x (T.to_partition.rowg obj) 0 :=
let T' := T.simplex (λ T', T'.offset obj 0 ≤ 0) hT obj in
begin
  cases h : T'.2,
  { simp only [sign_of_max_row, *, termination_eq_while_iff, eq_self_iff_true, true_iff,
      to_bool_ff_iff, not_le] at *,
    exact ⟨T'.1.of_col 0, by simp *⟩ },
  { simp only [sign_of_max_row, *, termination_eq_unbounded_iff, eq_self_iff_true,
      true_iff, to_bool_iff] at *,
    cases h.2 1 with y hy,
    use [y, hy.1],
    exact lt_of_lt_of_le zero_lt_one hy.2 },
  { simp only [sign_of_max_row, *, termination_eq_maximised_iff, to_bool_iff] at *,
    suffices : ∀ (x : matrix (fin (m + n)) (fin 1) ℚ), x ∈ sol_set T →
      x (T.to_partition.rowg obj) 0 ≤ 0,
    { split_ifs; simpa [show ¬(-1 : ℤ) = 1, from dec_trivial] },
    assume x hx,
    exact le_trans (h.2 x hx) (by simpa using h.1) }
end

lemma sign_of_max_row_eq_neg_one {T : tableau m n} {hT : feasible T} {obj : fin m} :
  sign_of_max_row T hT obj = -1 ↔
    ∀ x : cvec (m + n), x ∈ sol_set T → x (T.to_partition.rowg obj) 0 < 0 :=
let T' := T.simplex (λ T', T'.offset obj 0 ≤ 0) hT obj in
begin
  cases h : T'.2,
  { simp only [sign_of_max_row, *, termination_eq_while_iff, false_iff, classical.not_forall,
      not_lt, show (1 : ℤ) ≠ -1, from dec_trivial, to_bool_ff_iff, not_le] at *,
    use T'.1.of_col 0,
    simp [le_of_lt h] },
  { simp only [sign_of_max_row, *, termination_eq_unbounded_iff, false_iff, classical.not_forall,
      show (1 : ℤ) ≠ -1, from dec_trivial, to_bool_iff, not_lt, not_le] at *,
    cases h.2 1 with y hy,
    use [y, hy.1],
    exact le_trans zero_le_one hy.2 },
  { simp only [sign_of_max_row, *, termination_eq_maximised_iff, to_bool_iff] at *,
    split_ifs,
    { simp [show (0 : ℤ) ≠ -1, from dec_trivial, classical.not_forall],
      use T'.1.of_col 0, simp * },
    { simp only [eq_self_iff_true, true_iff],
      assume x hx,
      exact lt_of_le_of_lt (h.2 x hx) (by apply lt_of_le_of_ne; simp; tauto) } }
end

end sign_of_max_row

section to_row

def to_row_pivot_row (T : tableau m n) (c : fin n) : option (fin m) :=
((list.fin_range m).filter (λ r, (T.to_partition.rowg r ∈ T.restricted ∧
  T.to_matrix r c < 0))).argmax (λ r, T.offset r 0 / T.to_matrix r c)

lemma feasible_to_row_pivot_row {T : tableau m n} (hT : feasible T) {r} (c : fin n)
  (hr : r ∈ to_row_pivot_row T c) : feasible (T.pivot r c) :=
begin
  simp only [to_row_pivot_row, list.mem_argmax_iff, list.mem_filter] at hr,
  refine feasible_pivot hT (by tauto) (by tauto) _,
  assume i hir hir0,
  have hic0 : T.to_matrix i c < 0,
    from neg_of_mul_pos_left hir0 (inv_nonpos.2 $ le_of_lt $ by tauto),
  rw [abs_of_nonpos (div_nonpos_of_nonneg_of_neg (hT _ hir) hic0),
    abs_of_nonpos (div_nonpos_of_nonneg_of_neg (hT r (by tauto)) hr.1.2.2), neg_le_neg_iff],
  apply hr.2.1,
  simp,
  tauto
end

def to_row (T : tableau m n) (hT : feasible T) (c : fin n) : option (tableau m n) :=
to_row_pivot_row T c >>= λ r, T.pivot r c



end to_row


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
-- { to_matrix := list.to_matrix 4 5 [[-1, -3/4, 20, -1/2, 6], [0, 1/4, -8, -1, 9],
--     [0, 1/2, -12, -1/2, 3], [0,0,0,1,0]],
--   offset := (list.to_matrix 1 4 [[0,0,0,1]])ᵀ,
--   to_partition := default _,
--   restricted := univ }

-- def T : tableau 4 5 :=
-- { to_matrix := list.to_matrix 4 5 [[1, 3/5, 20, 1/2, -6], [19, 1, -8, -1, 9],
--     [5, 1/2, -12, 1/2, 3], [13,0.1,11,21,0]],
--   offset := (list.to_matrix 1 4 [[3,1,51,1]])ᵀ,
--   to_partition := default _,
--   restricted := univ }
-- set_option profiler true
-- #print tactic.eval_expr
def T : tableau 25 10 :=
{ to_matrix := list.to_matrix 25 10
    [[0, 0, 0, 0, 1, 0, 1, 0, 1, -1], [-1, 1, 0, -1, 1, 0, 1, -1, 0, 0], [0, -1, 1, 1, 1, 0, 0, 0, 1, 0], [1, 1, 1, 0, 1, -1, 1, -1, 1, -1], [0, 1, 1, -1, -1, 1, -1, 1, -1, 1], [0, -1, 1, -1, 1, 1, 0, 1, 0, -1], [-1, 0, 0, -1, -1, 1, 1, 0, -1, -1], [-1, 0, 0, -1, 0, -1, 0, 0, -1, 1], [-1, 0, 0, 1, -1, 1, -1, -1, 1, 0], [1, 0, 0, 0, 1, -1, 1, 0, -1, 1], [0, -1, 1, 0, 0, 1, 0, -1, 0, 0], [-1, 1, -1, 1, 1, 0, 1, 0, 1, 0], [1, 1, 1, 1, -1, 0, 0, 0, -1, 0], [-1, -1, 0, 0, 1, 0, 1, 1, -1, 0], [0, 0, -1, 1, -1, 0, 0, 1, 0, -1], [-1, 0, -1, 1, 1, 1, 0, 0, 0, 0], [1, 0, -1, 1, 0, -1, -1, 1, -1, 1], [-1, 1, -1, 1, -1, -1, -1, 1, -1, 1], [-1, 0, 0, 0, 1, -1, 1, -1, -1, 1], [-1, -1, -1, 1, 0, 1, -1, 1, 0, 0], [-1, 0, 0, 0, -1, -1, 1, -1, 0, 1], [-1, 0, 0, -1, 1, 1, 1, -1, 1, 0], [0, -1, 0, 0, 0, -1, 0, 1, 0, -1], [1, -1, 1, 0, 0, 1, 0, 1, 0, -1], [0, -1, -1, 0, 0, 0, -1, 0, 1, 0]],
  offset := λ i _, if i.1 < 5 then 0 else 1,
  to_partition := default _,
  restricted := univ }

-- #eval tableau.sizeof _ _ T
-- #print tc.rec

-- #eval 1000 * 1000

-- run_cmd do tactic.is_def_eq `(1000000) `(1000 * 1000)


--#reduce let s := T.simplex (λ _, tt) dec_trivial 0 in s.2

#eval let s := T.simplex (λ _, tt) dec_trivial 0 in
(s.2, s.1.to_partition.row_indices.1, s.1.offset)

-- (s.2, s.1.offset 0 0, s.1.to_partition.row_indices.1)

end test
