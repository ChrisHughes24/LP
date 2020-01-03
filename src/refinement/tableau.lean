import data.matrix.pequiv data.rat.basic tactic.fin_cases data.list.min_max partition .tableau_class

open matrix fintype finset function pequiv is_tableau

local notation `rvec`:2000 n := matrix (fin 1) (fin n) ℚ
local notation `cvec`:2000 m := matrix (fin m) (fin 1) ℚ
local infix ` ⬝ `:70 := matrix.mul
local postfix `ᵀ` : 1500 := transpose

variables {m n : ℕ}
variables {X : ℕ → ℕ → Type} [is_tableau X]

namespace is_tableau
open partition

section predicates

variable (T : X m n)

/-- The affine subspace represented by the tableau ignoring nonnegativity restrictiions -/
def flat : set (cvec (m + n)) :=
{ x | (to_partition T).rowp.to_matrixᵀ ⬝ x = (to_matrix T) ⬝ (to_partition T).colp.to_matrixᵀ ⬝ x + (const T) }

/-- The res_set is the subset of ℚ^(m+n) that satisifies the nonnegativity constraints of
  the tableau, and the affine conditions -/
def res_set : set (cvec (m + n)) := flat T ∩ { x | ∀ i, i ∈ (restricted T) → 0 ≤ x i 0 }

/-- The dead_set is the subset of ℚ^(m+n) such that all dead variables are zero, and satisfies
  the affine conditions -/
def dead_set : set (cvec (m + n)) :=
flat T ∩ { x | ∀ j, j ∈ (dead T) → x ((to_partition T).colg j) 0 = 0 }

/-- The `sol_set` is the set of vector that satisfy the affine constraints the dead variable
  constraints, and the nonnegativity constraints. -/
def sol_set : set (cvec (m + n)) :=
res_set T ∩ { x | ∀ j, j ∈ (dead T) → x ((to_partition T).colg j) 0 = 0 }

lemma sol_set_eq_res_set_inter :
  (sol_set T) = res_set T ∩ { x | ∀ j, j ∈ (dead T) → x ((to_partition T).colg j) 0 = 0 } := rfl

lemma sol_set_eq_dead_set_inter :
   (sol_set T) = dead_set T ∩ { x | ∀ i, i ∈ (restricted T) → 0 ≤ x i 0 } :=
set.inter_right_comm _ _ _

lemma sol_set_eq_res_set_inter_dead_set : (sol_set T) = (res_set T) ∩ (dead_set T) :=
by simp [sol_set, res_set, dead_set, set.ext_iff]; tauto

/-- Predicate for a variable being unbounded above in the `res_set` -/
def is_unbounded_above (i : fin (m + n)) : Prop :=
∀ q : ℚ, ∃ x : cvec (m + n), x ∈ sol_set T ∧ q ≤ x i 0

/-- Predicate for a variable being unbounded below in the `res_set` -/
def is_unbounded_below (i : fin (m + n)) : Prop :=
∀ q : ℚ, ∃ x : cvec (m + n), x ∈ sol_set T ∧ x i 0 ≤ q

def is_optimal (x : cvec (m + n)) (i : fin (m + n)) : Prop :=
x ∈ (sol_set T) ∧ ∀ y : cvec (m + n), y ∈ sol_set T → y i 0 ≤ x i 0

/-- Is this equivalent to `∀ (x : cvec (m + n)), x ∈ res_set T → x i 0 = x j 0`? No -/
def equal_in_flat (i j : fin (m + n)) : Prop :=
∀ (x : cvec (m + n)), x ∈ flat T → x i 0 = x j 0

/-- Returns an element of the `flat` after assigning values to the column variables -/
def of_col (T : X m n) (x : cvec n) : cvec (m + n) :=
(to_partition T).colp.to_matrix ⬝ x + (to_partition T).rowp.to_matrix ⬝ ((to_matrix T) ⬝ x + (const T))

/-- A `tableau` is feasible if its `const` column is nonnegative in restricted rows -/
def feasible : Prop :=
∀ i, (to_partition T).rowg i ∈ (restricted T) → 0 ≤ (const T) i 0

instance : decidable_pred (@feasible m n X _) := λ _, by dunfold feasible; apply_instance

end predicates

section predicate_lemmas
variable {T : X m n}

-- @[simp] lemma eta : tableau.mk (to_partition T) (to_matrix T) (const T) (restricted T) (dead T) = T :=
-- by cases T; refl

lemma mem_flat_iff {x : cvec (m + n)} : x ∈ (flat T) ↔
  ∀ r, x ((to_partition T).rowg r) 0 = univ.sum
    (λ c : fin n, (to_matrix T) r c * x ((to_partition T).colg c) 0) +
  (const T) r 0 :=
have hx : x ∈ (flat T) ↔ ∀ i, ((to_partition T).rowp.to_matrixᵀ ⬝ x) i 0 =
    ((to_matrix T) ⬝ (to_partition T).colp.to_matrixᵀ ⬝ x + (const T)) i 0,
  by rw [flat, set.mem_set_of_eq, matrix.ext_iff.symm, forall_swap,
      unique.forall_iff];
    refl,
begin
  rw hx,
  refine forall_congr (λ i, _),
  rw [← to_matrix_symm, mul_matrix_apply, add_val, rowp_symm_eq_some_rowg,
    matrix.mul_assoc, matrix.mul],
  conv in ((to_matrix T) _ _ * ((to_partition T).colp.to_matrixᵀ ⬝ x) _ _)
  { rw [← to_matrix_symm, mul_matrix_apply, colp_symm_eq_some_colg] }
end

variable (T)

@[simp] lemma colp_mul_of_col (x : cvec n) :
  (to_partition T).colp.to_matrixᵀ ⬝ of_col T x = x :=
by simp [matrix.mul_assoc, matrix.mul_add, of_col, flat,
    mul_right_eq_of_mul_eq (rowp_transpose_mul_colp _),
    mul_right_eq_of_mul_eq (rowp_transpose_mul_rowp _),
    mul_right_eq_of_mul_eq (colp_transpose_mul_colp _),
    mul_right_eq_of_mul_eq (colp_transpose_mul_rowp _)]

@[simp] lemma rowp_mul_of_col (x : cvec n) :
  (to_partition T).rowp.to_matrixᵀ ⬝ of_col T x = (to_matrix T) ⬝ x + (const T) :=
by simp [matrix.mul_assoc, matrix.mul_add, of_col, flat,
    mul_right_eq_of_mul_eq (rowp_transpose_mul_colp _),
    mul_right_eq_of_mul_eq (rowp_transpose_mul_rowp _),
    mul_right_eq_of_mul_eq (colp_transpose_mul_colp _),
    mul_right_eq_of_mul_eq (colp_transpose_mul_rowp _)]

lemma of_col_mem_flat (x : cvec n) : (of_col T) x ∈ (flat T) :=
by simp [matrix.mul_assoc, matrix.mul_add, flat]

@[simp] lemma of_col_colg (x : cvec n) (c : fin n) :
  of_col T x ((to_partition T).colg c) = x c :=
funext $ λ v,
  calc of_col T x ((to_partition T).colg c) v =
      ((to_partition T).colp.to_matrixᵀ ⬝ of_col T x) c v :
    by rw [← to_matrix_symm, mul_matrix_apply, colp_symm_eq_some_colg]
  ... = x c v : by rw [colp_mul_of_col]

lemma of_col_rowg (c : cvec n) (r : fin m) :
  of_col T c ((to_partition T).rowg r) = ((to_matrix T) ⬝ c + (const T)) r :=
funext $ λ v,
  calc of_col T c ((to_partition T).rowg r) v =
      ((to_partition T).rowp.to_matrixᵀ ⬝ of_col T c) r v :
     by rw [← to_matrix_symm, mul_matrix_apply, rowp_symm_eq_some_rowg]
  ... = ((to_matrix T) ⬝ c + (const T)) r v : by rw [rowp_mul_of_col]

variable {T}

lemma of_col_single_rowg {q : ℚ} {r c} {k} :
  (of_col T) (q • (single c 0).to_matrix) ((to_partition T).rowg r) k =
    q * (to_matrix T) r c + (const T) r k:=
begin
  fin_cases k,
  erw [of_col_rowg, matrix.mul_smul, matrix.add_val, matrix.smul_val,
    matrix_mul_apply, pequiv.symm_single_apply]
end

/-- Condition for the solution given by setting column index `j` to `q` and all other columns to
  zero being in the `res_set` -/
lemma of_col_single_mem_res_set {q : ℚ} {c : fin n} (hT : (feasible T))
  (hi : ∀ i, (to_partition T).rowg i ∈ (restricted T) → 0 ≤ q * (to_matrix T) i c)
  (hj : (to_partition T).colg c ∉ (restricted T) ∨ 0 ≤ q) :
  (of_col T) (q • (single c 0).to_matrix) ∈ (res_set T) :=
⟨of_col_mem_flat _ _,
  λ v, ((to_partition T).eq_rowg_or_colg v).elim
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

lemma of_col_single_mem_sol_set {q : ℚ} {c : fin n} (hT : (feasible T))
  (hi : ∀ i, (to_partition T).rowg i ∈ (restricted T) → 0 ≤ q * (to_matrix T) i c)
  (hj : (to_partition T).colg c ∉ (restricted T) ∨ 0 ≤ q) (hdead : c ∉ (dead T) ∨ q = 0):
  (of_col T) (q • (single c 0).to_matrix) ∈ (sol_set T) :=
⟨of_col_single_mem_res_set hT hi hj,
  λ j hj, classical.by_cases
    (λ hjc : j = c, by subst hjc; simp * at *)
    (λ hjc : j ≠ c, by simp [smul_val, pequiv.single, pequiv.to_matrix, hjc])⟩

@[simp] lemma of_col_zero_mem_res_set_iff : (of_col T) 0 ∈ (res_set T) ↔ (feasible T) :=
suffices (∀ v : fin (m + n), v ∈ (restricted T) → (0 : ℚ) ≤ (of_col T) 0 v 0) ↔
    (∀ i : fin m, (to_partition T).rowg i ∈ (restricted T) → 0 ≤ (const T) i 0),
  by simpa [res_set, feasible, of_col_mem_flat],
⟨λ h i hi, by simpa [of_col_rowg] using h _ hi,
  λ h v hv, ((to_partition T).eq_rowg_or_colg v).elim
    (by rintros ⟨i, hi⟩; subst hi; simp [of_col_rowg]; tauto)
    (by rintros ⟨j, hj⟩; subst hj; simp)⟩

@[simp] lemma of_col_zero_mem_sol_set_iff : (of_col T) 0 ∈ (sol_set T) ↔ (feasible T) :=
by simp [sol_set,  of_col_zero_mem_res_set_iff]

lemma is_unbounded_above_colg_aux {c : fin n} (hT : (feasible T)) (hdead : c ∉ (dead T))
  (h : ∀ i : fin m, (to_partition T).rowg i ∈ (restricted T) → 0 ≤ (to_matrix T) i c) (q : ℚ) :
  of_col T (max q 0 • (single c 0).to_matrix) ∈ sol_set T ∧
    q ≤ of_col T (max q 0 • (single c 0).to_matrix) ((to_partition T).colg c) 0 :=
⟨of_col_single_mem_sol_set hT (λ i hi, mul_nonneg (le_max_right _ _) (h _ hi))
    (or.inr (le_max_right _ _)) (or.inl hdead),
  by simp [of_col_colg, smul_val, pequiv.single, pequiv.to_matrix, le_refl q]⟩

/-- A column variable is unbounded above if it is in a column where every negative entry is
  in a row owned by an unrestricted variable -/
lemma is_unbounded_above_colg {c : fin n} (hT : (feasible T)) (hdead : c ∉ (dead T))
  (h : ∀ i : fin m, (to_partition T).rowg i ∈ (restricted T) → 0 ≤ (to_matrix T) i c) :
  (is_unbounded_above T) ((to_partition T).colg c) :=
λ q, ⟨_, is_unbounded_above_colg_aux hT hdead h q⟩

lemma is_unbounded_below_colg_aux {c : fin n} (hT : (feasible T))
  (hres : (to_partition T).colg c ∉ (restricted T)) (hdead : c ∉ (dead T))
  (h : ∀ i : fin m, (to_partition T).rowg i ∈ (restricted T) → (to_matrix T) i c ≤ 0) (q : ℚ) :
  of_col T (min q 0 • (single c 0).to_matrix) ∈ sol_set T ∧
    of_col T (min q 0 • (single c 0).to_matrix) ((to_partition T).colg c) 0 ≤ q :=
⟨of_col_single_mem_sol_set hT
    (λ i hi, mul_nonneg_of_nonpos_of_nonpos (min_le_right _ _) (h _ hi))
    (or.inl hres) (or.inl hdead),
  by simp [of_col_colg, smul_val, pequiv.single, pequiv.to_matrix, le_refl q]⟩

/-- A column variable is unbounded below if it is unrestricted and it is in a column where every
  positive entry is in a row owned by an unrestricted variable -/
lemma is_unbounded_below_colg {c : fin n} (hT : (feasible T))
  (hres : (to_partition T).colg c ∉ (restricted T)) (hdead : c ∉ (dead T))
  (h : ∀ i : fin m, (to_partition T).rowg i ∈ (restricted T) → (to_matrix T) i c ≤ 0) :
  (is_unbounded_below T) ((to_partition T).colg c) :=
λ q, ⟨_, is_unbounded_below_colg_aux hT hres hdead h q⟩

/-- A row variable `r` is unbounded above if it is unrestricted and there is a column `s`
  where every restricted row variable has a nonpositive entry in that column, and
  `r` has a negative entry in that column. -/
lemma is_unbounded_above_rowg_of_nonpos {r : fin m} (hT : (feasible T)) (c : fin n)
  (hres : (to_partition T).colg c ∉ (restricted T)) (hdead : c ∉ (dead T))
  (h : ∀ i : fin m, (to_partition T).rowg i ∈ (restricted T) → (to_matrix T) i c ≤ 0)
  (his : (to_matrix T) r c < 0) : is_unbounded_above T ((to_partition T).rowg r) :=
λ q, ⟨(of_col T) (min ((q - (const T) r 0) / (to_matrix T) r c) 0 • (single c 0).to_matrix),
  of_col_single_mem_sol_set hT
    (λ i' hi', mul_nonneg_of_nonpos_of_nonpos (min_le_right _ _) (h _ hi'))
    (or.inl hres) (or.inl hdead),
  begin
    rw [of_col_rowg, add_val, matrix.mul_smul, smul_val, matrix_mul_apply,
      symm_single_apply],
    cases le_total 0 ((q - (const T) r 0) / (to_matrix T) r c) with hq hq,
    { rw [min_eq_right hq],
      rw [le_div_iff_of_neg his, zero_mul, sub_nonpos] at hq,
      simpa },
    { rw [min_eq_left hq, div_mul_cancel _ (ne_of_lt his)],
      simp }
  end⟩

/-- A row variable `r` is unbounded above if there is a column `s`
  where every restricted row variable has a nonpositive entry in that column, and
  `r` has a positive entry in that column. -/
lemma is_unbounded_above_rowg_of_nonneg {r : fin m} (hT : (feasible T)) (c : fin n)
  (hs : ∀ i : fin m, (to_partition T).rowg i ∈ (restricted T) → 0 ≤ (to_matrix T) i c) (hdead : c ∉ (dead T))
  (his : 0 < (to_matrix T) r c) : is_unbounded_above T ((to_partition T).rowg r) :=
λ q, ⟨(of_col T) (max ((q - (const T) r 0) / (to_matrix T) r c) 0 • (single c 0).to_matrix),
  of_col_single_mem_sol_set hT
    (λ i hi, mul_nonneg (le_max_right _ _) (hs i hi))
    (or.inr (le_max_right _ _)) (or.inl hdead),
  begin
    rw [of_col_rowg, add_val, matrix.mul_smul, smul_val, matrix_mul_apply,
      symm_single_apply],
    cases le_total ((q - (const T) r 0) / (to_matrix T) r c) 0 with hq hq,
    { rw [max_eq_right hq],
      rw [div_le_iff his, zero_mul, sub_nonpos] at hq,
      simpa },
    { rw [max_eq_left hq, div_mul_cancel _ (ne_of_gt his)],
      simp }
  end⟩

/-- The sample solution of a feasible tableau maximises the variable in row `r`,
  if every entry in that row is nonpositive and every entry in that row owned by a restricted
  variable is `0`  -/
lemma is_optimal_of_col_zero {obj : fin m} (hf : (feasible T))
  (h : ∀ j, j ∉ (dead T) → (to_matrix T) obj j ≤ 0 ∧
    ((to_partition T).colg j ∉ (restricted T) → (to_matrix T) obj j = 0)) :
  (is_optimal T) ((of_col T) 0) ((to_partition T).rowg obj) :=
⟨of_col_zero_mem_sol_set_iff.2 hf, λ x hx, begin
  rw [of_col_rowg, matrix.mul_zero, zero_add, mem_flat_iff.1 hx.1.1],
  refine add_le_of_nonpos_of_le _ (le_refl _),
  refine sum_nonpos (λ j _, _),
  by_cases hj : ((to_partition T).colg j) ∈ (restricted T),
  { by_cases hdead : j ∈ (dead T),
    { simp [hx.2 _ hdead] },
    { exact mul_nonpos_of_nonpos_of_nonneg (h _ hdead).1 (hx.1.2 _ hj) } },
  { by_cases hdead : j ∈ (dead T),
    { simp [hx.2 _ hdead] },
    { rw [(h _ hdead).2 hj, zero_mul] } }
end⟩

lemma not_optimal_of_unbounded_above {v : fin (m + n)} {x : cvec (m + n)}
  (hu : is_unbounded_above T v) : ¬is_optimal T x v :=
λ hm, let ⟨y, hy⟩ := hu (x v 0 + 1) in
  not_le_of_gt (lt_add_one (x v 0)) (le_trans hy.2 (hm.2 y hy.1))

/-- Expression for the sum of all but one entries in the a row of a tableau. -/
lemma row_sum_erase_eq {x : cvec (m + n)} (hx : x ∈ (flat T)) {r : fin m} {s : fin n} :
  (univ.erase s).sum (λ j : fin n, (to_matrix T) r j * x ((to_partition T).colg j) 0) =
    x ((to_partition T).rowg r) 0 - (const T) r 0 - (to_matrix T) r s * x ((to_partition T).colg s) 0 :=
begin
  rw [mem_flat_iff] at hx,
  conv_rhs { rw [hx r, ← insert_erase (mem_univ s), sum_insert (not_mem_erase _ _)] },
  simp
end

/-- An expression for a column variable in terms of row variables. -/
lemma colg_eq {x : cvec (m + n)} (hx : x ∈ (flat T)) {r : fin m} {s : fin n}
  (hrs : (to_matrix T) r s ≠ 0) : x ((to_partition T).colg s) 0 =
    (x ((to_partition T).rowg r) 0
    -(univ.erase s).sum (λ j : fin n, (to_matrix T) r j * x ((to_partition T).colg j) 0)
        - (const T) r 0) * ((to_matrix T) r s)⁻¹ :=
by simp [row_sum_erase_eq hx, mul_left_comm ((to_matrix T) r s)⁻¹, mul_assoc,
    mul_left_comm ((to_matrix T) r s), mul_inv_cancel hrs]

/-- Another expression for a column variable in terms of row variables. -/
lemma colg_eq' {x : cvec (m + n)} (hx : x ∈ (flat T)) {r : fin m} {s : fin n}
  (hrs : (to_matrix T) r s ≠ 0) : x ((to_partition T).colg s) 0 =
  univ.sum (λ (j : fin n), (if j = s then ((to_matrix T) r s)⁻¹
    else (-((to_matrix T) r j * ((to_matrix T) r s)⁻¹))) *
      x (colg (swap ((to_partition T)) r s) j) 0) -
  ((const T) r 0) * ((to_matrix T) r s)⁻¹ :=
have (univ.erase s).sum
    (λ j : fin n, ite (j = s) ((to_matrix T) r s)⁻¹ (-((to_matrix T) r j * ((to_matrix T) r s)⁻¹)) *
      x (colg (swap ((to_partition T)) r s) j) 0) =
    (univ.erase s).sum (λ j : fin n,
      -(to_matrix T) r j * x ((to_partition T).colg j) 0 * ((to_matrix T) r s)⁻¹),
  from finset.sum_congr rfl $ λ j hj,
    by simp [if_neg (mem_erase.1 hj).1, colg_swap_of_ne _ (mem_erase.1 hj).1,
      mul_comm, mul_assoc, mul_left_comm],
by rw [← finset.insert_erase (mem_univ s), finset.sum_insert (not_mem_erase _ _),
    if_pos rfl, colg_swap, colg_eq hx hrs, this, ← finset.sum_mul];
  simp [_root_.add_mul, mul_comm, _root_.mul_add]

-- /-- Pivoting twice in the same place does nothing -/
-- @[simp] lemma pivot_pivot {r : fin m} {s : fin n} (hrs : (to_matrix T) r s ≠ 0) :
--   pivot ((pivot T) r s) r s = T :=
-- begin
--   cases T,
--   simp [pivot, function.funext_iff],
--   split; intros; split_ifs;
--   simp [*, mul_assoc, mul_left_comm (T_to_matrix r s), mul_left_comm (T_to_matrix r s)⁻¹,
--     mul_comm (T_to_matrix r s), inv_mul_cancel hrs]
-- end

variable (T)

@[simp] lemma pivot_pivot_element (r : fin m) (s : fin n) :
  to_matrix ((pivot T) r s) r s = ((to_matrix T) r s)⁻¹ :=
by simp [to_matrix, to_tableau_pivot, tableau.pivot_pivot_element]

@[simp] lemma pivot_pivot_row {r : fin m} {j s : fin n} (h : j ≠ s) :
  to_matrix ((pivot T) r s) r j = -(to_matrix T) r j / (to_matrix T) r s :=
by simp [to_matrix, to_tableau_pivot, tableau.pivot_pivot_row _ h]

@[simp] lemma pivot_pivot_column {i r : fin m} {s : fin n} (h : i ≠ r) :
  to_matrix ((pivot T) r s) i s = (to_matrix T) i s / (to_matrix T) r s :=
by simp [to_matrix, to_tableau_pivot, tableau.pivot_pivot_column _ h]

@[simp] lemma pivot_of_ne_of_ne {i r : fin m} {j s : fin n} (hir : i ≠ r)
  (hjs : j ≠ s) : to_matrix ((pivot T) r s) i j =
  (to_matrix T) i j - (to_matrix T) i s * (to_matrix T) r j / (to_matrix T) r s :=
by simp [to_matrix, to_tableau_pivot, tableau.pivot_of_ne_of_ne _ hir hjs]

@[simp] lemma const_pivot_row {r : fin m} {s : fin n} : const ((pivot T) r s) r 0 =
  -(const T) r 0 / (to_matrix T) r s :=
by simp [const, to_matrix, to_tableau_pivot, tableau.const_pivot_row]

@[simp] lemma const_pivot_of_ne {i r : fin m} {s : fin n} (hir : i ≠ r) : const ((pivot T) r s) i 0
  = (const T) i 0 - (to_matrix T) i s * (const T) r 0 / (to_matrix T) r s :=
by simp [const, to_matrix, to_tableau_pivot, tableau.const_pivot_of_ne _ hir]

@[simp] lemma restricted_pivot (r s) : restricted ((pivot T) r s) = (restricted T) :=
by simp [restricted, to_tableau_pivot]

@[simp] lemma to_partition_pivot (r s) : to_partition ((pivot T) r s) = (to_partition T).swap r s :=
by simp [to_partition, to_tableau_pivot]

@[simp] lemma dead_pivot (r c) : dead ((pivot T) r c) = (dead T) :=
by simp [dead, to_tableau_pivot]

variable {T}

@[simp] lemma flat_pivot {r : fin m} {s : fin n} (hrs : (to_matrix T) r s ≠ 0) :
  flat ((pivot T) r s) = (flat T) :=
by simp only [flat, to_tableau_pivot, to_matrix, to_partition, const];
  exact tableau.flat_pivot hrs

@[simp] lemma res_set_pivot {r : fin m} {s : fin n} (hrs : (to_matrix T) r s ≠ 0) :
  res_set ((pivot T) r s) = (res_set T) :=
by simp only [res_set, flat, to_tableau_pivot, to_matrix, to_partition, const, restricted];
  exact tableau.res_set_pivot hrs

@[simp] lemma dead_set_pivot {r : fin m} {c : fin n} (hrs : (to_matrix T) r c ≠ 0)
  (hdead : c ∉ (dead T)) : dead_set ((pivot T) r c) = (dead_set T) :=
by simp only [dead_set, flat, to_tableau_pivot, to_matrix, to_partition, const, dead] at *;
  exact tableau.dead_set_pivot hrs hdead

@[simp] lemma sol_set_pivot {r : fin m} {c : fin n} (hrs : (to_matrix T) r c ≠ 0)
  (hdead : c ∉ (dead T)) : sol_set ((pivot T) r c) = (sol_set T) :=
by simp [sol_set_eq_dead_set_inter, dead_set_pivot hrs hdead, flat_pivot hrs]

-- lemma mul_single_ext {R : Type*} {m n : ℕ} [semiring R]
--   {A B : matrix (fin m) (fin n) R} (h : ∀ j : fin n, A ⬝ (single j (0 : fin 1)).to_matrix = B ⬝
--     (single j (0 : fin 1)).to_matrix) : A = B :=
-- by ext i j; simpa [matrix_mul_apply] using congr_fun (congr_fun (h j) i) 0

-- lemma single_mul_ext {R : Type*} {m n : ℕ} [semiring R]
--   {A B : matrix (fin m) (fin n) R} (h : ∀ i, (single (0 : fin 1) i).to_matrix ⬝ A =
--     (single (0 : fin 1) i).to_matrix ⬝ B) : A = B :=
-- by ext i j; simpa [mul_matrix_apply] using congr_fun (congr_fun (h i) 0) j

-- lemma ext {T₁ T₂ : X m n} (hflat : T₁.flat = T₂.flat)
--   (hpartition : T₁.to_partition = T₂.to_partition)
--   (hdead : T₁.dead = T₂.dead)
--   (hres : T₁.restricted = T₂.restricted) : T₁ = T₂ :=
-- have hconst : T₁.const = T₂.const,
--   by rw [set.ext_iff] at hflat; simpa [of_col, flat, hpartition, matrix.mul_assoc,
--     mul_right_eq_of_mul_eq (rowp_transpose_mul_rowp _),
--     mul_right_eq_of_mul_eq (colp_transpose_mul_rowp _)] using
--   (hflat (T₁.of_col 0)).1 (of_col_mem_flat _ _),
-- have hmatrix : T₁.to_matrix = T₂.to_matrix,
--   from mul_single_ext $ λ j, begin
--     rw [set.ext_iff] at hflat,
--     have := (hflat (T₁.of_col (single j 0).to_matrix)).1 (of_col_mem_flat _ _),
--     simpa [of_col, hconst, hpartition, flat, matrix.mul_add, matrix.mul_assoc,
--         mul_right_eq_of_mul_eq (rowp_transpose_mul_colp _),
--         mul_right_eq_of_mul_eq (rowp_transpose_mul_rowp _),
--         mul_right_eq_of_mul_eq (colp_transpose_mul_colp _),
--         mul_right_eq_of_mul_eq (colp_transpose_mul_rowp _)] using
--       (hflat (T₁.of_col (single j 0).to_matrix)).1 (of_col_mem_flat _ _)
--   end,
-- by cases T₁; cases T₂; simp * at *

end predicate_lemmas

/-- Conditions for unboundedness based on reading the tableau. The conditions are equivalent to the
  simplex pivot rule failing to find a pivot row. -/
lemma unbounded_of_tableau {T : X m n} {obj : fin m} {c : fin n} (hT : (feasible T))
  (hdead : c ∉ (dead T))
  (hrow : ∀ r, obj ≠ r → (to_partition T).rowg r ∈ (restricted T) →
    0 ≤ (to_matrix T) obj c / (to_matrix T) r c)
  (hc : ((to_matrix T) obj c ≠ 0 ∧ (to_partition T).colg c ∉ (restricted T))
    ∨ (0 < (to_matrix T) obj c ∧ (to_partition T).colg c ∈ (restricted T))) :
  (is_unbounded_above T) ((to_partition T).rowg obj) :=
have hToc : (to_matrix T) obj c ≠ 0, from λ h, by simpa [h, lt_irrefl] using hc,
(lt_or_gt_of_ne hToc).elim
  (λ hToc : (to_matrix T) obj c < 0, is_unbounded_above_rowg_of_nonpos hT c
    (hc.elim and.right (λ h, (not_lt_of_gt hToc h.1).elim)) hdead
    (λ i hi, classical.by_cases
      (λ hoi : obj = i, le_of_lt (hoi ▸ hToc))
      (λ hoi : obj ≠ i, inv_nonpos.1 $ nonpos_of_mul_nonneg_right (hrow _ hoi hi) hToc))
    hToc)
  (λ hToc : 0 < (to_matrix T) obj c, is_unbounded_above_rowg_of_nonneg hT c
    (λ i hi, classical.by_cases
      (λ hoi : obj = i, le_of_lt (hoi ▸ hToc))
      (λ hoi : obj ≠ i, inv_nonneg.1 $ nonneg_of_mul_nonneg_left (hrow _ hoi hi) hToc))
    hdead hToc)

/-- Conditions for the tableau being feasible, that must be satisified by a simplex pivot rule -/
lemma feasible_pivot {T : X m n} (hT : (feasible T)) {r c}
  (hres : (to_partition T).rowg r ∈ (restricted T))
  (hpos : (to_partition T).colg c ∈ (restricted T) → (to_matrix T) r c < 0)
  (hrmin : ∀ (i : fin m), (to_partition T).rowg i ∈ (restricted T) →
    0 < (to_matrix T) i c / (to_matrix T) r c →
    abs ((const T) r 0 / (to_matrix T) r c) ≤ abs ((const T) i 0 / (to_matrix T) i c)) :
  feasible ((pivot T) r c) :=
by simp only [to_matrix, const, to_partition, restricted, feasible, to_tableau_pivot] at *;
  exact tableau.feasible_pivot hT hres hpos hrmin

lemma feasible_simplex_pivot {T : X m n} {obj : fin m} (hT : (feasible T)) {r c}
  (hres : (to_partition T).rowg r ∈ (restricted T))
  (hrneg : (to_matrix T) obj c / (to_matrix T) r c < 0)
  (hrmin : ∀ (r' : fin m), obj ≠ r' → (to_partition T).rowg r' ∈ (restricted T) →
          (to_matrix T) obj c / (to_matrix T) r' c < 0 →
          abs ((const T) r 0 / (to_matrix T) r c) ≤ abs ((const T) r' 0 / (to_matrix T) r' c))
  (hc : (to_partition T).colg c ∈ (restricted T) → 0 < (to_matrix T) obj c) :
  feasible ((pivot T) r c) :=
feasible_pivot hT hres (λ hcres, inv_neg'.1 (neg_of_mul_neg_left hrneg (le_of_lt (hc hcres))))
  (λ i hires hir,
    have hobji : obj ≠ i,
      from λ hobji, not_lt_of_gt hir (hobji ▸ hrneg),
    (hrmin _ hobji hires $
      have hTrc0 : (to_matrix T) r c ≠ 0, from λ _, by simp [*, lt_irrefl] at *,
      suffices ((to_matrix T) obj c / (to_matrix T) r c) / ((to_matrix T) i c / (to_matrix T) r c) < 0,
        by rwa [div_div_div_cancel_right _ _ hTrc0] at this,
      div_neg_of_neg_of_pos hrneg hir))

-- /-- Used in sign_of_max -/
-- lemma feasible_pivot_obj_of_nonpos {T : X m n} {obj : fin m} (hT : (feasible T)) {c}
--   (hc : (to_partition T).colg c ∈ (restricted T) → 0 < (to_matrix T) obj c)
--   (hr : ∀ r, obj ≠ r → (to_partition T).rowg r ∈ (restricted T) →
--     0 ≤ (to_matrix T) obj c / (to_matrix T) r c)
--   (hobj : (const T) obj 0 ≤ 0) : feasible ((pivot T) obj c) :=
-- λ i hi,
-- if hiobj : i = obj
-- then by rw [hiobj, const_pivot_row, neg_div, neg_nonneg];
--   exact mul_nonpos_of_nonpos_of_nonneg hobj (le_of_lt $ by simp [*, inv_pos'] at *)
-- else begin
--   rw [const_pivot_of_ne _ hiobj],
--   rw [to_partition_pivot, rowg_swap_of_ne _ hiobj, restricted_pivot] at hi,
--   refine add_nonneg (hT _ hi) (neg_nonneg.2 _),
--   rw [div_eq_mul_inv, mul_right_comm],
--   exact mul_nonpos_of_nonneg_of_nonpos
--     (inv_nonneg.1 (by simpa [mul_inv'] using hr _ (ne.symm hiobj) hi))
--     hobj
-- end

-- lemma simplex_const_obj_le {T : X m n} {obj : fin m} (hT : (feasible T)) {r c}
--   (hres : (to_partition T).rowg r ∈ (restricted T))
--   (hrneg : (to_matrix T) obj c / (to_matrix T) r c < 0) :
--   (const T) obj 0 ≤ ((pivot T) r c).const obj 0 :=
-- have obj ≠ r, from λ hor, begin
--   subst hor,
--   by_cases h0 : (to_matrix T) obj c = 0,
--   { simp [lt_irrefl, *] at * },
--   { simp [div_self h0, not_lt_of_le zero_le_one, *] at * }
-- end,
-- by simp only [le_add_iff_nonneg_right, sub_eq_add_neg, neg_nonneg, mul_assoc, div_eq_mul_inv,
--     mul_left_comm ((to_matrix T) obj c), const_pivot_of_ne _ this];
--   exact mul_nonpos_of_nonneg_of_nonpos (hT _ hres) (le_of_lt hrneg)

-- lemma const_eq_zero_of_const_obj_eq {T : X m n} {obj : fin m} (hT : (feasible T)) {r c}
--   (hc : (to_matrix T) obj c ≠ 0) (hrc : (to_matrix T) r c ≠ 0) (hobjr : obj ≠ r)
--   (hobj : ((pivot T) r c).const obj 0 = (const T) obj 0) :
--   (const T) r 0 = 0 :=
-- by rw [const_pivot_of_ne _ hobjr, sub_eq_iff_eq_add, ← sub_eq_iff_eq_add', sub_self,
--     eq_comm, div_eq_mul_inv, mul_eq_zero, mul_eq_zero, inv_eq_zero] at hobj; tauto

end is_tableau
