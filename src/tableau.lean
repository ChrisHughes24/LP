import data.matrix.pequiv data.rat.basic tactic.fin_cases data.list.min_max partition

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

/-- The tableau consists of a matrix and a kant `const` column.
  `to_partition` stores the indices of the current row and column variables.
  `restricted` is the set of variables that are restricted to be nonnegative  -/
structure tableau (m n : ℕ) extends partition m n :=
(to_matrix  : matrix (fin m) (fin n) ℚ)
(const      : cvec m)
(restricted : finset (fin (m + n)))
(dead       : finset (fin n))

namespace tableau
open partition

section predicates
variable (T : tableau m n)

/-- The affine subspace represented by the tableau ignoring nonnegativity restrictiions -/
def flat : set (cvec (m + n)) :=
{ x | T.to_partition.rowp.to_matrixᵀ ⬝ x = T.to_matrix ⬝ T.to_partition.colp.to_matrixᵀ ⬝ x + T.const }

/-- The res_set is the subset of ℚ^(m+n) that satisifies the nonnegativity constraints of
  the tableau, and the affine conditions -/
def res_set : set (cvec (m + n)) := flat T ∩ { x | ∀ i, i ∈ T.restricted → 0 ≤ x i 0 }

/-- The dead_set is the subset of ℚ^(m+n) such that all dead variables are zero, and satisfies
  the affine conditions -/
def dead_set : set (cvec (m + n)) :=
flat T ∩ { x | ∀ j, j ∈ T.dead → x (T.to_partition.colg j) 0 = 0 }

/-- The `sol_set` is the set of vector that satisfy the affine constraints the dead variable
  constraints, and the nonnegativity constraints. -/
def sol_set : set (cvec (m + n)) :=
res_set T ∩ { x | ∀ j, j ∈ T.dead → x (T.to_partition.colg j) 0 = 0 }

lemma sol_set_eq_res_set_inter :
  T.sol_set = res_set T ∩ { x | ∀ j, j ∈ T.dead → x (T.to_partition.colg j) 0 = 0 } := rfl

lemma sol_set_eq_dead_set_inter :
   T.sol_set = dead_set T ∩ { x | ∀ i, i ∈ T.restricted → 0 ≤ x i 0 } :=
set.inter_right_comm _ _ _

lemma sol_set_eq_res_set_inter_dead_set : T.sol_set = T.res_set ∩ T.dead_set :=
by simp [sol_set, res_set, dead_set, set.ext_iff]; tauto

/-- Predicate for a variable being unbounded above in the `res_set` -/
def is_unbounded_above (i : fin (m + n)) : Prop :=
∀ q : ℚ, ∃ x : cvec (m + n), x ∈ sol_set T ∧ q ≤ x i 0

/-- Predicate for a variable being unbounded below in the `res_set` -/
def is_unbounded_below (i : fin (m + n)) : Prop :=
∀ q : ℚ, ∃ x : cvec (m + n), x ∈ sol_set T ∧ x i 0 ≤ q

def is_optimal (x : cvec (m + n)) (i : fin (m + n)) : Prop :=
x ∈ T.sol_set ∧ ∀ y : cvec (m + n), y ∈ sol_set T → y i 0 ≤ x i 0

/-- Is this equivalent to `∀ (x : cvec (m + n)), x ∈ res_set T → x i 0 = x j 0`? No -/
def equal_in_flat (i j : fin (m + n)) : Prop :=
∀ (x : cvec (m + n)), x ∈ flat T → x i 0 = x j 0

/-- Returns an element of the `flat` after assigning values to the column variables -/
def of_col (T : tableau m n) (x : cvec n) : cvec (m + n) :=
T.to_partition.colp.to_matrix ⬝ x + T.to_partition.rowp.to_matrix ⬝ (T.to_matrix ⬝ x + T.const)

/-- A `tableau` is feasible if its `const` column is nonnegative in restricted rows -/
def feasible : Prop :=
∀ i, T.to_partition.rowg i ∈ T.restricted → 0 ≤ T.const i 0

instance : decidable_pred (@feasible m n) := λ _, by dunfold feasible; apply_instance

/-- Given a row index `r` and a column index `s` it returns a tableau with `r` and `s` switched,
  but with the same `res_set` -/
def pivot (i : fin m) (j : fin n) : tableau m n :=
let p := (T.to_matrix i j)⁻¹ in
{ to_matrix := λ i' j',
    if i' = i
      then if j' = j
        then p
        else -T.to_matrix i' j' * p
      else if j' = j
        then T.to_matrix i' j * p
        else T.to_matrix i' j' - T.to_matrix i' j * T.to_matrix i j' * p,
  to_partition := T.to_partition.swap i j,
  const := λ i' k,
    if i' = i
      then -T.const i k * p
      else T.const i' k - T.to_matrix i' j * T.const i k * p,
  restricted := T.restricted,
  dead := T.dead }

def restrict (T : tableau m n) (v : fin (m + n)) : tableau m n :=
{ restricted := insert v T.restricted,
  ..T }

-- def kill_col (T : tableau m n) (j : fin n) : tableau m n :=
-- { dead := insert c T.dead,
--   ..T }

end predicates

section predicate_lemmas
variable {T : tableau m n}

@[simp] lemma eta : tableau.mk T.to_partition T.to_matrix T.const T.restricted T.dead = T :=
by cases T; refl

lemma mem_flat_iff {x : cvec (m + n)} : x ∈ T.flat ↔
  ∀ i, x (T.to_partition.rowg i) 0 = univ.sum
    (λ j : fin n, T.to_matrix i j * x (T.to_partition.colg j) 0) +
  T.const i 0 :=
have hx : x ∈ T.flat ↔ ∀ i, (T.to_partition.rowp.to_matrixᵀ ⬝ x) i 0 =
    (T.to_matrix ⬝ T.to_partition.colp.to_matrixᵀ ⬝ x + T.const) i 0,
  by rw [flat, set.mem_set_of_eq, matrix.ext_iff.symm, forall_swap,
      unique.forall_iff];
    refl,
begin
  rw hx,
  refine forall_congr (λ i, _),
  rw [← to_matrix_symm, mul_matrix_apply, add_val, rowp_symm_eq_some_rowg,
    matrix.mul_assoc, matrix.mul],
  conv in (T.to_matrix _ _ * (T.to_partition.colp.to_matrixᵀ ⬝ x) _ _)
  { rw [← to_matrix_symm, mul_matrix_apply, colp_symm_eq_some_colg] }
end

variable (T)

@[simp] lemma colp_mul_of_col (x : cvec n) :
  T.to_partition.colp.to_matrixᵀ ⬝ of_col T x = x :=
by simp [matrix.mul_assoc, matrix.mul_add, of_col, flat,
    mul_right_eq_of_mul_eq (rowp_transpose_mul_colp _),
    mul_right_eq_of_mul_eq (rowp_transpose_mul_rowp _),
    mul_right_eq_of_mul_eq (colp_transpose_mul_colp _),
    mul_right_eq_of_mul_eq (colp_transpose_mul_rowp _)]

@[simp] lemma rowp_mul_of_col (x : cvec n) :
  T.to_partition.rowp.to_matrixᵀ ⬝ of_col T x = T.to_matrix ⬝ x + T.const :=
by simp [matrix.mul_assoc, matrix.mul_add, of_col, flat,
    mul_right_eq_of_mul_eq (rowp_transpose_mul_colp _),
    mul_right_eq_of_mul_eq (rowp_transpose_mul_rowp _),
    mul_right_eq_of_mul_eq (colp_transpose_mul_colp _),
    mul_right_eq_of_mul_eq (colp_transpose_mul_rowp _)]

lemma of_col_mem_flat (x : cvec n) : T.of_col x ∈ T.flat :=
by simp [matrix.mul_assoc, matrix.mul_add, flat]

@[simp] lemma of_col_colg (x : cvec n) (j : fin n) :
  of_col T x (T.to_partition.colg j) = x j :=
funext $ λ v,
  calc of_col T x (T.to_partition.colg j) v =
      (T.to_partition.colp.to_matrixᵀ ⬝ of_col T x) j v :
    by rw [← to_matrix_symm, mul_matrix_apply, colp_symm_eq_some_colg]
  ... = x j v : by rw [colp_mul_of_col]

lemma of_col_rowg (c : cvec n) (i : fin m) :
  of_col T c (T.to_partition.rowg i) = (T.to_matrix ⬝ c + T.const) i :=
funext $ λ v,
  calc of_col T c (T.to_partition.rowg i) v =
      (T.to_partition.rowp.to_matrixᵀ ⬝ of_col T c) i v :
     by rw [← to_matrix_symm, mul_matrix_apply, rowp_symm_eq_some_rowg]
  ... = (T.to_matrix ⬝ c + T.const) i v : by rw [rowp_mul_of_col]

variable {T}

lemma of_col_single_rowg {q : ℚ} {i j} {k} :
  T.of_col (q • (single j 0).to_matrix) (T.to_partition.rowg i) k =
    q * T.to_matrix i j + T.const i k:=
begin
  fin_cases k,
  erw [of_col_rowg, matrix.mul_smul, matrix.add_val, matrix.smul_val,
    matrix_mul_apply, pequiv.symm_single_apply]
end

/-- Condition for the solution given by setting column index `j` to `q` and all other columns to
  zero being in the `res_set` -/
lemma of_col_single_mem_res_set {q : ℚ} {j : fin n} (hT : T.feasible)
  (hi : ∀ i, T.to_partition.rowg i ∈ T.restricted → 0 ≤ q * T.to_matrix i j)
  (hj : T.to_partition.colg j ∉ T.restricted ∨ 0 ≤ q) :
  T.of_col (q • (single j 0).to_matrix) ∈ T.res_set :=
⟨of_col_mem_flat _ _,
  λ v, (T.to_partition.eq_rowg_or_colg v).elim
    begin
      rintros ⟨i', hi'⟩ hres,
      subst hi',
      rw [of_col_single_rowg],
      exact add_nonneg (hi _ hres) (hT _ hres)
    end
    begin
      rintros ⟨j', hj'⟩ hres,
      subst hj',
      simp [of_col_colg, smul_val, pequiv.single, pequiv.to_matrix],
      by_cases hjc : j' = j; simp [*, le_refl] at *
    end⟩

lemma of_col_single_mem_sol_set {q : ℚ} {j : fin n} (hT : T.feasible)
  (hi : ∀ i, T.to_partition.rowg i ∈ T.restricted → 0 ≤ q * T.to_matrix i j)
  (hj : T.to_partition.colg j ∉ T.restricted ∨ 0 ≤ q) (hdead : j ∉ T.dead ∨ q = 0):
  T.of_col (q • (single j 0).to_matrix) ∈ T.sol_set :=
⟨of_col_single_mem_res_set hT hi hj,
  λ j' hj', classical.by_cases
    (λ hjj' : j' = j, by subst hjj'; simp * at *)
    (λ hjj' : j' ≠ j, by simp [smul_val, pequiv.single, pequiv.to_matrix, hjj'])⟩

@[simp] lemma of_col_zero_mem_res_set_iff : T.of_col 0 ∈ T.res_set ↔ T.feasible :=
suffices (∀ v : fin (m + n), v ∈ T.restricted → (0 : ℚ) ≤ T.of_col 0 v 0) ↔
    (∀ i : fin m, T.to_partition.rowg i ∈ T.restricted → 0 ≤ T.const i 0),
  by simpa [res_set, feasible, of_col_mem_flat],
⟨λ h i hi, by simpa [of_col_rowg] using h _ hi,
  λ h v hv, (T.to_partition.eq_rowg_or_colg v).elim
    (by rintros ⟨i, hi⟩; subst hi; simp [of_col_rowg]; tauto)
    (by rintros ⟨j, hj⟩; subst hj; simp)⟩

@[simp] lemma of_col_zero_mem_sol_set_iff : T.of_col 0 ∈ T.sol_set ↔ T.feasible :=
by simp [sol_set,  of_col_zero_mem_res_set_iff]

@[simp] lemma to_matrix_restrict (v : fin (m + n)) : (T.restrict v).to_matrix = T.to_matrix := rfl

@[simp] lemma const_restrict (v : fin (m + n)) : (T.restrict v).const = T.const := rfl

@[simp] lemma to_partition_restrict (v : fin (m + n)) :
  (T.restrict v).to_partition = T.to_partition := rfl

@[simp] lemma dead_restrict (v : fin (m + n)) : (T.restrict v).dead = T.dead := rfl

@[simp] lemma restricted_restrict (v : fin (m + n)) :
  (T.restrict v).restricted = insert v T.restricted := rfl

@[simp] lemma flat_restrict (v : fin (m + n)) : (T.restrict v).flat = T.flat := by simp [flat]

@[simp] lemma dead_set_restrict (v : fin (m + n)) : (T.restrict v).dead_set = T.dead_set :=
by simp [dead_set]

lemma res_set_restrict (v : fin (m + n)) : (T.restrict v).res_set =
  T.res_set ∩ {x | 0 ≤ x v 0} :=
begin
  simp only [res_set, flat_restrict, set.inter_assoc],
  ext x,
  exact ⟨λ h, ⟨h.1, λ i hi, h.2 _ $ by simp [hi], h.2 _ $ by simp⟩,
    λ h, ⟨h.1, λ i hi, (mem_insert.1 hi).elim (λ hv, hv.symm ▸ h.2.2) $ h.2.1 _⟩⟩
end

lemma sol_set_restrict (v : fin (m + n)) : (T.restrict v).sol_set =
  T.sol_set ∩ {x | 0 ≤ x v 0} :=
by simp [sol_set_eq_res_set_inter_dead_set, res_set_restrict, set.inter_comm, set.inter_assoc,
  set.inter_left_comm]

lemma feasible_restrict {v : fin (m + n)} (hfT : T.feasible)
  (h : (∃ c, v = T.to_partition.colg c) ∨ ∃ i, v = T.to_partition.rowg i ∧ 0 ≤ T.const i 0) :
  (T.restrict v).feasible :=
h.elim
  (λ ⟨c, hc⟩, hc.symm ▸ λ i hi, hfT _ $ by simpa using hi)
  (λ ⟨i, hiv, hi⟩, hiv.symm ▸ λ i' hi', (mem_insert.1 hi').elim
    (λ h, by simp [T.to_partition.injective_rowg.eq_iff, *] at *)
    (λ hres, hfT _ $ by simpa using hres))

lemma is_unbounded_above_colg_aux {j : fin n} (hT : T.feasible) (hdead : j ∉ T.dead)
  (h : ∀ i : fin m, T.to_partition.rowg i ∈ T.restricted → 0 ≤ T.to_matrix i j) (q : ℚ) :
  of_col T (max q 0 • (single j 0).to_matrix) ∈ sol_set T ∧
    q ≤ of_col T (max q 0 • (single j 0).to_matrix) (T.to_partition.colg j) 0 :=
⟨of_col_single_mem_sol_set hT (λ i hi, mul_nonneg (le_max_right _ _) (h _ hi))
    (or.inr (le_max_right _ _)) (or.inl hdead),
  by simp [of_col_colg, smul_val, pequiv.single, pequiv.to_matrix, le_refl q]⟩

/-- A column variable is unbounded above if it is in a column where every negative entry is
  in a row owned by an unrestricted variable -/
lemma is_unbounded_above_colg {j : fin n} (hT : T.feasible) (hdead : j ∉ T.dead)
  (h : ∀ i : fin m, T.to_partition.rowg i ∈ T.restricted → 0 ≤ T.to_matrix i j) :
  T.is_unbounded_above (T.to_partition.colg j) :=
λ q, ⟨_, is_unbounded_above_colg_aux hT hdead h q⟩

lemma is_unbounded_below_colg_aux {j : fin n} (hT : T.feasible)
  (hres : T.to_partition.colg j ∉ T.restricted) (hdead : j ∉ T.dead)
  (h : ∀ i : fin m, T.to_partition.rowg i ∈ T.restricted → T.to_matrix i j ≤ 0) (q : ℚ) :
  of_col T (min q 0 • (single j 0).to_matrix) ∈ sol_set T ∧
    of_col T (min q 0 • (single j 0).to_matrix) (T.to_partition.colg j) 0 ≤ q :=
⟨of_col_single_mem_sol_set hT
    (λ i hi, mul_nonneg_of_nonpos_of_nonpos (min_le_right _ _) (h _ hi))
    (or.inl hres) (or.inl hdead),
  by simp [of_col_colg, smul_val, pequiv.single, pequiv.to_matrix, le_refl q]⟩

/-- A column variable is unbounded below if it is unrestricted and it is in a column where every
  positive entry is in a row owned by an unrestricted variable -/
lemma is_unbounded_below_colg {j : fin n} (hT : T.feasible)
  (hres : T.to_partition.colg j ∉ T.restricted) (hdead : j ∉ T.dead)
  (h : ∀ i : fin m, T.to_partition.rowg i ∈ T.restricted → T.to_matrix i j ≤ 0) :
  T.is_unbounded_below (T.to_partition.colg j) :=
λ q, ⟨_, is_unbounded_below_colg_aux hT hres hdead h q⟩

/-- A row variable `r` is unbounded above if it is unrestricted and there is a column `s`
  where every restricted row variable has a nonpositive entry in that column, and
  `r` has a negative entry in that column. -/
lemma is_unbounded_above_rowg_of_nonpos {i : fin m} (hT : T.feasible) (j : fin n)
  (hres : T.to_partition.colg j ∉ T.restricted) (hdead : j ∉ T.dead)
  (h : ∀ i : fin m, T.to_partition.rowg i ∈ T.restricted → T.to_matrix i j ≤ 0)
  (his : T.to_matrix i j < 0) : is_unbounded_above T (T.to_partition.rowg i) :=
λ q, ⟨T.of_col (min ((q - T.const i 0) / T.to_matrix i j) 0 • (single j 0).to_matrix),
  of_col_single_mem_sol_set hT
    (λ i' hi', mul_nonneg_of_nonpos_of_nonpos (min_le_right _ _) (h _ hi'))
    (or.inl hres) (or.inl hdead),
  begin
    rw [of_col_rowg, add_val, matrix.mul_smul, smul_val, matrix_mul_apply,
      symm_single_apply],
    cases le_total 0 ((q - T.const i 0) / T.to_matrix i j) with hq hq,
    { rw [min_eq_right hq],
      rw [le_div_iff_of_neg his, zero_mul, sub_nonpos] at hq,
      simpa },
    { rw [min_eq_left hq, div_mul_cancel _ (ne_of_lt his)],
      simp }
  end⟩

/-- A row variable `i` is unbounded above if there is a column `s`
  where every restricted row variable has a nonpositive entry in that column, and
  `i` has a positive entry in that column. -/
lemma is_unbounded_above_rowg_of_nonneg {i : fin m} (hT : T.feasible) (j : fin n)
  (hs : ∀ i' : fin m, T.to_partition.rowg i' ∈ T.restricted → 0 ≤ T.to_matrix i' j) (hdead : j ∉ T.dead)
  (his : 0 < T.to_matrix i j) : is_unbounded_above T (T.to_partition.rowg i) :=
λ q, ⟨T.of_col (max ((q - T.const i 0) / T.to_matrix i j) 0 • (single j 0).to_matrix),
  of_col_single_mem_sol_set hT
    (λ i hi, mul_nonneg (le_max_right _ _) (hs i hi))
    (or.inr (le_max_right _ _)) (or.inl hdead),
  begin
    rw [of_col_rowg, add_val, matrix.mul_smul, smul_val, matrix_mul_apply,
      symm_single_apply],
    cases le_total ((q - T.const i 0) / T.to_matrix i j) 0 with hq hq,
    { rw [max_eq_right hq],
      rw [div_le_iff his, zero_mul, sub_nonpos] at hq,
      simpa },
    { rw [max_eq_left hq, div_mul_cancel _ (ne_of_gt his)],
      simp }
  end⟩

/-- The sample solution of a feasible tableau maximises the variable in row `r`,
  if every entry in that row is nonpositive and every entry in that row owned by a restricted
  variable is `0`  -/
lemma is_optimal_of_col_zero {obj : fin m} (hf : T.feasible)
  (h : ∀ j, j ∉ T.dead → T.to_matrix obj j ≤ 0 ∧
    (T.to_partition.colg j ∉ T.restricted → T.to_matrix obj j = 0)) :
  T.is_optimal (T.of_col 0) (T.to_partition.rowg obj) :=
⟨of_col_zero_mem_sol_set_iff.2 hf, λ x hx, begin
  rw [of_col_rowg, matrix.mul_zero, zero_add, mem_flat_iff.1 hx.1.1],
  refine add_le_of_nonpos_of_le _ (le_refl _),
  refine sum_nonpos (λ j _, _),
  by_cases hj : (T.to_partition.colg j) ∈ T.restricted,
  { by_cases hdead : j ∈ T.dead,
    { simp [hx.2 _ hdead] },
    { exact mul_nonpos_of_nonpos_of_nonneg (h _ hdead).1 (hx.1.2 _ hj) } },
  { by_cases hdead : j ∈ T.dead,
    { simp [hx.2 _ hdead] },
    { rw [(h _ hdead).2 hj, zero_mul] } }
end⟩

lemma not_optimal_of_unbounded_above {v : fin (m + n)} {x : cvec (m + n)}
  (hu : is_unbounded_above T v) : ¬is_optimal T x v :=
λ hm, let ⟨y, hy⟩ := hu (x v 0 + 1) in
  not_le_of_gt (lt_add_one (x v 0)) (le_trans hy.2 (hm.2 y hy.1))

/-- Expression for the sum of all but one entries in the a row of a tableau. -/
lemma row_sum_erase_eq {x : cvec (m + n)} (hx : x ∈ T.flat) {i : fin m} {s : fin n} :
  (univ.erase s).sum (λ j : fin n, T.to_matrix i j * x (T.to_partition.colg j) 0) =
    x (T.to_partition.rowg i) 0 - T.const i 0 - T.to_matrix i s * x (T.to_partition.colg s) 0 :=
begin
  rw [mem_flat_iff] at hx,
  conv_rhs { rw [hx i, ← insert_erase (mem_univ s), sum_insert (not_mem_erase _ _)] },
  simp
end

/-- An expression for a column variable in terms of row variables. -/
lemma colg_eq {x : cvec (m + n)} (hx : x ∈ T.flat) {i : fin m} {s : fin n}
  (his : T.to_matrix i s ≠ 0) : x (T.to_partition.colg s) 0 =
    (x (T.to_partition.rowg i) 0
    -(univ.erase s).sum (λ j : fin n, T.to_matrix i j * x (T.to_partition.colg j) 0)
        - T.const i 0) * (T.to_matrix i s)⁻¹ :=
by simp [row_sum_erase_eq hx, mul_left_comm (T.to_matrix i s)⁻¹, mul_assoc,
    mul_left_comm (T.to_matrix i s), mul_inv_cancel his]

/-- Another expression for a column variable in terms of row variables. -/
lemma colg_eq' {x : cvec (m + n)} (hx : x ∈ T.flat) {i : fin m} {s : fin n}
  (his : T.to_matrix i s ≠ 0) : x (T.to_partition.colg s) 0 =
  univ.sum (λ (j : fin n), (if j = s then (T.to_matrix i s)⁻¹
    else (-(T.to_matrix i j * (T.to_matrix i s)⁻¹))) *
      x (colg (swap (T.to_partition) i s) j) 0) -
  (T.const i 0) * (T.to_matrix i s)⁻¹ :=
have (univ.erase s).sum
    (λ j : fin n, ite (j = s) (T.to_matrix i s)⁻¹ (-(T.to_matrix i j * (T.to_matrix i s)⁻¹)) *
      x (colg (swap (T.to_partition) i s) j) 0) =
    (univ.erase s).sum (λ j : fin n,
      -T.to_matrix i j * x (T.to_partition.colg j) 0 * (T.to_matrix i s)⁻¹),
  from finset.sum_congr rfl $ λ j hj,
    by simp [if_neg (mem_erase.1 hj).1, colg_swap_of_ne _ (mem_erase.1 hj).1,
      mul_comm, mul_assoc, mul_left_comm],
by rw [← finset.insert_erase (mem_univ s), finset.sum_insert (not_mem_erase _ _),
    if_pos rfl, colg_swap, colg_eq hx his, this, ← finset.sum_mul];
  simp [_root_.add_mul, mul_comm, _root_.mul_add]

/-- Pivoting twice in the same place does nothing -/
@[simp] lemma pivot_pivot {i : fin m} {s : fin n} (his : T.to_matrix i s ≠ 0) :
  (T.pivot i s).pivot i s = T :=
begin
  cases T,
  simp [pivot, function.funext_iff],
  split; intros; split_ifs;
  simp [*, mul_assoc, mul_left_comm (T_to_matrix i s), mul_left_comm (T_to_matrix i s)⁻¹,
    mul_comm (T_to_matrix i s), inv_mul_cancel his]
end

/- These two sets are equal_in_flat, the stronger lemma is `flat_pivot` -/
private lemma subset_flat_pivot {i : fin m} {s : fin n} (h : T.to_matrix i s ≠ 0) :
  T.flat ⊆ (T.pivot i s).flat :=
λ x hx,
have ∀ i' : fin m, (univ.erase s).sum (λ j : fin n,
  ite (j = s) (T.to_matrix i' s * (T.to_matrix i s)⁻¹)
    (T.to_matrix i' j + -(T.to_matrix i' s * T.to_matrix i j * (T.to_matrix i s)⁻¹))
      * x ((T.to_partition.swap i s).colg j) 0) =
  (univ.erase s).sum (λ j : fin n, T.to_matrix i' j * x (T.to_partition.colg j) 0 -
    T.to_matrix i j *
      x (T.to_partition.colg j) 0 * T.to_matrix i' s * (T.to_matrix i s)⁻¹),
  from λ i', finset.sum_congr rfl (λ j hj,
    by rw [if_neg (mem_erase.1 hj).1, colg_swap_of_ne _ (mem_erase.1 hj).1];
      simp [mul_add, add_mul, mul_comm, mul_assoc, mul_left_comm]),
begin
  rw mem_flat_iff,
  assume i',
  by_cases hi'i : i' = i,
  { rw eq_comm at hi'i,
    subst hi'i,
    dsimp [pivot],
    simp [mul_inv_cancel h, neg_mul_eq_neg_mul_symm, if_true,
      add_comm, mul_inv_cancel, rowg_swap, eq_self_iff_true, colg_eq' hx h],
    congr, funext, congr },
  { dsimp [pivot],
    simp only [if_neg hi'i],
    rw [← insert_erase (mem_univ s), sum_insert (not_mem_erase _ _),
      if_pos rfl, colg_swap, this, sum_sub_distrib, ← sum_mul, ← sum_mul,
      row_sum_erase_eq hx, rowg_swap_of_ne _ hi'i],
    simp [row_sum_erase_eq hx, mul_add, add_mul,
      mul_comm, mul_left_comm, mul_assoc],
    simp [mul_assoc, mul_left_comm (T.to_matrix i s), mul_left_comm (T.to_matrix i s)⁻¹,
      mul_comm (T.to_matrix i s), inv_mul_cancel h] }
end

variable (T)

@[simp] lemma pivot_pivot_element (i : fin m) (s : fin n) :
  (T.pivot i s).to_matrix i s = (T.to_matrix i s)⁻¹ :=
by simp [pivot, if_pos rfl]

@[simp] lemma pivot_pivot_row {i : fin m} {j s : fin n} (h : j ≠ s) :
  (T.pivot i s).to_matrix i j = -T.to_matrix i j / T.to_matrix i s :=
by dsimp [pivot]; rw [if_pos rfl, if_neg h, div_eq_mul_inv]

@[simp] lemma pivot_pivot_column {i' i : fin m} {s : fin n} (h : i' ≠ i) :
  (T.pivot i s).to_matrix i' s = T.to_matrix i' s / T.to_matrix i s :=
by dsimp [pivot]; rw [if_neg h, if_pos rfl, div_eq_mul_inv]

@[simp] lemma pivot_of_ne_of_ne {i i' : fin m} {j s : fin n} (hi'i : i' ≠ i)
  (hjs : j ≠ s) : (T.pivot i s).to_matrix i' j =
  T.to_matrix i' j - T.to_matrix i' s * T.to_matrix i j / T.to_matrix i s :=
by dsimp [pivot]; rw [if_neg hi'i, if_neg hjs, div_eq_mul_inv]

@[simp] lemma const_pivot_row {i : fin m} {s : fin n} : (T.pivot i s).const i 0 =
  -T.const i 0 / T.to_matrix i s :=
by simp [pivot, if_pos rfl, div_eq_mul_inv]

@[simp] lemma const_pivot_of_ne {i i' : fin m} {s : fin n} (hi'i : i' ≠ i) : (T.pivot i s).const i' 0
  = T.const i' 0 - T.to_matrix i' s * T.const i 0 / T.to_matrix i s :=
by dsimp [pivot]; rw [if_neg hi'i, div_eq_mul_inv]

@[simp] lemma restricted_pivot (i s) : (T.pivot i s).restricted = T.restricted := rfl

@[simp] lemma to_partition_pivot (i s) : (T.pivot i s).to_partition = T.to_partition.swap i s := rfl

@[simp] lemma dead_pivot (i c) : (T.pivot i c).dead = T.dead := rfl

variable {T}

@[simp] lemma flat_pivot {i : fin m} {s : fin n} (hij : T.to_matrix i s ≠ 0) :
  (T.pivot i s).flat = T.flat :=
set.subset.antisymm
  (by conv_rhs { rw ← pivot_pivot hij };
    exact subset_flat_pivot (by simp [hij]))
  (subset_flat_pivot hij)

@[simp] lemma res_set_pivot {i : fin m} {s : fin n} (hij : T.to_matrix i s ≠ 0) :
  (T.pivot i s).res_set = T.res_set :=
by rw [res_set, flat_pivot hij]; refl

@[simp] lemma dead_set_pivot {i : fin m} {j : fin n} (hij : T.to_matrix i j ≠ 0)
  (hdead : j ∉ T.dead) : (T.pivot i j).dead_set = T.dead_set :=
begin
  rw [dead_set, dead_set, flat_pivot hij],
  congr,
  funext x,
  refine forall_congr_eq (λ j', forall_congr_eq (λ hj', _)),
  have hjj' : j' ≠ j, from λ hjj', by simp * at *,
  simp [colg_swap_of_ne _ hjj']
end

@[simp] lemma sol_set_pivot {i : fin m} {j : fin n} (hij : T.to_matrix i j ≠ 0)
  (hdead : j ∉ T.dead) : (T.pivot i j).sol_set = T.sol_set :=
by simp [sol_set_eq_dead_set_inter, dead_set_pivot hij hdead, flat_pivot hij]

/-- Two row variables are `equal_in_flat` iff the corresponding rows of the tableau are equal -/
lemma equal_in_flat_row_row {i i' : fin m} :
  T.equal_in_flat (T.to_partition.rowg i) (T.to_partition.rowg i')
  ↔ (T.const i 0 = T.const i' 0 ∧ ∀ j : fin n, T.to_matrix i j = T.to_matrix i' j) :=
⟨λ h, have Hconst : T.const i 0 = T.const i' 0,
    by simpa [of_col_rowg] using h (T.of_col 0) (of_col_mem_flat _ _),
  ⟨Hconst,
    λ j, begin
      have := h (T.of_col (single j (0 : fin 1)).to_matrix) (of_col_mem_flat _ _),
      rwa [of_col_rowg, of_col_rowg, add_val, add_val, matrix_mul_apply, matrix_mul_apply,
        symm_single_apply, Hconst, add_right_cancel_iff] at this,
    end⟩,
λ h x hx, by simp [mem_flat_iff.1 hx, h.1, h.2]⟩

/-- A row variable is equal_in_flat to a column variable iff its row has zeros, and a single
  one in that column. -/
lemma equal_in_flat_row_col {i : fin m} {j : fin n} :
  T.equal_in_flat (T.to_partition.rowg i) (T.to_partition.colg j)
  ↔ (∀ j', j' ≠ j → T.to_matrix i j' = 0) ∧ T.const i 0 = 0 ∧ T.to_matrix i j = 1 :=
⟨λ h, have Hconst : T.const i 0 = 0,
    by simpa [of_col_rowg] using h (T.of_col 0) (of_col_mem_flat _ _),
  ⟨assume j' hj', begin
      have := h (T.of_col (single j' (0 : fin 1)).to_matrix) (of_col_mem_flat _ _),
      rwa [of_col_rowg, of_col_colg, add_val, Hconst, add_zero, matrix_mul_apply,
        symm_single_apply, pequiv.to_matrix, single_apply_of_ne hj',
        if_neg (option.not_mem_none _)] at this
    end,
  Hconst,
  begin
    have := h (T.of_col (single j (0 : fin 1)).to_matrix) (of_col_mem_flat _ _),
    rwa [of_col_rowg, of_col_colg, add_val, Hconst, add_zero, matrix_mul_apply,
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
  (hdead : T₁.dead = T₂.dead)
  (hres : T₁.restricted = T₂.restricted) : T₁ = T₂ :=
have hconst : T₁.const = T₂.const,
  by rw [set.ext_iff] at hflat; simpa [of_col, flat, hpartition, matrix.mul_assoc,
    mul_right_eq_of_mul_eq (rowp_transpose_mul_rowp _),
    mul_right_eq_of_mul_eq (colp_transpose_mul_rowp _)] using
  (hflat (T₁.of_col 0)).1 (of_col_mem_flat _ _),
have hmatrix : T₁.to_matrix = T₂.to_matrix,
  from mul_single_ext $ λ j, begin
    rw [set.ext_iff] at hflat,
    have := (hflat (T₁.of_col (single j 0).to_matrix)).1 (of_col_mem_flat _ _),
    simpa [of_col, hconst, hpartition, flat, matrix.mul_add, matrix.mul_assoc,
        mul_right_eq_of_mul_eq (rowp_transpose_mul_colp _),
        mul_right_eq_of_mul_eq (rowp_transpose_mul_rowp _),
        mul_right_eq_of_mul_eq (colp_transpose_mul_colp _),
        mul_right_eq_of_mul_eq (colp_transpose_mul_rowp _)] using
      (hflat (T₁.of_col (single j 0).to_matrix)).1 (of_col_mem_flat _ _)
  end,
by cases T₁; cases T₂; simp * at *

end predicate_lemmas

/-- Conditions for unboundedness based on reading the tableau. The conditions are equivalent to the
  simplex pivot rule failing to find a pivot row. -/
lemma unbounded_of_tableau {T : tableau m n} {obj : fin m} {j : fin n} (hT : T.feasible)
  (hdead : j ∉ T.dead)
  (hrow : ∀ i, obj ≠ i → T.to_partition.rowg i ∈ T.restricted →
    0 ≤ T.to_matrix obj j / T.to_matrix i j)
  (hc : (T.to_matrix obj j ≠ 0 ∧ T.to_partition.colg j ∉ T.restricted)
    ∨ (0 < T.to_matrix obj j ∧ T.to_partition.colg j ∈ T.restricted)) :
  T.is_unbounded_above (T.to_partition.rowg obj) :=
have hToj : T.to_matrix obj j ≠ 0, from λ h, by simpa [h, lt_irrefl] using hc,
(lt_or_gt_of_ne hToj).elim
  (λ hToj : T.to_matrix obj j < 0, is_unbounded_above_rowg_of_nonpos hT j
    (hc.elim and.right (λ h, (not_lt_of_gt hToj h.1).elim)) hdead
    (λ i hi, classical.by_cases
      (λ hoi : obj = i, le_of_lt (hoi ▸ hToj))
      (λ hoi : obj ≠ i, inv_nonpos.1 $ nonpos_of_mul_nonneg_right (hrow _ hoi hi) hToj))
    hToj)
  (λ hToj : 0 < T.to_matrix obj j, is_unbounded_above_rowg_of_nonneg hT j
    (λ i hi, classical.by_cases
      (λ hoi : obj = i, le_of_lt (hoi ▸ hToj))
      (λ hoi : obj ≠ i, inv_nonneg.1 $ nonneg_of_mul_nonneg_left (hrow _ hoi hi) hToj))
    hdead hToj)

/-- Conditions for the tableau being feasible, that must be satisified by a simplex pivot rule -/
lemma feasible_pivot {T : tableau m n} (hT : T.feasible) {i j}
  (hres : T.to_partition.rowg i ∈ T.restricted)
  (hpos : T.to_partition.colg j ∈ T.restricted → T.to_matrix i j < 0)
  (himin : ∀ (i' : fin m), T.to_partition.rowg i' ∈ T.restricted →
    0 < T.to_matrix i' j / T.to_matrix i j →
    abs (T.const i 0 / T.to_matrix i j) ≤ abs (T.const i' 0 / T.to_matrix i' j)) :
  (T.pivot i j).feasible :=
begin
  assume i' hi',
  dsimp only [pivot],
  by_cases hii : i' = i,
  { subst i',
    rw [if_pos rfl, neg_mul_eq_neg_mul_symm, neg_nonneg],
    exact mul_nonpos_of_nonneg_of_nonpos (hT _ hres) (inv_nonpos.2 $ le_of_lt (by simp * at *)) },
  { rw if_neg hii,
    rw [to_partition_pivot, rowg_swap_of_ne _ hii, restricted_pivot] at hi',
    by_cases hTii : 0 < T.to_matrix i' j / T.to_matrix i j,
    { have hTi'c0 : T.to_matrix i' j ≠ 0, from λ h, by simpa [h, lt_irrefl] using hTii,
      have hTic0 : T.to_matrix i j ≠ 0, from λ h, by simpa [h, lt_irrefl] using hTii,
      have := himin _ hi' hTii,
      rwa [abs_div, abs_div, abs_of_nonneg (hT _ hres), abs_of_nonneg (hT _ hi'),
        le_div_iff (abs_pos_iff.2 hTi'c0), div_eq_mul_inv, mul_right_comm, ← abs_inv, mul_assoc,
        ← abs_mul, ← div_eq_mul_inv, abs_of_nonneg (le_of_lt hTii), ← sub_nonneg,
        ← mul_div_assoc, div_eq_mul_inv, mul_comm (T.const i 0)] at this },
    { refine add_nonneg (hT _ hi') (neg_nonneg.2 _),
      rw [mul_assoc, mul_left_comm],
      exact mul_nonpos_of_nonneg_of_nonpos (hT _ hres) (le_of_not_gt hTii) } }
end

lemma feasible_simplex_pivot {T : tableau m n} {obj : fin m} (hT : T.feasible) {i j}
  (hres : T.to_partition.rowg i ∈ T.restricted)
  (hineg : T.to_matrix obj j / T.to_matrix i j < 0)
  (himin : ∀ (i' : fin m), obj ≠ i' → T.to_partition.rowg i' ∈ T.restricted →
          T.to_matrix obj j / T.to_matrix i' j < 0 →
          abs (T.const i 0 / T.to_matrix i j) ≤ abs (T.const i' 0 / T.to_matrix i' j))
  (hc : T.to_partition.colg j ∈ T.restricted → 0 < T.to_matrix obj j) :
  (T.pivot i j).feasible :=
feasible_pivot hT hres (λ hcres, inv_neg'.1 (neg_of_mul_neg_left hineg (le_of_lt (hc hcres))))
  (λ i' hi'res hii,
    have hobji : obj ≠ i',
      from λ hobji, not_lt_of_gt hii (hobji ▸ hineg),
    (himin _ hobji hi'res $
      have hTrc0 : T.to_matrix i j ≠ 0, from λ _, by simp [*, lt_irrefl] at *,
      suffices (T.to_matrix obj j / T.to_matrix i j) / (T.to_matrix i' j / T.to_matrix i j) < 0,
        by rwa [div_div_div_cancel_right _ _ hTrc0] at this,
      div_neg_of_neg_of_pos hineg hii))

/-- Used in sign_of_max -/
lemma feasible_pivot_obj_of_nonpos {T : tableau m n} {obj : fin m} (hT : T.feasible) {j}
  (hc : T.to_partition.colg j ∈ T.restricted → 0 < T.to_matrix obj j)
  (hr : ∀ i, obj ≠ i → T.to_partition.rowg i ∈ T.restricted →
    0 ≤ T.to_matrix obj j / T.to_matrix i j)
  (hobj : T.const obj 0 ≤ 0) : feasible (T.pivot obj j) :=
λ i hi,
if hiobj : i = obj
then by rw [hiobj, const_pivot_row, neg_div, neg_nonneg];
  exact mul_nonpos_of_nonpos_of_nonneg hobj (le_of_lt $ by simp [*, inv_pos'] at *)
else begin
  rw [const_pivot_of_ne _ hiobj],
  rw [to_partition_pivot, rowg_swap_of_ne _ hiobj, restricted_pivot] at hi,
  refine add_nonneg (hT _ hi) (neg_nonneg.2 _),
  rw [div_eq_mul_inv, mul_right_comm],
  exact mul_nonpos_of_nonneg_of_nonpos
    (inv_nonneg.1 (by simpa [mul_inv'] using hr _ (ne.symm hiobj) hi))
    hobj
end

lemma simplex_const_obj_le {T : tableau m n} {obj : fin m} (hT : T.feasible) {i j}
  (hres : T.to_partition.rowg i ∈ T.restricted)
  (hineg : T.to_matrix obj j / T.to_matrix i j < 0) :
  T.const obj 0 ≤ (T.pivot i j).const obj 0 :=
have obj ≠ i, from λ hor, begin
  subst hor,
  by_cases h0 : T.to_matrix obj j = 0,
  { simp [lt_irrefl, *] at * },
  { simp [div_self h0, not_lt_of_le zero_le_one, *] at * }
end,
by simp only [le_add_iff_nonneg_right, sub_eq_add_neg, neg_nonneg, mul_assoc, div_eq_mul_inv,
    mul_left_comm (T.to_matrix obj j), const_pivot_of_ne _ this];
  exact mul_nonpos_of_nonneg_of_nonpos (hT _ hres) (le_of_lt hineg)

lemma const_eq_zero_of_const_obj_eq {T : tableau m n} {obj : fin m} (hT : T.feasible) {i j}
  (hc : T.to_matrix obj j ≠ 0) (hrc : T.to_matrix i j ≠ 0) (hobjr : obj ≠ i)
  (hobj : (T.pivot i j).const obj 0 = T.const obj 0) :
  T.const i 0 = 0 :=
by rw [const_pivot_of_ne _ hobjr, sub_eq_iff_eq_add, ← sub_eq_iff_eq_add', sub_self,
    eq_comm, div_eq_mul_inv, mul_eq_zero, mul_eq_zero, inv_eq_zero] at hobj; tauto

end tableau
