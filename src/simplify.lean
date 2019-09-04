import dead_simplex

open matrix fintype finset function pequiv partition tableau tableau.termination
variables {m n : ℕ}

local notation `rvec` : 2000 n := matrix (fin 1) (fin n) ℚ
local notation `cvec` : 2000 m := matrix (fin m) (fin 1) ℚ
local infix ` ⬝ `:70 := matrix.mul
local postfix `ᵀ` : 1500 := transpose

@[derive _root_.decidable_eq] inductive undo : Type
| unrestrict : ℕ → undo
| revive     : ℕ → undo
| delete     : ℕ → undo

instance : has_repr undo :=
⟨λ u, undo.cases_on u
  (λ n, "unrestrict " ++ repr n)
  (λ n, "revive " ++ repr n)
  (λ n, "delete " ++ repr n)⟩

open undo

structure stableau (m n : ℕ) extends tableau m n :=
(feasible : to_tableau.feasible)
(undo_stack : list undo)

namespace stableau

section predicates
variable (T : stableau m n)

/-- The affine subspace represented by the tableau ignoring nonnegativity restrictiions -/
@[reducible] def flat : set (cvec (m + n)) := T.to_tableau.flat

/-- The res_set is the subset of ℚ^(m+n) that satisifies the nonnegativity constraints of
  the tableau, and the affine conditions -/
@[reducible] def res_set : set (cvec (m + n)) := T.to_tableau.res_set

/-- The dead_set is the subset of ℚ^(m+n) such that all dead variables are zero, and satisfies
  the affine conditions -/
@[reducible] def dead_set : set (cvec (m + n)) := T.to_tableau.dead_set

/-- The `sol_set` is the set of vector that satisfy the affine constraints the dead variable
  constraints, and the nonnegativity constraints. -/
@[reducible] def sol_set : set (cvec (m + n)) := T.to_tableau.sol_set

lemma sol_set_eq_res_set_inter :
  T.sol_set = res_set T ∩ { x | ∀ j, j ∈ T.dead → x (T.to_partition.colg j) 0 = 0 } := rfl

lemma sol_set_eq_dead_set_inter :
   T.sol_set = dead_set T ∩ { x | ∀ i, i ∈ T.restricted → 0 ≤ x i 0 } :=
set.inter_right_comm _ _ _

lemma sol_set_eq_res_set_inter_dead_set : T.sol_set = T.res_set ∩ T.dead_set :=
tableau.sol_set_eq_res_set_inter_dead_set _

/-- Predicate for a variable being unbounded above in the `res_set` -/
@[reducible] def is_unbounded_above (i : fin (m + n)) : Prop := T.to_tableau.is_unbounded_above i

/-- Predicate for a variable being unbounded below in the `res_set` -/
@[reducible] def is_unbounded_below (i : fin (m + n)) : Prop := T.to_tableau.is_unbounded_below i

@[reducible] def is_optimal (x : cvec (m + n)) (i : fin (m + n)) : Prop :=
T.to_tableau.is_optimal x i

lemma is_optimal_iff {T : stableau m n} (x : cvec (m + n)) (i : fin (m + n)) :
  T.is_optimal x i ↔ x ∈ T.sol_set ∧ ∀ y : cvec (m + n), y ∈ sol_set T → y i 0 ≤ x i 0 := iff.rfl

/-- Is this equivalent to `∀ (x : cvec (m + n)), x ∈ res_set T → x i 0 = x j 0`? No -/
@[reducible] def equal_in_flat (i j : fin (m + n)) : Prop := T.to_tableau.equal_in_flat i j

/-- Returns an element of the `flat` after assigning values to the column variables -/
@[reducible] def of_col (x : cvec n) : cvec (m + n) :=
T.to_tableau.of_col x

@[simp] lemma of_col_zero_mem_sol_set : T.of_col 0 ∈ T.sol_set :=
tableau.of_col_zero_mem_sol_set_iff.2 T.feasible

@[simp] lemma of_col_rowg (x : cvec n) (r : fin m) :
  of_col T x (T.to_partition.rowg r) = (T.to_matrix ⬝ x + T.const) r := tableau.of_col_rowg _ _ _

end predicates

section simplex

def simplex (w : tableau m n → bool) (obj : fin m) (T : stableau m n) :
  stableau m n × termination :=
let s := T.to_tableau.simplex w obj T.feasible in
prod.mk
  { feasible := feasible_simplex,
    undo_stack := T.undo_stack,
    ..s.1 }
  s.2

/- Transfer lemmas about `tableau.simplex` onto `stableau.simplex` -/
@[simp] lemma simplex_to_tableau (w : tableau m n → bool) (obj : fin m) (T : stableau m n) :
  (T.to_tableau.simplex w obj T.feasible).1 = (T.simplex w obj).1.to_tableau :=
tableau.eta.symm

@[simp] lemma rowg_simplex (T : stableau m n) (w : tableau m n → bool)
  (obj : fin m) : (T.simplex w obj).1.to_partition.rowg obj = T.to_partition.rowg obj :=
tableau.rowg_simplex _ _ _ _

@[simp] lemma flat_simplex (T : stableau m n) (w : tableau m n → bool)
  (obj : fin m) : (T.simplex w obj).1.flat = T.flat :=
tableau.flat_simplex _ _ _ _

@[simp] lemma res_set_simplex (T : stableau m n) (w : tableau m n → bool)
  (obj : fin m) : (T.simplex w obj).1.res_set = T.res_set :=
tableau.res_set_simplex _ _ _ _

@[simp] lemma dead_set_simplex (T : stableau m n) (w : tableau m n → bool)
  (obj : fin m) : (T.simplex w obj).1.dead_set = T.dead_set :=
tableau.dead_set_simplex _ _ _ _

@[simp] lemma sol_set_simplex (T : stableau m n) (w : tableau m n → bool) (obj : fin m) :
  (T.simplex w obj).1.sol_set = T.sol_set :=
tableau.sol_set_simplex _ _ _ _

@[simp] lemma of_col_simplex_mem_sol_set (T : stableau m n) (w : tableau m n → bool) (obj : fin m) :
  (T.simplex w obj).1.of_col 0 ∈ T.sol_set :=
by rw [← sol_set_simplex T w obj]; exact of_col_zero_mem_sol_set _

@[simp] lemma of_col_simplex_rowg {T : stableau m n} {w : tableau m n → bool}  {obj : fin m}
  (x : cvec n) :
  (T.simplex w obj ).1.of_col x (T.to_partition.rowg obj) =
  ((T.simplex w obj).1.to_matrix ⬝ x + (T.simplex w obj).1.const) obj :=
tableau.of_col_simplex_rowg _

@[simp] lemma is_unbounded_above_simplex {T : stableau m n} {w : tableau m n → bool}
  {obj : fin m} {v : fin (m + n)} : is_unbounded_above (T.simplex w obj).1 v ↔
  is_unbounded_above T v :=
tableau.is_unbounded_above_simplex

@[simp] lemma is_optimal_simplex {T : stableau m n} {w : tableau m n → bool}
  {obj : fin m} {x : cvec (m + n)} {v : fin (m + n)} : is_optimal (T.simplex w obj).1 x v ↔
  is_optimal T x v :=
tableau.is_optimal_simplex

lemma termination_eq_while_iff {T : stableau m n} {w : tableau m n → bool}
  {obj : fin m} : (T.simplex w obj).2 = while ↔ w (T.simplex w obj).1.to_tableau = ff :=
by rw [simplex, tableau.termination_eq_while_iff, simplex_to_tableau]; refl

lemma termination_eq_optimal_iff {T : stableau m n}
  {w : tableau m n → bool} {obj : fin m} : (T.simplex w obj).2 = optimal ↔
  w (T.simplex w obj).1.to_tableau = tt ∧
  is_optimal T ((T.simplex w obj).1.of_col 0) (T.to_partition.rowg obj) :=
by rw [simplex, tableau.termination_eq_optimal_iff, simplex_to_tableau]; refl

lemma termination_eq_unbounded_iff {T : stableau m n} {w : tableau m n → bool} {obj : fin m} :
  (T.simplex w obj).2 = unbounded ↔
  w (T.simplex w obj).1.to_tableau = tt ∧ is_unbounded_above T (T.to_partition.rowg obj) :=
by rw [simplex, tableau.termination_eq_unbounded_iff, simplex_to_tableau]; refl

end simplex

section add_row

/-- adds a new row without making it a restricted variable. -/
def add_row_aux (T : tableau m n) (fac : rvec (m + n)) (k : ℚ) : tableau (m + 1) n :=
{ to_matrix := λ i j, if hm : i.1 < m
    then T.to_matrix (fin.cast_lt i hm) j
    else fac 0 (T.to_partition.colg j) +
      univ.sum (λ i' : fin m, fac 0 (T.to_partition.rowg i') * T.to_matrix i' j),
  const := λ i j, if hm : i.1 < m
    then T.const (fin.cast_lt i hm) j
    else k +
      univ.sum (λ i' : fin m, fac 0 (T.to_partition.rowg i') * T.const i' 0),
  to_partition := T.to_partition.add_row,
  restricted := T.restricted.map ⟨fin.castp,
    λ ⟨_, _⟩ ⟨_, _⟩ h, fin.eq_of_veq (fin.veq_of_eq h : _)⟩,
  dead := T.dead }

@[simp] lemma add_row_aux_to_partition (T : tableau m n) (fac : rvec (m + n)) (k : ℚ) :
  (add_row_aux T fac k).to_partition = T.to_partition.add_row := rfl

lemma add_row_aux_to_matrix (T : tableau m n) (fac : rvec (m + n)) (k : ℚ) :
  (add_row_aux T fac k).to_matrix = λ i j, if hm : i.1 < m
    then T.to_matrix (fin.cast_lt i hm) j else fac 0 (T.to_partition.colg j) +
      univ.sum (λ i' : fin m, fac 0 (T.to_partition.rowg i') * T.to_matrix i' j) := rfl

lemma add_row_aux_const (T : tableau m n) (fac : rvec (m + n)) (k : ℚ) :
  (add_row_aux T fac k).const = λ i j, if hm : i.1 < m
    then T.const (fin.cast_lt i hm) j else k +
    univ.sum (λ i' : fin m, fac 0 (T.to_partition.rowg i') * T.const i' 0) := rfl

lemma add_row_aux_restricted (T : tableau m n) (fac : rvec (m + n)) (k : ℚ) :
  (add_row_aux T fac k).restricted = T.restricted.image fin.castp :=
by simp [add_row_aux, map_eq_image]

@[elab_as_eliminator] def fin.cases_last {n : ℕ}
  {C : fin n.succ → Sort*} (Hl : C (fin.last n)) (Hs : ∀ i : fin n, C i.cast_succ)
  (i : fin n.succ) : C i :=
if hi : fin.last n = i then eq.rec_on hi Hl
else have i = fin.cast_succ ⟨i, lt_of_le_of_ne (nat.le_of_lt_succ i.2) (ne.symm (fin.vne_of_ne hi))⟩,
  from fin.eq_of_veq rfl,
eq.rec_on this.symm (Hs _)

@[simp] lemma cases_last_last {n : ℕ}
  {C : fin n.succ → Sort*} (Hl : C (fin.last n)) (Hs : ∀ i : fin n, C i.cast_succ) :
  (fin.cases_last Hl Hs (fin.last n) : C (fin.last n)) = Hl :=
by simp [fin.cases_last]

lemma cast_succ_lt_last {n : ℕ} (i : fin n) : i.cast_succ < fin.last n := i.2

@[simp] lemma cases_last_cast_succ {n : ℕ}
  {C : fin n.succ → Sort*} (Hl : C (fin.last n)) (Hs : ∀ i : fin n, C i.cast_succ)
  (i : fin n) : (fin.cases_last Hl Hs i.cast_succ : C i.cast_succ) = Hs i :=
by simp [fin.cases_last, ne_of_gt (cast_succ_lt_last i)]; cases i; refl

lemma add_row_aux_feasible {T : tableau m n} (hfT : T.feasible) (fac : rvec (m + n)) (k : ℚ) :
  (add_row_aux T fac k).feasible :=
λ i, fin.cases_last
  (by simp [add_row_aux_restricted, add_row_aux_const, add_row_rowg_last])
  (λ i, by simp [add_row_aux_const, dif_pos (show i.cast_succ.1 < m, from i.2),
    fin.cast_lt_cast_succ, add_row_aux_restricted, add_row_aux_to_partition, add_row_rowg_cast_succ,
    mem_image, exists_imp_distrib, fin.injective_castp.eq_iff, @forall_swap _ (_ = _), hfT i]
      {contextual := tt}) i

def add_row (T : stableau m n) (fac : rvec (m + n)) (k : ℚ) : stableau (m + 1) n :=
{ undo_stack := delete m :: T.undo_stack,
  feasible := add_row_aux_feasible T.feasible _ _,
  ..add_row_aux T.to_tableau fac k }

@[simp] lemma add_row_to_partition (T : stableau m n) (fac : rvec (m + n)) (k : ℚ) :
  (add_row T fac k).to_partition = T.to_partition.add_row := rfl

lemma add_row_to_matrix (T : stableau m n) (fac : rvec (m + n)) (k : ℚ) :
  (add_row T fac k).to_matrix = λ i j, if hm : i.1 < m
    then T.to_matrix (fin.cast_lt i hm) j else fac 0 (T.to_partition.colg j) +
      univ.sum (λ i' : fin m, fac 0 (T.to_partition.rowg i') * T.to_matrix i' j) := rfl

lemma add_row_const (T : stableau m n) (fac : rvec (m + n)) (k : ℚ) :
  (add_row T fac k).const = λ i j, if hm : i.1 < m
    then T.const (fin.cast_lt i hm) j else k +
    univ.sum (λ i' : fin m, fac 0 (T.to_partition.rowg i') * T.const i' 0) := rfl

lemma add_row_restricted (T : stableau m n) (fac : rvec (m + n)) (k : ℚ) :
  (add_row T fac k).restricted = T.restricted.image fin.castp :=
add_row_aux_restricted _ _ _

@[simp] lemma add_row_dead (T : stableau m n) (fac : rvec (m + n)) (k : ℚ) :
  (add_row T fac k).dead = T.dead := rfl

lemma minor_mem_flat_of_mem_add_row_flat {T : stableau m n} {fac : rvec (m + n)} {k : ℚ}
  {x : cvec (m + 1 + n)} : x ∈ (T.add_row fac k).flat → minor x fin.castp id ∈ T.flat :=
begin
  rw [mem_flat_iff, mem_flat_iff],
  intros h r,
  have := h (fin.cast_succ r),
  simp [add_row_rowg_cast_succ, add_row_const, add_row_to_matrix,
    (show (fin.cast_succ r).val < m, from r.2), add_row_colg] at this,
  simpa
end

lemma minor_mem_res_set_of_mem_add_row_res_set {T : stableau m n} {fac : rvec (m + n)} {k : ℚ}
  {x : cvec (m + 1 + n)} : x ∈ (T.add_row fac k).res_set → minor x fin.castp id ∈ T.res_set :=
and_implies minor_mem_flat_of_mem_add_row_flat begin
  assume h v,
  simp only [set.mem_set_of_eq, add_row_restricted, mem_image, exists_imp_distrib] at h,
  simpa [add_row_restricted, matrix.minor, id.def] using h (fin.castp v) v
end

lemma minor_mem_dead_set_of_mem_add_row_dead_set {T : stableau m n} {fac : rvec (m + n)} {k : ℚ}
  {x : cvec (m + 1 + n)} : x ∈ (T.add_row fac k).dead_set → minor x fin.castp id ∈ T.dead_set :=
and_implies minor_mem_flat_of_mem_add_row_flat $
  by simp only [add_row_colg, add_row_to_partition];
  exact id

lemma minor_mem_sol_set_of_mem_add_row_sol_set {T : stableau m n} {fac : rvec (m + n)} {k : ℚ}
  {x : cvec (m + 1 + n)} : x ∈ (T.add_row fac k).sol_set → minor x fin.castp id ∈ T.sol_set :=
by rw [sol_set_eq_res_set_inter_dead_set, sol_set_eq_res_set_inter_dead_set];
  exact and_implies minor_mem_res_set_of_mem_add_row_res_set
    minor_mem_dead_set_of_mem_add_row_dead_set

lemma add_row_new_eq_sum_fac (T : stableau m n) (fac : rvec (m + n)) (k : ℚ)
  (x : cvec (m + 1 + n)) (hx : x ∈ (T.add_row fac k).flat) :
  x fin.lastp 0 = univ.sum (λ v : fin (m + n), fac 0 v * x (fin.castp v) 0) + k :=
calc x fin.lastp 0 = x ((T.add_row fac k).to_partition.rowg (fin.last _)) 0 :
  by simp [add_row_rowg_last]
... = univ.sum (λ j : fin n, _) + (T.add_row fac k).const _ _ : mem_flat_iff.1 hx _
... = k +
  univ.sum (λ j, (fac 0 (T.to_partition.colg j) * x (T.to_partition.add_row.colg j) 0)) +
  (univ.sum (λ j, univ.sum (λ i, fac 0 (T.to_partition.rowg i) * T.to_matrix i j *
      x (T.to_partition.add_row.colg j) 0))
    + univ.sum (λ i, fac 0 (T.to_partition.rowg i) * T.const i 0)) :
  by simp [add_row_to_matrix, add_row_const, fin.last, add_mul, sum_add_distrib, sum_mul]
... = k +
  univ.sum (λ j, (fac 0 (T.to_partition.colg j) * x (T.to_partition.add_row.colg j) 0)) +
  (univ.sum (λ i, univ.sum (λ j, fac 0 (T.to_partition.rowg i) * T.to_matrix i j *
    x (T.to_partition.add_row.colg j) 0))
    + univ.sum (λ i, fac 0 (T.to_partition.rowg i) * T.const i 0)) : by rw [sum_comm]
... = k +
  univ.sum (λ j, (fac 0 (T.to_partition.colg j) * x (T.to_partition.add_row.colg j) 0)) +
  univ.sum (λ i : fin m, (fac 0 (T.to_partition.rowg i) * x (fin.castp (T.to_partition.rowg i)) 0)) :
begin
  rw [← sum_add_distrib],
  have : ∀ r : fin m, x (fin.castp (T.to_partition.rowg r)) 0 =
    sum univ (λ (c : fin n), T.to_matrix r c * x (fin.castp (T.to_partition.colg c)) 0) +
    T.const r 0, from mem_flat_iff.1 (minor_mem_flat_of_mem_add_row_flat hx),
  simp [this, mul_add, add_row_colg, mul_sum, mul_assoc]
end
... = ((univ.image T.to_partition.colg).sum (λ v, (fac 0 v * x (fin.castp v) 0)) +
  (univ.image T.to_partition.rowg).sum (λ v, (fac 0 v * x (fin.castp v) 0))) + k :
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

section sign_of_max_row

def sign_of_max_row (T : stableau m n) (obj : fin m) : stableau m n × ℤ :=
let T' := T.simplex (λ T', T'.const obj 0 ≤ 0) obj in prod.mk T'.1 $
match T'.2 with
| while     := 1
| unbounded := 1
| optimal   := if T'.1.const obj 0 = 0 then 0 else -1
end

lemma sign_of_max_row_eq_zero {T : stableau m n} {obj : fin m} :
  (sign_of_max_row T obj).2 = 0 ↔
    ∃ x : cvec (m + n), x (T.to_partition.rowg obj) 0 = 0 ∧ is_optimal T x
      (T.to_partition.rowg obj) :=
let T' := T.simplex (λ T', T'.const obj 0 ≤ 0) obj in
begin
  cases h : T'.2,
  { simp only [sign_of_max_row, *, termination_eq_while_iff, is_optimal_iff, classical.not_forall,
      not_exists, exists_prop, false_iff, not_and, not_le, to_bool_ff_iff, one_ne_zero] at *,
    assume x hx0 hxs,
    refine ⟨T'.1.of_col 0, _⟩,
    simpa [T', hx0] },
  { simp only [sign_of_max_row, *, termination_eq_unbounded_iff, is_unbounded_above,
      classical.not_forall, not_exists, exists_prop, false_iff, not_and, not_le, to_bool_iff,
      one_ne_zero, is_optimal_iff] at * {contextual := tt},
    cases h.2 1 with y hy,
    assume x hxs hx,
    use [y, hy.1],
    exact lt_of_lt_of_le zero_lt_one hy.2 },
  { simp only [sign_of_max_row, *, termination_eq_optimal_iff, is_unbounded_above,
      classical.not_forall, not_exists, exists_prop, false_iff, not_and, not_le, to_bool_iff,
      one_ne_zero] at * {contextual := tt},
    split_ifs with h0,
    { simp only [eq_self_iff_true, true_iff],
      refine ⟨_, _, _, h.2.2⟩;
      simp [h0] },
    { simp only [is_optimal_iff, not_exists, neg_eq_zero, one_ne_zero, false_iff, not_and],
      assume x hx0 hsx ,
      exact absurd (le_antisymm h.1 (by simpa [hx0] using h.2.2 x hsx)) h0 } }
end

lemma sign_of_max_row_eq_one {T : stableau m n} {obj : fin m} :
  (sign_of_max_row T obj).2 = 1 ↔
    ∃ x : cvec (m + n), x ∈ sol_set T ∧ 0 < x (T.to_partition.rowg obj) 0 :=
let T' := T.simplex (λ T', T'.const obj 0 ≤ 0) obj in
begin
  cases h : T'.2,
  { simp only [sign_of_max_row, *, termination_eq_while_iff, eq_self_iff_true, true_iff,
      to_bool_ff_iff, not_le] at *,
    exact ⟨T'.1.of_col 0, by simp [*, T']⟩ },
  { simp only [sign_of_max_row, *, termination_eq_unbounded_iff, eq_self_iff_true,
      true_iff, to_bool_iff] at *,
    cases h.2 1 with y hy,
    use [y, hy.1],
    exact lt_of_lt_of_le zero_lt_one hy.2 },
  { simp only [sign_of_max_row, *, termination_eq_optimal_iff, to_bool_iff] at *,
    suffices : ∀ (x : matrix (fin (m + n)) (fin 1) ℚ), x ∈ sol_set T →
      x (T.to_partition.rowg obj) 0 ≤ 0,
    { split_ifs; simpa [show ¬(-1 : ℤ) = 1, from dec_trivial] },
    assume x hx,
    exact le_trans (h.2.2 x hx) (by simpa using h.1) }
end

lemma sign_of_max_row_eq_neg_one {T : stableau m n} {obj : fin m} :
  (sign_of_max_row T obj).2 = -1 ↔
    ∀ x : cvec (m + n), x ∈ sol_set T → x (T.to_partition.rowg obj) 0 < 0 :=
let T' := T.simplex (λ T', T'.const obj 0 ≤ 0) obj in
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
  { simp only [sign_of_max_row, *, termination_eq_optimal_iff, to_bool_iff] at *,
    split_ifs,
    { simp [show (0 : ℤ) ≠ -1, from dec_trivial, classical.not_forall],
      use T'.1.of_col 0, simp * },
    { simp only [eq_self_iff_true, true_iff],
      assume x hx,
      exact lt_of_le_of_lt (h.2.2 x hx) (by apply lt_of_le_of_ne; simp; tauto) } }
end

end sign_of_max_row

section to_row

def to_row_pivot_row (T : stableau m n) (c : fin n) : option (fin m) :=
if c ∈ T.dead then none
else ((list.fin_range m).filter (λ r, (T.to_partition.rowg r ∈ T.restricted ∧
  T.to_matrix r c < 0))).argmax (λ r, T.const r 0 / T.to_matrix r c)

lemma feasible_to_row_pivot_row {T : stableau m n} (c : fin n) (r)
  (hr : r ∈ to_row_pivot_row T c) : (T.to_tableau.pivot r c).feasible :=
begin
  unfold to_row_pivot_row at hr,
  split_ifs at hr,
  { simpa using hr },
  { simp only [to_row_pivot_row, list.mem_argmax_iff, list.mem_filter] at hr,
    refine feasible_pivot T.feasible (by tauto) (by tauto) _,
    assume i hir hir0,
    have hic0 : T.to_matrix i c < 0,
      from neg_of_mul_pos_left hir0 (inv_nonpos.2 $ le_of_lt $ by tauto),
    rw [abs_of_nonpos (div_nonpos_of_nonneg_of_neg (T.feasible _ hir) hic0),
      abs_of_nonpos (div_nonpos_of_nonneg_of_neg (T.feasible r (by tauto)) hr.1.2.2), neg_le_neg_iff],
    apply hr.2.1,
    simp,
  tauto }
end

def to_row (T : stableau m n) (c : fin n) : stableau m n × bool :=
match to_row_pivot_row T c, feasible_to_row_pivot_row c with
| none, h := (T, ff)
| some r, h :=
  ({ feasible := h _ rfl,
     undo_stack := T.undo_stack,
     ..T.to_tableau.pivot r c },
  tt)
end

lemma to_row_eq_ff_iff_eq_self {T : stableau m n} {c : fin n} : (T.to_row c).2 = ff ↔
  (T.to_row c).1 = T :=
begin
  dsimp [to_row],
  cases h : to_row_pivot_row T c,
  { simp only [h, to_row._match_1],
    dsimp [to_row_pivot_row] at h,
    split_ifs at h with hdead; simp [hdead] },
  { simp [h, to_row._match_1],
    dsimp [to_row_pivot_row] at h,
    split_ifs at h with hdead,
    { simpa using h },
    { cases T with T hT, cases T,
      simp } }
end

lemma to_row_eq_ff {T : stableau m n} {c : fin n} : (T.to_row c).2 = ff →
  (c ∈ T.dead ∨ is_unbounded_above T (T.to_partition.colg c)) :=
begin
  dsimp [to_row],
  cases h : to_row_pivot_row T c,
  { simp only [h, to_row._match_1],
    dsimp [to_row_pivot_row] at h,
    split_ifs at h with hdead,
    { simp [hdead] },
    { simp only [true_and, forall_prop_of_true, eq_self_iff_true],
      right,
      exact is_unbounded_above_colg T.feasible hdead (by simpa [list.filter_eq_nil] using h) } },
  { simp [h, to_row._match_1] }
end

lemma to_row_eq_tt {T : stableau m n} {c : fin n} (h : (T.to_row c).2 = tt →
  T.to_row

end to_row

def sign_of_max (T : stableau m n) (c : fin not_exists)


end stableau
