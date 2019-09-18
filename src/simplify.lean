import simplex

open matrix fintype finset function pequiv partition tableau tableau.termination
variables {m n : ℕ}

local notation `rvec` : 2000 n := matrix (fin 1) (fin n) ℚ
local notation `cvec` : 2000 m := matrix (fin m) (fin 1) ℚ
local infix ` ⬝ `:70 := matrix.mul
local postfix `ᵀ` : 1500 := transpose

@[derive _root_.decidable_eq] inductive undo : Type
| unrestrict : ℕ → undo
| revive_col : ℕ → undo
| delete_row : ℕ → undo

instance : has_repr undo :=
⟨λ u, undo.cases_on u
  (λ n, "unrestrict " ++ repr n)
  (λ n, "revive_col " ++ repr n)
  (λ n, "delete_row " ++ repr n)⟩
#print list.length_pos_
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

lemma sol_set_eq_flat_inter : T.sol_set =
  T.flat ∩ { x | ∀ i, i ∈ T.restricted → 0 ≤ x i 0 }
    ∩ { x | ∀ j, j ∈ T.dead → x (T.to_partition.colg j) 0 = 0 } :=
by simp [flat, sol_set, tableau.sol_set, tableau.res_set, set.ext_iff]; tauto

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
  stableau m n × termination n :=
let s := T.to_tableau.simplex w obj T.feasible in
prod.mk
  { to_tableau := s.1,
    feasible := feasible_simplex,
    undo_stack := T.undo_stack }
  s.2

/- Transfer lemmas about `tableau.simplex` onto `stableau.simplex` -/
@[simp] lemma simplex_to_tableau (w : tableau m n → bool) (obj : fin m) (T : stableau m n) :
  (T.to_tableau.simplex w obj T.feasible).1 = (T.simplex w obj).1.to_tableau := rfl

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

@[simp] lemma restricted_simplex (T : stableau m n) (w : tableau m n → bool) (obj : fin m) :
  (T.simplex w obj).1.restricted = T.restricted :=
tableau.restricted_simplex _ _ _ _

@[simp] lemma dead_simplex (T : stableau m n) (w : tableau m n → bool) (obj : fin m) :
  (T.simplex w obj).1.dead = T.dead :=
tableau.dead_simplex _ _ _ _

@[simp] lemma undo_stack_simplex (T : stableau m n) (w : tableau m n → bool) (obj : fin m) :
  (T.simplex w obj).1.undo_stack = T.undo_stack := rfl

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

lemma termination_eq_unbounded_iff {T : stableau m n} {w : tableau m n → bool} {obj : fin m}
  (c : fin n) :
  ((T.simplex w obj).2 = unbounded c) ↔
  w (T.simplex w obj).1.to_tableau = tt ∧ is_unbounded_above T (T.to_partition.rowg obj)
  ∧ c ∈ pivot_col (T.simplex w obj).1.to_tableau obj :=
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
{ undo_stack := delete_row (m + n) :: T.undo_stack,
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
  {x : cvec (m + 1 + n)} : x ∈ (T.add_row fac k).flat → minor x fin.castp (λ x, x) ∈ T.flat :=
begin
  rw [mem_flat_iff, mem_flat_iff],
  intros h r,
  have := h (fin.cast_succ r),
  simp [add_row_rowg_cast_succ, add_row_const, add_row_to_matrix,
    (show (fin.cast_succ r).val < m, from r.2), add_row_colg] at this,
  simpa
end

lemma minor_mem_res_set_of_mem_add_row_res_set {T : stableau m n} {fac : rvec (m + n)} {k : ℚ}
  {x : cvec (m + 1 + n)} : x ∈ (T.add_row fac k).res_set → minor x fin.castp (λ x, x) ∈ T.res_set :=
and_implies minor_mem_flat_of_mem_add_row_flat begin
  assume h v,
  simp only [set.mem_set_of_eq, add_row_restricted, mem_image, exists_imp_distrib] at h,
  simpa [add_row_restricted, matrix.minor, id.def] using h (fin.castp v) v
end

lemma minor_mem_dead_set_of_mem_add_row_dead_set {T : stableau m n} {fac : rvec (m + n)} {k : ℚ}
  {x : cvec (m + 1 + n)} : x ∈ (T.add_row fac k).dead_set → minor x fin.castp (λ x, x) ∈ T.dead_set :=
and_implies minor_mem_flat_of_mem_add_row_flat $
  by simp only [add_row_colg, add_row_to_partition];
  exact id

lemma minor_mem_sol_set_of_mem_add_row_sol_set {T : stableau m n} {fac : rvec (m + n)} {k : ℚ}
  {x : cvec (m + 1 + n)} : x ∈ (T.add_row fac k).sol_set → minor x fin.castp (λ x, x) ∈ T.sol_set :=
by rw [sol_set_eq_res_set_inter_dead_set, sol_set_eq_res_set_inter_dead_set];
  exact and_implies minor_mem_res_set_of_mem_add_row_res_set
    minor_mem_dead_set_of_mem_add_row_dead_set

lemma sum_colg_eq_sum_fac {T : stableau m n} {fac : rvec (m + n)} {k : ℚ} {x : cvec (m + n)}
  (hx : x ∈ T.flat) : univ.sum (λ j : fin n, (T.add_row fac k).to_matrix (fin.last _) j *
    x (T.to_partition.colg j) 0) + (T.add_row fac k).const (fin.last _) 0 =
      univ.sum (λ v : fin (m + n), fac 0 v * x v 0) + k :=
calc univ.sum (λ j : fin n, (T.add_row fac k).to_matrix (fin.last _) j *
      x (T.to_partition.colg j) 0) + (T.add_row fac k).const (fin.last _) 0
    = k +
  univ.sum (λ j, (fac 0 (T.to_partition.colg j) * x (T.to_partition.colg j) 0)) +
  (univ.sum (λ j, univ.sum (λ i, fac 0 (T.to_partition.rowg i) * T.to_matrix i j *
      x (T.to_partition.colg j) 0))
    + univ.sum (λ i, fac 0 (T.to_partition.rowg i) * T.const i 0)) :
  by simp [add_row_to_matrix, add_row_const, fin.last, add_mul, sum_add_distrib, sum_mul]
... = k +
  univ.sum (λ j, (fac 0 (T.to_partition.colg j) * x (T.to_partition.colg j) 0)) +
  (univ.sum (λ i, univ.sum (λ j, fac 0 (T.to_partition.rowg i) * T.to_matrix i j *
    x (T.to_partition.colg j) 0))
    + univ.sum (λ i, fac 0 (T.to_partition.rowg i) * T.const i 0)) : by rw [sum_comm]
... = k +
  univ.sum (λ j, (fac 0 (T.to_partition.colg j) * x (T.to_partition.colg j) 0)) +
  univ.sum (λ i : fin m, (fac 0 (T.to_partition.rowg i) * x (T.to_partition.rowg i) 0)) :
begin
  rw [← sum_add_distrib],
  have : ∀ r : fin m, x (T.to_partition.rowg r) 0 =
    sum univ (λ (c : fin n), T.to_matrix r c * x (T.to_partition.colg c) 0) +
    T.const r 0, from mem_flat_iff.1 hx,
  simp [this, mul_add, add_row_colg, mul_sum, mul_assoc]
end
... = ((univ.image T.to_partition.colg).sum (λ v, (fac 0 v * x v 0)) +
  (univ.image T.to_partition.rowg).sum (λ v, (fac 0 v * x v 0))) + k :
  by rw [sum_image, sum_image];
    simp [add_row_rowg_cast_succ, add_row_colg, T.to_partition.injective_rowg.eq_iff,
      T.to_partition.injective_colg.eq_iff]
... = _ : begin
  rw [← sum_union],
  congr,
  simpa [finset.ext, eq_comm] using T.to_partition.eq_rowg_or_colg,
  { simp [finset.ext, eq_comm, T.to_partition.rowg_ne_colg] {contextual := tt} }
end

lemma add_row_new_eq_sum_fac {T : stableau m n} {fac : rvec (m + n)} {k : ℚ}
  {x : cvec (m + 1 + n)} (hx : x ∈ (T.add_row fac k).flat) :
  x fin.lastp 0 = univ.sum (λ v : fin (m + n), fac 0 v * x (fin.castp v) 0) + k :=
calc x fin.lastp 0 = x ((T.add_row fac k).to_partition.rowg (fin.last _)) 0 :
  by simp [add_row_rowg_last]
... = univ.sum (λ j : fin n, _) + (T.add_row fac k).const _ _ : mem_flat_iff.1 hx _
... = univ.sum (λ v : fin (m + n), fac 0 v * x (fin.castp v) 0) + k :
  by erw ← sum_colg_eq_sum_fac (minor_mem_flat_of_mem_add_row_flat hx);
  simp [minor, add_row_colg, id.def (0 : fin 1)]

lemma flat_add_row (T : stableau m n) (fac : rvec (m + n)) (k : ℚ) :
  (T.add_row fac k).flat = (λ x, minor x fin.castp (λ x, x)) ⁻¹' T.flat ∩
  {x : cvec (m + 1 + n) |
    x fin.lastp 0 = univ.sum (λ v : fin (m + n), fac 0 v * x (fin.castp v) 0) + k} :=
set.ext $ λ x, ⟨λ hx, ⟨minor_mem_flat_of_mem_add_row_flat hx, add_row_new_eq_sum_fac hx⟩,
  λ h, mem_flat_iff.2 (λ r, begin
    refine fin.cases_last _ _ r,
    { erw [add_row_to_partition, add_row_rowg_last, show _ = _, from h.2,
        ← sum_colg_eq_sum_fac h.1],
      simp [minor, add_row_colg] },
    { assume i,
      have := mem_flat_iff.1 h.1 i,
      simp [add_row_to_matrix, dif_pos (show i.cast_succ.val < m, from i.2),
        add_row_to_partition, add_row_rowg_cast_succ, minor, *, add_row_const, add_row_colg] at * }
  end)⟩

lemma res_set_add_row_aux (T : stableau m n) (fac : rvec (m + n)) (k : ℚ) :
  { x : cvec (m + 1 + n) | ∀ i, i ∈ (T.add_row fac k).restricted → 0 ≤ x i 0 } =
  (λ x, minor x fin.castp (λ x, x)) ⁻¹' { x | ∀ i, i ∈ T.restricted → 0 ≤ x i 0 } :=
set.ext $ λ x, ⟨λ h i hres, h _ (by simp [add_row_restricted, fin.injective_castp.eq_iff, *]),
  by simp [add_row_restricted, @eq_comm _ (fin.castp _), minor] {contextual := tt}⟩

lemma res_set_add_row (T : stableau m n) (fac : rvec (m + n)) (k : ℚ) :
  (T.add_row fac k).res_set = (λ x, minor x fin.castp (λ x, x)) ⁻¹' T.res_set ∩
  {x : cvec (m + 1 + n) |
    x fin.lastp 0 = univ.sum (λ v : fin (m + n), fac 0 v * x (fin.castp v) 0) + k} :=
by rw [res_set, res_set, tableau.res_set, tableau.res_set, ← flat, ← flat, flat_add_row,
    res_set_add_row_aux];
  finish [set.ext_iff]

lemma dead_set_add_row_aux (T : stableau m n) (fac : rvec (m + n)) (k : ℚ) :
  { x : cvec (m + 1 + n) | ∀ j, j ∈ (T.add_row fac k).dead →
    x ((T.add_row fac k).to_partition.colg j ) 0 = 0 } =
  (λ x, minor x fin.castp (λ x, x)) ⁻¹' { x | ∀ j, j ∈ T.dead →
    x (T.to_partition.colg j ) 0 = 0 } :=
by simp [add_row_dead, minor, add_row_colg, set.ext_iff]

lemma dead_set_add_row (T : stableau m n) (fac : rvec (m + n)) (k : ℚ) :
(T.add_row fac k).dead_set = (λ x, minor x fin.castp (λ x, x)) ⁻¹' T.dead_set ∩
  {x : cvec (m + 1 + n) |
    x fin.lastp 0 = univ.sum (λ v : fin (m + n), fac 0 v * x (fin.castp v) 0) + k} :=
by rw [dead_set, dead_set, tableau.dead_set, tableau.dead_set, ← flat, ← flat, flat_add_row,
    dead_set_add_row_aux];
  finish [set.ext_iff]

lemma sol_set_add_row (T : stableau m n) (fac : rvec (m + n)) (k : ℚ) :
  (T.add_row fac k).sol_set = (λ x, minor x fin.castp (λ x, x)) ⁻¹' T.sol_set ∩
  {x : cvec (m + 1 + n) |
    x fin.lastp 0 = univ.sum (λ v : fin (m + n), fac 0 v * x (fin.castp v) 0) + k} :=
by rw [sol_set_eq_res_set_inter_dead_set, sol_set_eq_res_set_inter_dead_set,
    dead_set_add_row, res_set_add_row];
  simp [set.ext_iff]; tauto

lemma image_flat_add_row (T : stableau m n) (fac : rvec (m + n)) (k : ℚ) :
  (λ x, minor x fin.castp (λ x, x)) '' (T.add_row fac k).flat = T.flat :=
begin
  simp only [flat_add_row, set.ext_iff, minor, mem_flat_iff, set.mem_preimage, set.mem_image,
    set.mem_inter_eq, add_comm, set.mem_set_of_eq],
  assume x,
  split,
  { rintros ⟨y, ⟨hy, _⟩, hyx⟩,
    subst hyx, exact hy },
  { assume h,
    refine ⟨λ i j, if hi : i.1 < m + n then x ⟨i.1, hi⟩ j
      else k + univ.sum (λ v, fac 0 v * x v 0), _⟩,
    dsimp [fin.castp, fin.lastp],
    simp [fin.is_lt, h, lt_irrefl] }
end

lemma image_sol_set_add_row (T : stableau m n) (fac : rvec (m + n)) (k : ℚ) :
  (λ x, minor x fin.castp (λ x, x)) '' (T.add_row fac k).sol_set = T.sol_set :=
begin
  conv_rhs {rw [sol_set_eq_flat_inter, ← image_flat_add_row T fac k]},
  rw [sol_set_eq_flat_inter, dead_set_add_row_aux, res_set_add_row_aux],
  ext x,
  split,
  { rintros ⟨y, hy, ⟨_⟩⟩,
    exact ⟨⟨⟨y, hy.1.1, rfl⟩, hy.1.2⟩, hy.2⟩ },
  { rintros ⟨⟨⟨y, hy, ⟨_⟩⟩, hx₁⟩, hx₂⟩,
    exact ⟨y, ⟨⟨⟨hy, hx₁⟩, hx₂⟩, rfl⟩⟩ }
end

end add_row

section sign_of_max_row

lemma sign_of_max_row_feasible {T : tableau m n} (obj : fin m) (hT : T.feasible) (c : fin n)
  (hc : (T.simplex (λ T', T'.const obj 0 ≤ 0) obj hT).2 = unbounded c) :
  ((T.simplex (λ T', T'.const obj 0 ≤ 0) obj hT).1.pivot obj c).feasible :=
by rw [tableau.termination_eq_unbounded_iff_pivot_row_eq_none] at hc; exact
feasible_pivot_obj_of_nonpos (feasible_simplex)
  (λ hcres, by have := pivot_col_spec hc.2.1; simp * at *)
  (pivot_row_eq_none_aux hc.2.2 hc.2.1)
  (by finish)

set_option eqn_compiler.zeta true

def sign_of_max_row (T : stableau m n) (obj : fin m) : stableau m n × ℤ :=
let T' := T.simplex (λ T', T'.const obj 0 ≤ 0) obj in
match T'.2, sign_of_max_row_feasible obj T.feasible with
| while,       _  := (T'.1, 1)
| unbounded c, hc :=
  ({to_tableau := T'.1.to_tableau.pivot obj c,
    undo_stack := T.undo_stack,
    feasible := hc _ rfl }, 1)
| optimal,     _  := (T'.1, if T'.1.const obj 0 = 0 then 0 else -1)
end

set_option eqn_compiler.zeta false

lemma optimal_and_neg_of_sign_of_max_row_eq_zero {T : stableau m n} {obj : fin m} :
  (sign_of_max_row T obj).2 = 0 →
  let T' := T.simplex (λ T', T'.const obj 0 ≤ 0) obj in
  T'.2 = optimal ∧
  ∀ c : fin n, c ∉ T'.1.dead →
  (((sign_of_max_row T obj).1.to_matrix obj c = 0 ∧
      (sign_of_max_row T obj).1.to_partition.colg c ∉ (sign_of_max_row T obj).1.restricted)
    ∨ ((sign_of_max_row T obj).1.to_matrix obj c ≤ 0 ∧
      (sign_of_max_row T obj).1.to_partition.colg c ∈ (sign_of_max_row T obj).1.restricted)) :=
let T' := T.simplex (λ T', T'.const obj 0 ≤ 0) obj in
begin
  cases h : T'.2 with c,
  { simp [sign_of_max_row, *, termination_eq_while_iff, is_optimal_iff, classical.not_forall] at * },
  { simp [sign_of_max_row, *] },
  { simp only [sign_of_max_row, *, eq_self_iff_true, true_and],
    split_ifs,
    { simp only [eq_self_iff_true, true_implies_iff],
      assume c hc,
      exact (pivot_col_eq_none_aux feasible_simplex
        (termination_eq_optimal_iff_pivot_col_eq_none.1 h).2
          (show c ∉ T'.1.dead, by simpa using hc)) },
    { simp [show (-1 : ℤ) ≠ 0, from dec_trivial], } }
end

lemma sign_of_max_row_eq_zero {T : stableau m n} {obj : fin m} :
  (sign_of_max_row T obj).2 = 0 ↔
    ∃ x : cvec (m + n), x (T.to_partition.rowg obj) 0 = 0 ∧ is_optimal T x
      (T.to_partition.rowg obj) :=
let T' := T.simplex (λ T', T'.const obj 0 ≤ 0) obj in
begin
  cases h : T'.2 with c,
  { simp only [sign_of_max_row, *, termination_eq_while_iff, is_optimal_iff, classical.not_forall,
      not_exists, exists_prop, false_iff, not_and, not_le, to_bool_ff_iff, one_ne_zero] at *,
    assume x hx0 hxs,
    refine ⟨T'.1.of_col 0, _⟩,
    simpa [T', hx0] },
  { simp only [sign_of_max_row, *, termination_eq_unbounded_iff, is_unbounded_above,
      classical.not_forall, not_exists, exists_prop, false_iff, not_and, not_le, to_bool_iff,
      one_ne_zero, is_optimal_iff] at * {contextual := tt},
    cases h.2.1 1 with y hy,
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
    cases h.2.1 1 with y hy,
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
    cases h.2.1 1 with y hy,
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

lemma sign_of_max_row_eq_simplex_or_pivot (T : stableau m n) (obj : fin m) :
  (sign_of_max_row T obj).1 = (T.simplex (λ T', T'.const obj 0 ≤ 0) obj).1 ∨
  ∃ c, c ∈ pivot_col (T.simplex (λ T', T'.const obj 0 ≤ 0) obj).1.to_tableau obj ∧
    (sign_of_max_row T obj).1.to_tableau =
      (T.simplex (λ T', T'.const obj 0 ≤ 0) obj).1.to_tableau.pivot obj c :=
let T' := T.simplex (λ T', T'.const obj 0 ≤ 0) obj in
begin
  cases h : T'.2 with c,
  { simp [sign_of_max_row, h] },
  { right, use c,
    simp [sign_of_max_row, h, ((termination_eq_unbounded_iff _).1 h).2] },
  { simp [sign_of_max_row, h] }
end

@[simp] lemma sign_of_max_row_flat (T : stableau m n) (obj : fin m) :
  (sign_of_max_row T obj).1.flat = T.flat :=
(sign_of_max_row_eq_simplex_or_pivot T obj).elim
  (by simp { contextual := tt })
  (λ ⟨c, hc⟩, begin
    rw [flat, hc.2, simplex, ← flat_simplex T (λ T', T'.const obj 0 ≤ 0) obj],
    exact tableau.flat_pivot (ne_zero_of_mem_pivot_col hc.1)
  end)

@[simp] lemma sign_of_max_row_res_set (T : stableau m n) (obj : fin m) :
  (sign_of_max_row T obj).1.res_set = T.res_set :=
(sign_of_max_row_eq_simplex_or_pivot T obj).elim
  (by simp { contextual := tt })
  (λ ⟨c, hc⟩, begin
    rw [res_set, hc.2, simplex, ← res_set_simplex T (λ T', T'.const obj 0 ≤ 0) obj],
    exact tableau.res_set_pivot (ne_zero_of_mem_pivot_col hc.1)
  end)

@[simp] lemma sign_of_max_row_dead_set (T : stableau m n) (obj : fin m) :
  (sign_of_max_row T obj).1.dead_set = T.dead_set :=
(sign_of_max_row_eq_simplex_or_pivot T obj).elim
  (by simp { contextual := tt })
  (λ ⟨c, hc⟩, begin
    rw [dead_set, hc.2, simplex, ← dead_set_simplex T (λ T', T'.const obj 0 ≤ 0) obj],
    exact tableau.dead_set_pivot (ne_zero_of_mem_pivot_col hc.1) (pivot_col_spec hc.1).2
  end)

@[simp] lemma sign_of_max_row_sol_set (T : stableau m n) (obj : fin m) :
  (sign_of_max_row T obj).1.sol_set = T.sol_set :=
by simp [sol_set_eq_res_set_inter_dead_set]

@[simp] lemma restricted_sign_of_max_row (T : stableau m n) (obj : fin m) :
  (sign_of_max_row T obj).1.restricted = T.restricted :=
(sign_of_max_row_eq_simplex_or_pivot T obj).elim
  (by simp { contextual := tt })
  (by simp { contextual := tt })

@[simp] lemma dead_sign_of_max_row (T : stableau m n) (obj : fin m) :
  (sign_of_max_row T obj).1.dead = T.dead :=
(sign_of_max_row_eq_simplex_or_pivot T obj).elim
  (by simp { contextual := tt })
  (by simp { contextual := tt })

@[simp] lemma undo_stack_sign_of_max_row (T : stableau m n) (obj : fin m) :
  (sign_of_max_row T obj).1.undo_stack = T.undo_stack :=
let T' := T.simplex (λ T', T'.const obj 0 ≤ 0) obj in
by dsimp [sign_of_max_row]; cases h : T'.2; simp [h, sign_of_max_row._match_1]

lemma feasible_restrict_sign_of_max_row (T : stableau m n) (obj : fin m)
  (h0 : 0 ≤ (T.sign_of_max_row obj).2) :
  ((T.sign_of_max_row obj).1.to_tableau.restrict (T.to_partition.rowg obj)).feasible :=
let T' := T.simplex (λ T', T'.const obj 0 ≤ 0) obj in
tableau.feasible_restrict (T.sign_of_max_row obj).1.feasible $
  let T' := T.simplex (λ T', T'.const obj 0 ≤ 0) obj in
  begin
    cases h : T'.2,
    { refine or.inr ⟨obj, _⟩,
      simp [sign_of_max_row, h],
      exact le_of_not_ge (by simpa using termination_eq_while_iff.1 h) },
    { refine or.inl ⟨c, _⟩,
      simp [sign_of_max_row, h] },
    { refine or.inr ⟨obj, _⟩,
      simp [sign_of_max_row, h] at *,
      split_ifs at h0; simp [*, show ¬ (1 : ℤ) ≤ 0, from dec_trivial] at * }
  end

lemma rowg_sign_of_max_row_of_le_zero {T : stableau m n} {obj : fin m}
  (h1 : (T.sign_of_max_row obj).2 ≤ 0) :
  (T.sign_of_max_row obj).1.to_partition.rowg obj = T.to_partition.rowg obj :=
let T' := T.simplex (λ T', T'.const obj 0 ≤ 0) obj in
by cases h : T'.2; simp [sign_of_max_row, *, show ¬ (1 : ℤ) ≤ 0, from dec_trivial] at *

lemma const_sign_of_max_row_eq_zero_of_eq_zero {T : stableau m n} {obj : fin m}
  (h : (T.sign_of_max_row obj).2 = 0) : (T.sign_of_max_row obj).1.const obj 0 = 0 :=
let T' := T.simplex (λ T', T'.const obj 0 ≤ 0) obj in
by cases h : T'.2; simp [sign_of_max_row, *] at *; split_ifs at *; simp * at *

end sign_of_max_row

section to_row

def to_row_pivot_row (T : stableau m n) (c : fin n) : option (fin m) :=
((list.fin_range m).filter (λ r, (T.to_partition.rowg r ∈ T.restricted ∧
  T.to_matrix r c < 0))).argmax (λ r, T.const r 0 / T.to_matrix r c)

lemma feasible_to_row_pivot_row {T : stableau m n} (c : fin n) (r)
  (hr : r ∈ to_row_pivot_row T c) : (T.to_tableau.pivot r c).feasible :=
begin
  unfold to_row_pivot_row at hr,
  simp only [to_row_pivot_row, list.mem_argmax_iff, list.mem_filter] at hr,
  refine feasible_pivot T.feasible (by tauto) (by tauto) _,
  assume i hir hir0,
  have hic0 : T.to_matrix i c < 0,
    from neg_of_mul_pos_left hir0 (inv_nonpos.2 $ le_of_lt $ by tauto),
  rw [abs_of_nonpos (div_nonpos_of_nonneg_of_neg (T.feasible _ hir) hic0),
    abs_of_nonpos (div_nonpos_of_nonneg_of_neg (T.feasible r (by tauto)) hr.1.2.2), neg_le_neg_iff],
  apply hr.2.1,
  simp,
  tauto
end

/-- pivot a row into a column. makes no sense given a dead column -/
def to_row (T : stableau m n) (c : fin n) : stableau m n × option (fin m) :=
match to_row_pivot_row T c, feasible_to_row_pivot_row c with
| none, h := (T, none)
| some r, h :=
  ({ feasible := h _ rfl,
     undo_stack := T.undo_stack,
     ..T.to_tableau.pivot r c },
  some r)
end

@[simp] lemma to_row_snd_eq_to_row_pivot_row (T : stableau m n) (c : fin n) :
  (T.to_row c).2 = to_row_pivot_row T c :=
begin
  dsimp [to_row],
  cases h : to_row_pivot_row T c; simp [*, h, to_row._match_1]
end

lemma to_row_eq_none_iff_eq_self {T : stableau m n} {c : fin n} : (T.to_row c).2 = none ↔
  (T.to_row c).1 = T :=
begin
  dsimp [to_row],
  cases h : to_row_pivot_row T c,
  { simp [h, to_row._match_1] },
  { simp [h, to_row._match_1],
    dsimp [to_row_pivot_row] at h,
    cases T with T hT, cases T,
    simp }
end

lemma to_row_eq_none {T : stableau m n} {c : fin n} (hdead : c ∉ T.dead): (T.to_row c).2 = none →
  (is_unbounded_above T (T.to_partition.colg c)) :=
begin
  dsimp [to_row],
  cases h : to_row_pivot_row T c,
  { simp only [h, to_row._match_1],
    dsimp [to_row_pivot_row] at h,
    simp only [true_and, forall_prop_of_true, eq_self_iff_true],
    exact is_unbounded_above_colg T.feasible hdead (by simpa [list.filter_eq_nil] using h) },
  { simp [h, to_row._match_1] }
end

lemma to_row_eq_pivot_of_mem {T : stableau m n} {r : fin m} {c : fin n} (hr : r ∈ (T.to_row c).2) :
  (T.to_row c).1.to_tableau = T.to_tableau.pivot r c :=
begin
  dsimp [to_row] at *,
  cases h : to_row_pivot_row T c;
  simp only [*, to_row._match_1, tableau.eta, option.not_mem_none, option.mem_def,
    option.some_inj] at *
end

lemma ne_zero_of_mem_to_row {T : stableau m n} {r : fin m} {c : fin n} (hr : r ∈ (T.to_row c).2) :
  T.to_matrix r c ≠ 0 :=
λ h0, by simpa [list.argmax_eq_some_iff, h0, lt_irrefl, to_row_snd_eq_to_row_pivot_row,
  to_row_pivot_row] using hr

lemma colg_to_row_eq_of_mem {T : stableau m n} {r : fin m} {c : fin n} (hr : r ∈ (T.to_row c).2) :
  (T.to_row c).1.to_partition.colg c = T.to_partition.rowg r :=
by rw [to_row_eq_pivot_of_mem hr, to_partition_pivot, colg_swap]

lemma rowg_to_row_eq_of_mem {T : stableau m n} {r : fin m} {c : fin n} (hr : r ∈ (T.to_row c).2) :
  (T.to_row c).1.to_partition.rowg r = T.to_partition.colg c :=
by rw [to_row_eq_pivot_of_mem hr, to_partition_pivot, rowg_swap]

lemma to_row_eq_self_or_pivot (T : stableau m n) (c : fin n) :
  (T.to_row c).1 = T ∨ ∃ r, T.to_matrix r c ≠ 0 ∧
  (T.to_row c).1.to_tableau = T.to_tableau.pivot r c :=
begin
  cases h : (T.to_row c).2 with r,
  { exact or.inl (to_row_eq_none_iff_eq_self.1 h) },
  { exact or.inr ⟨r, ne_zero_of_mem_to_row h, (to_row_eq_pivot_of_mem h)⟩ }
end

@[simp] lemma flat_to_row (T : stableau m n) (c : fin n) : (T.to_row c).1.flat = T.flat :=
(to_row_eq_self_or_pivot T c).elim (congr_arg _)
  (λ ⟨r, hr0, hr⟩, by rw [flat, hr]; exact flat_pivot hr0)

@[simp] lemma res_set_to_row (T : stableau m n) (c : fin n) : (T.to_row c).1.res_set = T.res_set :=
(to_row_eq_self_or_pivot T c).elim (congr_arg _)
  (λ ⟨r, hr0, hr⟩, by rw [res_set, hr]; exact res_set_pivot hr0)

@[simp] lemma dead_set_to_row (T : stableau m n) (c : fin n) (hdead : c ∉ T.dead):
  (T.to_row c).1.dead_set = T.dead_set :=
(to_row_eq_self_or_pivot T c).elim (congr_arg _)
  (λ ⟨r, hr0, hr⟩, by rw [dead_set, hr]; exact dead_set_pivot hr0 hdead)

@[simp] lemma sol_set_to_row (T : stableau m n) (c : fin n) (hdead : c ∉ T.dead) :
  (T.to_row c).1.sol_set = T.sol_set :=
by simp [sol_set_eq_res_set_inter_dead_set, dead_set_to_row T c hdead]

@[simp] lemma undo_stack_to_row (T : stableau m n) (c : fin n) :
  (T.to_row c).1.undo_stack = T.undo_stack :=
by dsimp [to_row]; cases h : T.to_row_pivot_row c; simp [h, to_row._match_1]

@[simp] lemma dead_to_row (T : stableau m n) (c : fin n) : (T.to_row c).1.dead = T.dead :=
(to_row_eq_self_or_pivot T c).elim (λ h, by rw h) (λ ⟨r, _, hr⟩, hr.symm ▸ rfl)

@[simp] lemma restricted_to_row (T : stableau m n) (c : fin n) :
  (T.to_row c).1.restricted = T.restricted :=
(to_row_eq_self_or_pivot T c).elim (λ h, by rw h) (λ ⟨r, _, hr⟩, hr.symm ▸ rfl)

end to_row

section sign_of_max

def sign_of_max (T : stableau m n) (v : fin (m + n)) : stableau m n × ℤ :=
row_col_cases_on T.to_partition v (sign_of_max_row T)
  (λ c, if c ∈ T.dead then (T, 0)
    else let (T', r) := T.to_row c in
      option.cases_on r (T', 1) (sign_of_max_row T'))

lemma sign_of_max_rowg (T : stableau m n) (r : fin m) :
  sign_of_max T (T.to_partition.rowg r) = sign_of_max_row T r :=
by simp [sign_of_max]

lemma sign_of_max_colg_of_dead (T : stableau m n) (c : fin n) (hdead : c ∈ T.dead) :
  sign_of_max T (T.to_partition.colg c) = (T, 0) :=
by simp [sign_of_max, hdead]

lemma sign_of_max_colg_of_not_dead (T : stableau m n) (c : fin n) (hdead : c ∉ T.dead) :
  sign_of_max T (T.to_partition.colg c) = option.cases_on (T.to_row c).2 ((T.to_row c).1, 1)
  (sign_of_max_row (T.to_row c).1) :=
by simp [sign_of_max, hdead]; cases (T.to_row c); refl

lemma sign_of_max_eq_zero {T : stableau m n} {v : fin (m + n)} :
  (sign_of_max T v).2 = 0 ↔ ∃ x : cvec (m + n), x v 0 = 0 ∧ is_optimal T x v :=
(eq_rowg_or_colg T.to_partition v).elim
  (λ ⟨r, hr⟩, by simp [sign_of_max_rowg, hr, sign_of_max_row_eq_zero])
  (λ ⟨c, hc⟩, if hdead : c ∈ T.dead
    then by simp only [sign_of_max_colg_of_dead T c hdead, hc, eq_self_iff_true, true_iff];
      exact ⟨T.of_col 0, by simp [of_col], by simp, λ y hy, by simp [hy.2 c hdead, of_col]⟩
    else begin
      simp only [hc, sign_of_max_colg_of_not_dead _ _ hdead],
      cases h : (T.to_row c).2 with r,
      { simp only [h, not_exists, false_iff, not_and, one_ne_zero],
        exact λ _ _, not_optimal_of_unbounded_above (to_row_eq_none hdead h) },
      { simp [sign_of_max_row_eq_zero, to_row_eq_pivot_of_mem h, is_optimal, tableau.is_optimal,
          sol_set_pivot (ne_zero_of_mem_to_row h) hdead] }
    end)

lemma sign_of_max_eq_one {T : stableau m n} {v : fin (m + n)} :
  (sign_of_max T v).2 = 1 ↔ ∃ x : cvec (m + n), x ∈ sol_set T ∧ 0 < x v 0 :=
(eq_rowg_or_colg T.to_partition v).elim
  (λ ⟨r, hr⟩, by simp [sign_of_max_rowg, hr, sign_of_max_row_eq_one])
  (λ ⟨c, hc⟩, if hdead : c ∈ T.dead
    then by simp only [sign_of_max_colg_of_dead T c hdead, hc, zero_ne_one, false_iff,
        not_exists, not_and, not_lt];
      exact λ x hx, by rw [hx.2 _ hdead]
    else begin
      simp only [hc, sign_of_max_colg_of_not_dead _ _ hdead],
      cases h : (T.to_row c).2 with r,
      { cases to_row_eq_none hdead h 1 with x hx,
        simp only [hc, true_iff, eq_self_iff_true],
        use [x, hx.1],
        exact lt_of_lt_of_le zero_lt_one hx.2 },
      { simp [h, sign_of_max_row_eq_one, rowg_to_row_eq_of_mem h, sol_set_to_row _ _ hdead] }
    end)

lemma sign_of_max_eq_neg_one {T : stableau m n} {v : fin (m + n)} :
  (sign_of_max T v).2 = -1 ↔ ∀ x : cvec (m + n), x ∈ sol_set T → x v 0 < 0 :=
(eq_rowg_or_colg T.to_partition v).elim
  (λ ⟨r, hr⟩, by simp [sign_of_max_rowg, hr, sign_of_max_row_eq_neg_one])
  (λ ⟨c, hc⟩, if hdead : c ∈ T.dead
    then by simp only [hc, sign_of_max_colg_of_dead _ _ hdead, eq_neg_iff_add_eq_zero,
        classical.not_forall,exists_prop, not_lt,zero_add, one_ne_zero, false_iff];
      exact ⟨T.of_col 0, by simp [of_col]⟩
    else begin
      simp only [hc, sign_of_max_colg_of_not_dead T c hdead],
      cases h : (T.to_row c).2 with r,
      { simpa [sol_set, hc, false_iff, show (1 : ℤ) ≠ -1, by norm_num,
          classical.not_forall, not_lt, exists_prop] using to_row_eq_none hdead h 0 },
      { simp [h, sign_of_max_row_eq_neg_one, rowg_to_row_eq_of_mem h, sol_set_to_row _ _ hdead] }
    end)

lemma feasible_restrict_sign_of_max {T : stableau m n} {v : fin (m + n)}
  (h0 : 0 ≤ (sign_of_max T v).2) : ((T.sign_of_max v).1.to_tableau.restrict v).feasible :=
(eq_rowg_or_colg T.to_partition v).elim
  (λ ⟨r, hr⟩, by rw [hr, sign_of_max_rowg] at ⊢ h0;
    exact feasible_restrict_sign_of_max_row _ _ h0)
  (λ ⟨c, hc⟩, if hdead : c ∈ T.dead
    then by rw [hc, sign_of_max_colg_of_dead _ _ hdead] at ⊢ h0;
      exact tableau.feasible_restrict T.feasible (or.inl ⟨c, rfl⟩)
    else begin
      rw [hc, sign_of_max_colg_of_not_dead _ _ hdead] at ⊢ h0,
      cases h : (T.to_row c).2 with r,
      { exact tableau.feasible_restrict (stableau.feasible _)
          (or.inl ⟨c, by simp [to_row_eq_none_iff_eq_self.1 h]⟩) },
      { have : T.to_partition.colg c = (T.to_row c).1.to_partition.rowg r,
        { simp [to_row_eq_pivot_of_mem h] },
        rw this,
        exact feasible_restrict_sign_of_max_row _ _ (by rwa h at h0) }
    end)

@[simp] lemma restricted_sign_of_max (T : stableau m n) (v : fin (m + n)) :
  (T.sign_of_max v).1.restricted = T.restricted :=
(eq_rowg_or_colg T.to_partition v).elim
  (λ ⟨r, hr⟩, by simp [sign_of_max_rowg, hr, sign_of_max_row_eq_zero])
  (λ ⟨c, hc⟩, if hdead : c ∈ T.dead
    then by simp [sign_of_max_colg_of_dead T c hdead, hc, eq_self_iff_true, true_iff]
    else begin
      simp only [hc, sign_of_max_colg_of_not_dead _ _ hdead],
      cases h : (T.to_row c).2 with r,
      { simp [h, not_exists, false_iff, not_and, one_ne_zero] },
      { simp [sign_of_max_row_eq_zero, to_row_eq_pivot_of_mem h, is_optimal, tableau.is_optimal,
          sol_set_pivot (ne_zero_of_mem_to_row h) hdead] }
    end)

@[simp] lemma dead_sign_of_max (T : stableau m n) (v : fin (m + n)) :
  (T.sign_of_max v).1.dead = T.dead :=
(eq_rowg_or_colg T.to_partition v).elim
  (λ ⟨r, hr⟩, by simp [sign_of_max_rowg, hr, sign_of_max_row_eq_zero])
  (λ ⟨c, hc⟩, if hdead : c ∈ T.dead
    then by simp [sign_of_max_colg_of_dead T c hdead, hc, eq_self_iff_true, true_iff]
    else begin
      simp only [hc, sign_of_max_colg_of_not_dead _ _ hdead],
      cases h : (T.to_row c).2 with r,
      { simp [h, not_exists, false_iff, not_and, one_ne_zero] },
      { simp [sign_of_max_row_eq_zero, to_row_eq_pivot_of_mem h, is_optimal, tableau.is_optimal,
          sol_set_pivot (ne_zero_of_mem_to_row h) hdead] }
    end)

@[simp] lemma undo_stack_sign_of_max (T : stableau m n) (v : fin (m + n)) :
  (T.sign_of_max v).1.undo_stack = T.undo_stack :=
(eq_rowg_or_colg T.to_partition v).elim
  (λ ⟨r, hr⟩, by simp [sign_of_max_rowg, hr, sign_of_max_row_eq_zero])
  (λ ⟨c, hc⟩, if hdead : c ∈ T.dead
    then by simp [sign_of_max_colg_of_dead T c hdead, hc, eq_self_iff_true, true_iff]
    else begin
      simp only [hc, sign_of_max_colg_of_not_dead _ _ hdead],
      cases h : (T.to_row c).2 with r,
      { simp [h, not_exists, false_iff, not_and, one_ne_zero] },
      { simp [sign_of_max_row_eq_zero, to_row_eq_pivot_of_mem h, is_optimal, tableau.is_optimal,
          sol_set_pivot (ne_zero_of_mem_to_row h) hdead] }
    end)

@[simp] lemma flat_sign_of_max (T : stableau m n) (v : fin (m + n)) :
  (T.sign_of_max v).1.flat = T.flat :=
(eq_rowg_or_colg T.to_partition v).elim
  (λ ⟨r, hr⟩, by simp [sign_of_max_rowg, hr, sign_of_max_row_eq_zero])
  (λ ⟨c, hc⟩, if hdead : c ∈ T.dead
    then by simp [sign_of_max_colg_of_dead T c hdead, hc, eq_self_iff_true, true_iff]
    else begin
      simp only [hc, sign_of_max_colg_of_not_dead _ _ hdead],
      cases h : (T.to_row c).2 with r,
      { simp [h, not_exists, false_iff, not_and, one_ne_zero] },
      { simp [sign_of_max_row_eq_zero, to_row_eq_pivot_of_mem h, is_optimal, tableau.is_optimal,
          sol_set_pivot (ne_zero_of_mem_to_row h) hdead] }
    end)

@[simp] lemma dead_set_sign_of_max (T : stableau m n) (v : fin (m + n)) :
  (T.sign_of_max v).1.dead_set = T.dead_set :=
(eq_rowg_or_colg T.to_partition v).elim
  (λ ⟨r, hr⟩, by simp [sign_of_max_rowg, hr, sign_of_max_row_eq_zero])
  (λ ⟨c, hc⟩, if hdead : c ∈ T.dead
    then by simp [sign_of_max_colg_of_dead T c hdead, hc, eq_self_iff_true, true_iff]
    else begin
      simp only [hc, sign_of_max_colg_of_not_dead _ _ hdead],
      cases h : (T.to_row c).2 with r; simp [h, dead_set_to_row _ _ hdead]
    end)

@[simp] lemma res_set_sign_of_max (T : stableau m n) (v : fin (m + n)) :
  (T.sign_of_max v).1.res_set = T.res_set :=
(eq_rowg_or_colg T.to_partition v).elim
  (λ ⟨r, hr⟩, by simp [sign_of_max_rowg, hr, sign_of_max_row_eq_zero])
  (λ ⟨c, hc⟩, if hdead : c ∈ T.dead
    then by simp [sign_of_max_colg_of_dead T c hdead, hc, eq_self_iff_true, true_iff]
    else begin
      simp only [hc, sign_of_max_colg_of_not_dead _ _ hdead],
      cases h : (T.to_row c).2 with r; simp [h, dead_set_to_row _ _ hdead]
    end)

@[simp] lemma sol_set_sign_of_max (T : stableau m n) (v : fin (m + n)) :
  (T.sign_of_max v).1.sol_set = T.sol_set :=
(eq_rowg_or_colg T.to_partition v).elim
  (λ ⟨r, hr⟩, by simp [sign_of_max_rowg, hr, sign_of_max_row_eq_zero])
  (λ ⟨c, hc⟩, if hdead : c ∈ T.dead
    then by simp [sign_of_max_colg_of_dead T c hdead, hc, eq_self_iff_true, true_iff]
    else begin
      simp only [hc, sign_of_max_colg_of_not_dead _ _ hdead],
      cases h : (T.to_row c).2 with r; simp [h, sol_set_to_row _ _ hdead]
    end)

end sign_of_max

-- section kill_col

-- variable (T : stableau m n)

-- def kill_col (c : fin n) : stableau m n :=
-- { to_tableau := T.to_tableau.kill_col c,
--   undo_stack := revive_col c.1 :: T.undo_stack,
--   feasible   := T.feasible }

-- @[simp] lemma to_matrix_kill_col (c : fin n) :
--   (T.kill_col c).to_matrix = T.to_matrix := rfl

-- @[simp] lemma const_kill_col (c : fin n) : (T.kill_col c).const = T.const := rfl

-- @[simp] lemma to_partition_kill_col (c : fin n) :
--   (T.kill_col c).to_partition = T.to_partition := rfl

-- @[simp] lemma dead_kill_col (c : fin n) : (T.kill_col c).dead = insert c T.dead := rfl

-- @[simp] lemma restricted_kill_col (c : fin n) :
--   (T.kill_col c).restricted = T.restricted := rfl

-- @[simp] lemma flat_kill_col (c : fin n) : (T.kill_col c).flat = T.flat :=
-- tableau.flat_kill_col _

-- @[simp] lemma res_set_kill_col (c : fin n) : (T.kill_col c).res_set = T.res_set :=
-- tableau.res_set_kill_col _

-- @[simp] lemma dead_set_kill_col (c : fin n) : (T.kill_col c).dead_set =
--   T.dead_set ∩ {x | x (T.to_partition.colg c) 0 = 0} :=
-- tableau.dead_set_kill_col _

-- lemma sol_set_kill_col (c : fin n) : (T.kill_col c).sol_set =
--   T.sol_set ∩ {x | x (T.to_partition.colg c) 0 = 0} :=
-- tableau.sol_set_kill_col _

-- end kill_col

section restrict

def restrict (T : stableau m n) (v : fin (m + n)) (h : (T.to_tableau.restrict v).feasible) :
  stableau m n :=
{ to_tableau := T.to_tableau.restrict v,
  feasible := h,
  undo_stack := unrestrict v.1 :: T.undo_stack }

end restrict

section close_row

/-- Only to be used immediately after `sign_of_max_row` -/
def close_row (T : stableau m n) (r : fin m) : stableau m n :=
let s : list (fin n) := (list.fin_range n).filter (λ c, T.to_matrix r c < 0) in
{ dead := T.dead ∪ ⟨s, list.nodup_filter _ (list.nodup_fin_range _)⟩,
  undo_stack := s.map (λ c, revive_col c.val) ++ T.undo_stack,
  ..T }

@[simp] lemma to_matrix_close_row (T : stableau m n) (r : fin m) :
  (T.close_row r).to_matrix = T.to_matrix := rfl

@[simp] lemma const_close_row (T : stableau m n) (r : fin m) :
  (T.close_row r).const = T.const := rfl

@[simp] lemma to_partition_close_row (T : stableau m n) (r : fin m) :
  (T.close_row r).to_partition = T.to_partition := rfl

@[simp] lemma restricted_close_row (T : stableau m n) (r : fin m) :
  (T.close_row r).restricted = T.restricted := rfl

lemma dead_close_row (T : stableau m n) (r : fin m) :
  (T.close_row r).dead = T.dead ∪ univ.filter (λ c, T.to_matrix r c < 0) :=
by simp [finset.ext, close_row]

lemma undo_stack_close_row (T : stableau m n) (r : fin m) :
  (T.close_row r).undo_stack = ((list.fin_range n).filter (λ c, T.to_matrix r c < 0)).map
    (λ c, revive_col c.val) ++ T.undo_stack := rfl

@[simp] lemma flat_close_row (T : stableau m n) (r : fin m) :
  (T.close_row r).flat = T.flat := rfl

@[simp] lemma res_set_close_row (T : stableau m n) (r : fin m) :
  (T.close_row r).res_set = T.res_set := rfl

lemma sol_set_close_row_subset (T : stableau m n) (r : fin m) :
  (T.close_row r).sol_set ⊆ T.sol_set :=
λ _, by simp [sol_set, tableau.sol_set, tableau.res_set, close_row, tableau.flat] {contextual := tt}

lemma sol_set_close_row_sign_of_max_row (T : stableau m n) (r : fin m)
  (hres : (T.sign_of_max_row r).1.to_partition.rowg r ∈ T.restricted)
  (h0 : (T.sign_of_max_row r).2 = 0) :
  ((T.sign_of_max_row r).1.close_row r).sol_set = T.sol_set :=
have hsub : ((T.sign_of_max_row r).1.close_row r).sol_set ⊆ T.sol_set,
  by simpa using sol_set_close_row_subset (sign_of_max_row T r).1 r,
set.subset.antisymm hsub
  (λ x hx, begin
    rw [← sign_of_max_row_sol_set _ r] at hx,
    refine ⟨hx.1, λ c hc, _⟩,
    rw [dead_close_row, finset.mem_union, finset.mem_filter] at hc,
    cases hc with hc hc,
    { simpa using hx.2 _ hc },
    { cases sign_of_max_row_eq_zero.1 h0 with y hy,
      { have hx0 : x ((sign_of_max_row T r).fst.to_partition.rowg r) 0 = 0,
          from le_antisymm (le_trans begin
            rw [rowg_sign_of_max_row_of_le_zero],
            exact hy.2.2 x (by simpa using hx),
            simp * at *
          end
            (le_of_eq hy.1))
          (hx.1.2 _ (by simpa using hres)),
        have hc'0 : ∀ c', (sign_of_max_row T r).fst.to_matrix r c' *
          x ((sign_of_max_row T r).fst.to_partition.colg c') 0 ≤ 0,
        { assume c',
          by_cases hdead : c' ∈ T.dead,
          { have := hx.2 c', simp * at * },
          { cases (optimal_and_neg_of_sign_of_max_row_eq_zero h0).2 c'
              (by simpa using hdead) with h h,
            { simp [h.1] },
            { exact mul_nonpos_of_nonpos_of_nonneg h.1 (hx.1.2 _ h.2) } } },
        rw [mem_flat_iff.1 hx.1.1, const_sign_of_max_row_eq_zero_of_eq_zero h0, add_zero] at hx0,
        exact (mul_eq_zero.1 ((sum_eq_zero_iff_of_nonpos (λ c hc, hc'0 c)).1 hx0 _
            (mem_univ c))).resolve_left
          (ne_of_lt hc.2) } }
  end)

end close_row

section assert_ge

def assert_ge (T : stableau m n) (fac : rvec (m + n)) (k : ℚ) : stableau (m + 1) n × bool :=
let T' := sign_of_max (T.add_row fac k) fin.lastp in
if hneg : T'.2 < 0 then (T'.1, ff)
  else if T'.2 = 0 then (T'.1.close_row $ fin.last _, tt)
    else (T'.1.restrict fin.lastp (feasible_restrict_sign_of_max $ le_of_not_gt hneg), tt)

end assert_ge

end stableau
