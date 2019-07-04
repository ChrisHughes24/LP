import data.matrix data.rat.basic linear_algebra.basis data.fintype
import linear_algebra.determinant .misc order.pilex
import order.lexicographic .list_sup .fin_find
import data.list.min_max algebra.associated .matrix_pequiv

open matrix fintype finset function

variables {m n : ℕ}
variables (A : matrix (fin m) (fin n) ℚ)

local notation `rvec`:2000 n := matrix (fin 1) (fin n) ℚ
local notation `cvec`:2000 m := matrix (fin m) (fin 1) ℚ

-- def column (j : fin n) : cvec m := λ i _, A i j

-- def row (i : fin m) : rvec n := λ _ j, A i j

variables (b : cvec m) (c : cvec n)

def cvec.ordered_comm_group : ordered_comm_group (cvec n) :=
matrix.ordered_comm_group

local attribute [instance] cvec.ordered_comm_group

def cvec.decidable_le : decidable_rel ((≤) : (cvec n) → (cvec n) → Prop) :=
matrix.decidable_le

local attribute [instance] cvec.decidable_le

--instance : partial_order (matrix (fin m) (fin n) ℚ) := pi.partial_order

local infix ` ⬝ `:70 := matrix.mul
local postfix `ᵀ` : 1500 := transpose

def is_feasible (x : cvec n) : Prop :=
0 ≤ x ∧ A ⬝ x = b

instance (x : cvec n) : decidable (is_feasible A b x) :=
by dunfold is_feasible; apply_instance

def is_optimal (x : cvec n) : Prop :=
is_feasible A b x ∧ ∀ y, is_feasible A b y → cᵀ ⬝ y ≤ cᵀ ⬝ x

def is_invertible' (M : matrix (fin m) (fin n) ℚ) : Prop :=
∃ h : m = n, by rw h at M; exact det M ≠ 0

instance is_invertible'.decidable : decidable_pred (@is_invertible' m n) :=
λ _, by unfold is_invertible'; apply_instance

def comatrix (M : matrix (fin n) (fin n) ℚ) : matrix (fin n) (fin n) ℚ :=
begin
  cases n,
  { exact fin.elim0 },
  { exact λ i j, (-1) ^ ((i + j : ℕ) % 2) * det (minor M
      (λ i' : fin n, if i'.1 < i.1 then i'.cast_succ
        else i'.succ)
      (λ j' : fin n, if j'.1 < j.1 then j'.cast_succ
        else j'.succ)) }
end

def inverse (M : matrix (fin m) (fin n) ℚ) : matrix (fin n) (fin m) ℚ :=
if h : m = n then by subst h; exact (det M)⁻¹ • (comatrix M)ᵀ else 0

/-- false with current inverse definition. True when `M` is square -/
lemma inverse_mul {M : matrix (fin m) (fin n) ℚ} (h : M.has_left_inverse) :
  inverse M ⬝ M = 1 := sorry

/-- false with current inverse definition. True when `M` is square -/
lemma mul_inverse {M : matrix (fin m) (fin n) ℚ} (h : M.has_left_inverse) :
  M ⬝ inverse M = 1 := sorry

def rvec.to_list {n : ℕ} (x : rvec n) : list ℚ :=
(vector.of_fn (x 0)).1

def lex_rvec : linear_order (rvec m) :=
@pilex.linear_order _ _ _ (is_well_order.wf _)
  (λ _, pilex.linear_order (is_well_order.wf _))

def lex_rvec_decidable_linear_order : decidable_linear_order (rvec m) :=
{ decidable_le := λ x y, decidable_of_iff
    (list.lex (<) (rvec.to_list x) (rvec.to_list y) ∨ x = y) sorry,
  ..lex_rvec }

local attribute [instance] lex_rvec_decidable_linear_order

def lex_ordered_comm_group_rvec : ordered_comm_group (rvec m) :=
@pilex.ordered_comm_group _ _ _ (λ _, pilex.ordered_comm_group)

-- local attribute [instance] lex_ordered_comm_group_rvec
--   lex_rvec_decidable_linear_order

def pert_rat (m : ℕ) : Type := ℚ × rvec m

instance : decidable_eq (pert_rat m) := by unfold pert_rat; apply_instance

instance : add_comm_group (pert_rat m) := prod.add_comm_group

instance : module ℚ (pert_rat m) := prod.module

instance : decidable_linear_order (pert_rat m) :=
by letI := @lex_rvec_decidable_linear_order m; exact
{ decidable_le := @prod.lex.decidable _ _ _ _ _ _ _
    (lex_rvec_decidable_linear_order).decidable_le,
  ..lex_linear_order }

instance pert_rat.decidable_le (i j : pert_rat m) : decidable (i ≤ j) :=
@decidable_linear_order.decidable_le _ pert_rat.decidable_linear_order i j

instance has_repr_fin_fun {n : ℕ} {α : Type*} [has_repr α] : has_repr (fin n → α) :=
⟨λ f, repr (vector.of_fn f).to_list⟩

instance {m n} : has_repr (matrix (fin m) (fin n) ℚ) := has_repr_fin_fun

instance : has_repr (pert_rat m) := prod.has_repr

open list

@[simp] lemma fin.mk.inj_iff {n a b : ℕ} {ha : a < n} {hb : b < n} :
  fin.mk a ha = fin.mk b hb ↔ a = b :=
⟨fin.mk.inj, λ h, by subst h⟩

def pequiv_of_vector (v : vector (fin n) m) (hv : v.1.nodup) : pequiv (fin m) (fin n) :=
{ to_fun := λ i, some $ v.nth i,
  inv_fun := λ j, fin.find (λ i, v.nth i = j),
  inv := λ i j, ⟨λ h, by rw ← fin.find_spec _ h; exact rfl,
    λ h, fin.mem_find_of_unique
      (begin
        rintros ⟨i, him⟩ ⟨j, hjm⟩ h₁ h₂,
        cases v,
        refine fin.eq_of_veq (list.nodup_iff_nth_le_inj.1 hv i j _ _ (h₁.trans h₂.symm));
        simpa [v.2]
      end)
      (option.some_inj.1 h)⟩ }

def non_basis_vector_of_vector (v : vector (fin n) m) (hv : v.to_list.nodup) :
  {v : vector (fin n) (n - m) // v.to_list.nodup} :=
⟨⟨(fin_range n).diff v.to_list,
  have h : m ≤ n,
    by rw [← list.length_fin_range n, ← v.2];
      exact list.length_le_of_subperm
        (subperm_of_subset_nodup hv (λ _ _, list.mem_fin_range _)),
  begin
    rw [← add_right_inj m, nat.sub_add_cancel h],
    conv in m { rw [← vector.to_list_length v] },
    rw ← length_append,
    conv_rhs { rw ← length_fin_range n },
    exact list.perm_length ((perm_ext
      (nodup_append.2 ⟨nodup_diff (nodup_fin_range _), hv,
        by simp [list.disjoint, mem_diff_iff_of_nodup (nodup_fin_range n), imp_false]⟩)
      (nodup_fin_range _)).2
      (by simp only [list.mem_diff_iff_of_nodup (nodup_fin_range n),
          list.mem_append, mem_fin_range, true_and, iff_true];
        exact λ _, or.symm (decidable.em _))),
  end⟩,
  nodup_diff (nodup_fin_range _)⟩

def pre_nonbasis_of_vector (v : vector (fin n) m) (hv : v.1.nodup) : pequiv (fin (n - m)) (fin n) :=
pequiv_of_vector (non_basis_vector_of_vector v hv).1 (non_basis_vector_of_vector v hv).2

structure prebasis (m n : ℕ) : Type :=
( basis : pequiv (fin m) (fin n) )
( non_basis : pequiv (fin (n - m)) (fin n) )
( basis_left_inv : basis.trans basis.symm = pequiv.refl (fin m) )
( non_basis_left_inv : non_basis.trans non_basis.symm = pequiv.refl (fin (n - m)) )
( basis_trans_non_basis_symm_eq_bot : basis.trans non_basis.symm = ⊥ )

namespace prebasis
open pequiv

attribute [simp] basis_left_inv non_basis_left_inv basis_trans_non_basis_symm_eq_bot

lemma is_some_basis (B : prebasis m n) : ∀ (i : fin m), (B.basis i).is_some :=
by rw [← trans_symm_eq_iff_forall_mem, basis_left_inv]

lemma is_some_non_basis (B : prebasis m n) : ∀ (k : fin (n - m)), (B.non_basis k).is_some :=
by rw [← trans_symm_eq_iff_forall_mem, non_basis_left_inv]

lemma injective_basis (B : prebasis m n) : injective B.basis :=
injective_of_forall_is_some (is_some_basis B)

lemma injective_non_basis (B : prebasis m n) : injective B.non_basis :=
injective_of_forall_is_some (is_some_non_basis B)

local infix ` ♣ `: 70 := pequiv.trans

def swap (B : prebasis m n) (i : fin m) (j : fin (n - m)) : prebasis m n :=
let i' := @option.get _ (B.basis i) (B.is_some_basis _) in
let j' := @option.get _ (B.non_basis j) (B.is_some_non_basis _) in
{ basis := B.basis.trans (equiv.swap i' j').to_pequiv,
  non_basis := B.non_basis.trans (equiv.swap i' j').to_pequiv,
  basis_left_inv := by rw [symm_trans_rev, ← trans_assoc, trans_assoc B.basis,
        ← equiv.to_pequiv_symm,  ← equiv.to_pequiv_trans];
      simp,
  non_basis_left_inv := by rw [symm_trans_rev, ← trans_assoc, trans_assoc B.non_basis, ← equiv.to_pequiv_symm,
        ← equiv.to_pequiv_trans];
      simp,
  basis_trans_non_basis_symm_eq_bot := by rw [symm_trans_rev, ← trans_assoc, trans_assoc B.basis,
      ← equiv.to_pequiv_symm, ← equiv.to_pequiv_trans];
    simp }

lemma not_is_some_non_basis_of_is_some_basis (B : prebasis m n) (j : fin n) :
  (B.basis.symm j).is_some → (B.non_basis.symm j).is_some → false :=
begin
  rw [option.is_some_iff_exists, option.is_some_iff_exists],
  rintros ⟨i, hi⟩ ⟨k, hk⟩,
  have : B.basis.trans B.non_basis.symm i = none,
  { rw [B.basis_trans_non_basis_symm_eq_bot, pequiv.bot_apply] },
  rw [pequiv.trans_eq_none] at this,
  rw [pequiv.eq_some_iff] at hi,
  exact (this j k).resolve_left (not_not.2 hi) hk
end

lemma is_none_basis (B : prebasis m n) (j : fin n)
  (hb : B.basis.symm j = none) (hnb : B.non_basis.symm j = none) : false :=
have hs : card (univ.image B.basis) = m,
  by rw [card_image_of_injective _ (B.injective_basis), card_univ, card_fin],
have ht : card (univ.image B.non_basis) = (n - m),
  by rw [card_image_of_injective _ (B.injective_non_basis), card_univ, card_fin],
have hst : disjoint (univ.image B.basis) (univ.image B.non_basis),
  from finset.disjoint_left.2 begin
    simp only [mem_image, exists_imp_distrib, not_exists],
    assume j i _ hbasis k _ hnonbasis,
    cases option.is_some_iff_exists.1 (is_some_basis B i) with x hi,
    cases option.is_some_iff_exists.1 (is_some_non_basis B k) with y hk,
    have hxy : x = y,
    { rw [← option.some_inj, ← hk, ← hi, hbasis, hnonbasis] }, subst hxy,
    rw [← eq_some_iff] at hi hk,
    refine not_is_some_non_basis_of_is_some_basis B x _ _;
    simp [hi, hk]
  end,
have (univ.image B.basis) ∪ (univ.image B.non_basis) = univ.image (@some (fin n)),
  from eq_of_subset_of_card_le
    _
    (begin
      rw [card_image_of_injective, card_univ, card_fin, card_disjoint_union hst, hs, ht],
      exact nat.le_add_

    end)


-- lemma is_some_basis_iff (B : prebasis m n) {j : fin n} :
--   (B.basis.symm j).is_some ↔ ¬(B.non_basis.symm j).is_some :=
-- ⟨is_some_basis_iff_aux B, not_imp_comm.1 _⟩

lemma mul_symm_add_mul_symm (B : prebasis m n) :
  ((B.basis.symm.trans B.basis).to_matrix : matrix (fin n) (fin n) ℚ) +
  (B.non_basis.symm.trans B.non_basis).to_matrix = 1 :=
begin
  ext,
  simp only [add_val, pequiv.symm_trans, pequiv.to_matrix, one_val,
    pequiv.mem_of_set_iff, set.mem_set_of_eq],
  have := is_some_basis B j,
  split_ifs; tauto
end


lemma basis_trans_non_basis_eq_bot (B : prebasis m n) :
  B.basis.trans B.non_basis.symm = ⊥ :=
begin
  ext,
  dsimp [pequiv.trans], simp,

end


end prebasis

def pivot (A : matrix (fin m) (fin n) ℚ) (c : rvec n) (b : cvec m)
  (B : array m (fin n))
  (NB : array (n - m) (fin n))
  (i : fin (n - m)) (j : fin m) :
  array m (fin n) × -- basis
  array (n - m) (fin n) × -- non basis
  matrix (fin m) (fin (n - m)) ℚ × -- A_bar
  (rvec m) × -- c_B
  (rvec (n - m)) × --c_N
  (cvec m) × --b_bar
  matrix (fin m) (fin m) ℚ -- pert
  :=
let NBi : fin n := NB.read i in
let Bj : fin n := B.read j in
let NB' := NB.write i Bj in
let B' := B.write j NBi in
let A_B'_inverse := _root_.inverse (minor A id B'.read) in
⟨B',
  NB',
  A_B'_inverse ⬝ minor A id NB'.read,
  minor c id B'.read,
  minor c id NB'.read,
  A_B'_inverse ⬝ b,
  A_B'_inverse⟩

/-- given a basis, such that A_B is invertible, `solution_of_basis` returns `x` such that `A ⬝ x = b`. -/
def solution_of_basis (A : matrix (fin m) (fin n) ℚ) (b : cvec m) (B : prebasis m n) : cvec n :=
minor 1 id B.1.nth ⬝ inverse (minor A id B.1.nth) ⬝ b

local notation `£` := default _

@[simp] lemma univ_unique {α : Type*} [unique α] {h : fintype α} : @univ α h = {default α} :=
finset.ext.2 $ λ x, by simpa using unique.eq_default x

lemma solution_of_basis_is_solution (A : matrix (fin m) (fin n) ℚ) (b : cvec m)
  (B : prebasis m n) (hB : has_right_inverse (minor A id B.1.nth)) :
  A ⬝ solution_of_basis A b B = b :=
by rw [solution_of_basis, ← A.mul_assoc, ← A.mul_assoc,  ← minor_eq_minor_one_mul A,
    mul_inverse hB, b.one_mul];
  apply_instance

/-- function used solely for proof of termination. Never executed -/
def lex_objective_function (A : matrix (fin m) (fin n) ℚ)
  (c : rvec n) (b : cvec m) (B : prebasis m n) : ℚ × rvec m :=
((one_by_one_ring_equiv (fin 1) ℚ).to_equiv (minor c id B.1.nth ⬝ inverse (minor A id B.1.nth) ⬝ b),
  minor c id B.1.nth ⬝ inverse (minor A id B.1.nth))

lemma lex_objective_function_increasing (A : matrix (fin m) (fin n) ℚ)
  (c : rvec n) (b : cvec m) (B : prebasis m n) (i : fin (n - m)) (j : fin m) :
  lex_objective_function A c b B < lex_objective_function A c b (B.swap i j) :=
begin
  dsimp [lex_objective_function],

end

def simplex [inhabited (fin m)] (A : matrix (fin m) (fin n) ℚ)
  (c : rvec n) (b : cvec m) :
  Π (B : array m (fin n))
  (NB : array (n - m) (fin n))
  (A_bar : matrix (fin m) (fin (n - m)) ℚ)
  (c_B : rvec m) (c_N : rvec (n - m)) (b_bar : cvec m)
  (pert : (matrix (fin m) (fin m) ℚ))
  (pivots : ℕ),
  ℕ × option
  (array m (fin n) × -- basis
  array (n - m) (fin n) × -- non basis
  matrix (fin m) (fin (n - m)) ℚ × -- A_bar
  (rvec m) × -- c_B
  (rvec (n - m)) × --c_N
  (cvec m) × --b_bar
  matrix (fin m) (fin m) ℚ) -- pert)
| B NB A_bar c_B c_N b_bar pert pivots :=
let reduced_cost := c_N - c_B ⬝ A_bar in
let i' := (list.fin_range (n - m)).find (λ i, 0 < column reduced_cost (fin 1) i) in
match i' with
| none := (pivots, some (B, NB, A_bar, c_B, c_N, b_bar, pert))
| some i :=
  let ratio_pert : fin m → pert_rat m := λ j : fin m,
    (A_bar j i)⁻¹ • (b_bar j 0, row' pert (fin 1) j) in
  let l := (list.fin_range m).filter (λ j, 0 < ratio_pert j) in
  match l with
  | [] := (pivots + 1, none)
  | (a::l) :=
  let j : fin m := list.argmin ratio_pert (a :: l) in
  let ⟨B', NB', A_bar', c_B', c_N', b_bar', pert'⟩ :=
    pivot A c b B NB i j in
  have wf : true, from trivial,
  simplex B' NB' A_bar' c_B' c_N' b_bar' pert' (pivots + 1)
  end
end
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, true_well_founded⟩],
  dec_tac := tactic.assumption}

instance read_dec_pred (a : array m (fin n)) (i : fin n) :
  decidable_pred (λ (k : fin m), array.read a k = i) := by apply_instance


def find_optimal_solution_from_starting_basis [inhabited (fin m)] (A : matrix (fin m) (fin n) ℚ)
  (c : rvec n) (b : cvec m) (B : array m (fin n)) : ℕ × option (cvec n) :=
let NB : array (n - m) (fin n) :=
  vector.to_array ⟨(list.fin_range n).filter (λ i, ¬ B.mem i), sorry⟩ in
let A_B := minor A id B.read in
let A_N := minor A id NB.read in
let pert := _root_.inverse A_B in
let A_bar := pert ⬝ A_N in
let c_B := minor c id B.read in
let c_N := minor c id NB.read in
let b_bar := pert ⬝ b in
match simplex A c b B NB A_bar c_B c_N b_bar pert 0 with
| (pivots, none) := (pivots, none)
| (pivots, some ⟨B', NB', A_bar', c_B', c_N', b_bar', pert'⟩) := prod.mk pivots $
some (λ i _,
  match @fin.find _ (λ k, B'.read k = i) (read_dec_pred _ _) with
  | none := 0
  | some k := b_bar' k 0
  end)
end

/- test code -/

instance {m : ℕ} : inhabited (fin m.succ) := ⟨0⟩

def list.to_matrix (m :ℕ) (n : ℕ) (l : list (list ℚ)) : matrix (fin m) (fin n) ℚ :=
λ i j, (l.nth_le i sorry).nth_le j sorry

def found_solution_is_feasible [inhabited (fin m)] (A : matrix (fin m) (fin n) ℚ)
  (c : rvec n) (b : cvec m) (B : array m (fin n)) : bool :=
match find_optimal_solution_from_starting_basis A c b B with
| (_, none) := tt
| (_, some x) := (A ⬝ x = b ∧ 0 ≤ x : bool)
end

def is_optimal_bool [inhabited (fin m)] (A : matrix (fin m) (fin n) ℚ)
  (c : rvec n) (b : cvec m) (B : array m (fin n)) : bool :=
let NB : array (n - m) (fin n) :=
  vector.to_array ⟨(list.fin_range n).filter (λ i, ¬ B.mem i), sorry⟩ in
let A_B := minor A id B.read in
let A_N := minor A id NB.read in
let pert := _root_.inverse A_B in
let A_bar := pert ⬝ A_N in
let c_B := minor c id B.read in
let c_N := minor c id NB.read in
let b_bar := pert ⬝ b in
match simplex A c b B NB A_N c_B c_N b_bar pert 0 with
| (_, none) := tt
| (_, some ⟨B', NB', A_bar', c_B', c_N', b_bar', pert'⟩) := c_N' - c_B' ⬝ A_bar' ≤ 0
end

def is_feasible_basis [inhabited (fin m)] (A : matrix (fin m) (fin n) ℚ)
  (c : rvec n) (b : cvec m) (B : array m (fin n)) : Prop :=
let A_B := minor A id B.read in
let NB : array (n - m) (fin n) :=
  vector.to_array ⟨(list.fin_range n).filter (λ i, ¬ B.mem i), sorry⟩ in
let A_N := minor A id NB.read in
let pert := _root_.inverse A_B in
let A_bar := pert ⬝ A_N in
let c_B := minor c id B.read in
let c_N := minor c id NB.read in
let b_bar := pert ⬝ b in
let x : cvec n := λ i _, match @fin.find _ (λ k, B.read k = i) (read_dec_pred _ _) with
  | none := 0
  | some k := b_bar k 0
  end in
(0 : cvec n) ≤ x ∧ A ⬝ x = b ∧ det A_B ≠ 0

def finishing_basis [inhabited (fin m)] (A : matrix (fin m) (fin n) ℚ)
  (c : rvec n) (b : cvec m) (B : array m (fin n)) : option (array m (fin n)) :=
let NB : array (n - m) (fin n) :=
  vector.to_array ⟨(list.fin_range n).filter (λ i, ¬ B.mem i), sorry⟩ in
let A_B := minor A id B.read in
let A_N := minor A id NB.read in
let pert := _root_.inverse A_B in
let A_bar := pert ⬝ A_N in
let c_B := minor c id B.read in
let c_N := minor c id NB.read in
let b_bar := pert ⬝ b in
option.map prod.fst (simplex A c b B NB A_N c_B c_N b_bar pert 0).2

def test  [inhabited (fin m)] (A : matrix (fin m) (fin n) ℚ)
  (c : rvec n) (b : cvec m) (B : array m (fin n)) :=
let NB : array (n - m) (fin n) :=
  vector.to_array ⟨(list.fin_range n).filter (λ i, ¬ B.mem i), sorry⟩ in
let A_B := minor A id B.read in
let A_N := minor A id NB.read in
let pert := _root_.inverse A_B in
let A_bar := pert ⬝ A_N in
let c_B := minor c id B.read in
let c_N := minor c id NB.read in
let b_bar := pert ⬝ b in
let reduced_cost := c_N - c_B ⬝ A_bar in
let b_pert : fin m → pert_rat m := λ j : fin m,
     (A_bar j ⟨0, sorry⟩)⁻¹ • (b_bar j 0, row' pert (fin 1) j) in
let reduced_cost := c_N - c_B ⬝ A_bar in
let i' := (list.fin_range (n - m)).find (λ i, 0 < column reduced_cost (fin 1) i) in
match i' with
| none := sorry
| some i :=
  let ratio_pert : fin m → pert_rat m := λ j : fin m,
     (A_bar j i)⁻¹ • (b_bar j 0, row' pert (fin 1) j) in
  let l := (list.fin_range m).filter (λ j, 0 < ratio_pert j) in ratio_pert end
--simplex A c b B NB A_N c_B c_N b_bar pert

def objective_function_value (c : rvec n) (x : cvec n) := c ⬝ x


-- (list.fin_range (n - m)).find (λ i, 0 < column reduced_cost (fin 1) i)

-- pivot A c b B NB

instance [inhabited (fin m)] (A : matrix (fin m) (fin n) ℚ)
  (c : rvec n) (b : cvec m) (B : array m (fin n)) :
  decidable (is_feasible_basis A c b B) :=
by dunfold is_feasible_basis; apply_instance


-- def ex.A := list.to_matrix 3 4 [[12,-1,1,1],
--                      [1,1.45,1,0],
--                      [1,2,0,1]]

-- def ex.c : rvec 4 := λ _ i, (list.nth_le [1, 1.2, 1, 1.3] i sorry)
-- --#eval ex.c
-- def ex.b : cvec 3 := (λ i _, (list.nth_le [2, 2, 4] i sorry))
-- --#eval ex.b
-- def ex.B : array 3 (fin 4) := list.to_array [0, 1, 3]

-- def ex.NB : array 1 (fin 4) := list.to_array [2]

-- def ex.A := list.to_matrix 2 5 [[1,1,0,1,0], [0,1,-1,0,1]]

-- def ex.b : cvec 2 := (λ i _, (list.nth_le [8,0] i sorry))
-- --#eval ex.b
-- def ex.c : rvec 5 := λ _ i, (list.nth_le [1, 1, 1, 0, 0] i sorry)
-- --#eval ex.c
-- def ex.B : array 2 (fin 5) := list.to_array [3,4]

def ex.A := list.to_matrix 3 7 [[1/4, - 8, -  1, 9, 1, 0, 0],
                                [1/2, -12, -1/2, 3, 0, 1, 0],
                                [  0,   0,    1, 0, 0, 0, 1]]

def ex.b : cvec 3 := (λ i _, list.nth_le [0,0,1] i sorry)
--#eval ex.b
def ex.c : rvec 7 := λ _ i, (list.nth_le [3/4, -20, 1/2, -6, 0, 0, 0] i sorry)
--#eval ex.c
def ex.B : array 3 (fin 7) := list.to_array [4,5,6]

-- #eval (found_solution_is_feasible ex.A ex.c ex.b ex.B)

#eval (find_optimal_solution_from_starting_basis ex.A ex.c ex.b ex.B)
--set_option trace.fun_info true
#eval (is_optimal_bool ex.A ex.c ex.b ex.B)

-- (some [[2064/445]])
-- (some [[6401/1895]])
#eval (is_feasible_basis ex.A ex.c ex.b ex.B : bool)
-- #eval (show matrix _ _ ℚ, from minor ex.A id ex.B.read) *
--   _root_.inverse (show matrix _ _ ℚ, from minor ex.A id ex.B.read )
-- #eval ((1 : matrix (fin 1) (fin 1) ℚ) - (minor ex.c id ex.B.read) ⬝
--   _root_.inverse (minor ex.A id ex.B.read) ⬝
--   (minor ex.A id ex.NB.read))

#eval finishing_basis ex.A ex.c ex.b ex.B

#eval test ex.A ex.c ex.b ex.B

#eval (let x : cvec 4 := λ i _, list.nth_le [0, 80/89, 62/89, 196/89] i sorry in
  let A := list.to_matrix 3 4 [[12, -1, 1, 1],
                     [1, 1.45, 1, 0],
                     [1, 2, 0, 1]]
                     in A ⬝ x
 )
