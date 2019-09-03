import data.matrix data.rat.basic .misc tactic.fin_cases
import .matrix_pequiv order.order_iso .simplex_new_pivot

open matrix fintype finset function pequiv simplex simplex.prebasis

variables {m n k: ℕ}

local notation `rvec`:2000 n := matrix (fin 1) (fin n) ℚ
local notation `cvec`:2000 m := matrix (fin m) (fin 1) ℚ
local infix ` ⬝ `:70 := matrix.mul
local postfix `ᵀ` : 1500 := transpose
local attribute [instance] matrix.partial_order

namespace simplex'

def choose_pivot_column (AN_bar : matrix (fin m) (fin (n - m)) ℚ)
  (c : rvec (n - m)) : option (fin (n - m)) :=
fin.find (λ s : fin (n - m), 0 < c 0 s)

def choose_pivot_row (AN_bar : matrix (fin m) (fin (n - m)) ℚ) (b_bar : cvec m)
  (s : fin (n - m)) : option (fin m) :=
fin.find (λ r : fin m, 0 < AN_bar r s ∧ ∀ i : fin m, 0 < AN_bar i s →
  (AN_bar r s)⁻¹ * b_bar r 0 ≤ (AN_bar i s)⁻¹ * b_bar i 0)

lemma choose_pivot_column_eq_none (B : prebasis m n) (A_bar : matrix (fin m) (fin n) ℚ)
  (b_bar : cvec m) (c : rvec n) (hA_bar : A_bar ⬝ B.basis.to_matrixᵀ = 1)
  (h0b : 0 ≤ b_bar)
  (h : choose_pivot_column (A_bar ⬝ B.nonbasis.to_matrixᵀ) (reduced_cost B A_bar c) = none) :
  is_optimal_basis B A_bar b_bar c :=
is_optimal_basis_of_reduced_cost_nonpos _ _ hA_bar h0b $
  begin
    intros i j,
    fin_cases i,
    exact le_of_not_gt (fin.find_eq_none_iff.1 h j : _)
  end

lemma choose_pivot_row_eq_none (B : prebasis m n) (A_bar : matrix (fin m) (fin n) ℚ)
  (b_bar : cvec m) (r : fin m) (s : fin (n - m))
  (hn : choose_pivot_row (A_bar ⬝ B.nonbasis.to_matrixᵀ) b_bar s = none) :
  (A_bar ⬝ B.nonbasis.to_matrixᵀ) r s ≤ 0 :=
le_of_not_gt $ λ (hpivot : _ < _), begin
  rw [choose_pivot_row, fin.find_eq_none_iff] at hn,
  cases @finset.min_of_mem _ _
    ((univ.filter (λ j : fin m, 0 < (A_bar ⬝ B.nonbasis.to_matrixᵀ) j s)).image
      (λ i, ((A_bar ⬝ B.nonbasis.to_matrixᵀ) i s)⁻¹ * b_bar i 0))
      (((A_bar ⬝ B.nonbasis.to_matrixᵀ) r s)⁻¹ * b_bar r 0)
     (mem_image_of_mem _ (by simp *)) with q hq,
  rcases mem_image.1 (mem_of_min hq) with ⟨i, hip, hiq⟩,
  subst hiq,
  refine hn i ⟨(finset.mem_filter.1 hip).2, λ j hj, _⟩,
  refine min_le_of_mem _ hq,
  refine mem_image_of_mem _ _,
  simpa using hj
end

lemma choose_pivot_column_spec (AN_bar : matrix (fin m) (fin (n - m)) ℚ) (c : rvec (n - m))
  (s : fin (n - m)) (hs : s ∈ choose_pivot_column AN_bar c) : 0 < c 0 s :=
fin.find_spec _ hs

def swap_inverse (AN_bar : matrix (fin m) (fin (n - m)) ℚ) (r : fin m) (s : fin (n - m)) :
  matrix (fin m) (fin m) ℚ :=
let pivot_inv := (AN_bar r s)⁻¹ in
(1 : matrix (fin m) (fin m) ℚ).write_column r
  (λ i, if i = r then pivot_inv else -AN_bar i s * pivot_inv)

lemma pivot_element_eq (B : prebasis m n) (A_bar : matrix (fin m) (fin n) ℚ)
  (r : fin m) (s : fin (n - m)) :
  (pivot_element B A_bar r s) = (λ _ _, (A_bar ⬝ B.nonbasis.to_matrixᵀ) r s) :=
begin
  ext i j,
  have hi : i = 0, from subsingleton.elim _ _,
  have hj : j = 0, from subsingleton.elim _ _,
  substs hi hj,
  simp only [pivot_element, matrix_mul_apply, mul_matrix_apply, (to_matrix_symm _).symm],
  refl
end

lemma single_apply {α β : Type*} [decidable_eq α] [decidable_eq β] (a a' : α) (b : β) :
  single a b a' = if a' = a then some b else none := rfl

@[simp] lemma add_add_neg_cancel'_right {α : Type*} [add_comm_group α] (a b : α) : a + (b + -a) = b :=
add_sub_cancel'_right a b

lemma swap_inverse_eq_swap_inverse (B : prebasis m n) (AN_bar : matrix (fin m) (fin (n - m)) ℚ)
  (r : fin m) (s : fin (n - m)) (hpivot : AN_bar r s ≠ 0) :
  swap_inverse AN_bar r s =
  simplex.swap_inverse B (AN_bar ⬝ B.nonbasis.to_matrix) r s :=
have ∀ i j r s, (AN_bar ⬝ ((single s (0 : fin 1)).to_matrix ⬝ (λ (_ _ : fin 1), (AN_bar r s)⁻¹))) i j
  = (AN_bar r s)⁻¹ * AN_bar i s,
  begin
    intros, fin_cases j,
    rw [← matrix.mul_assoc, mul_eq_smul, matrix.smul_val, matrix_mul_apply, symm_single,
      simplex'.single_apply, if_pos],
    congr,
  end,
begin
  ext i j,
  simp [simplex'.swap_inverse, simplex.swap_inverse,
    matrix.mul_add, matrix.add_mul, matrix.add_val, write_column_apply,
    matrix.neg_val,
    mul_matrix_apply, matrix_mul_apply, one_val, pivot_element_eq, inv_def],
  dsimp [symm_single, simplex'.single_apply],
  split_ifs,
  { rw [if_pos h.symm, if_pos h_1],
    simp [add_val, neg_val, one_val, matrix.mul_assoc, this, h_1, inv_mul_cancel hpivot], },
  { cc },
  { cc },
  { rw [if_neg h_1, if_pos h.symm],
    simp [matrix.mul_assoc, this, mul_comm] },
  { cc },
  { rw [if_neg (ne.symm h), if_neg h_2], simp },
  { rw [if_pos h_2, if_neg (ne.symm h)], simp },
  { rw [if_neg h_2, if_neg (ne.symm h)], simp }
end

lemma swap_nonbasis_eq (B : prebasis m n) (r : fin m) (s : fin (n - m)) :
  (B.swap r s).nonbasis.to_matrix = (B.nonbasis.to_matrix : matrix _ _ ℚ)
  + (single s (B.basisg r)).to_matrix - (single s (B.nonbasisg s)).to_matrix :=
begin
  dsimp [prebasis.swap],
  simp only [to_matrix_swap, to_matrix_trans],
  simp [matrix.mul_add, (to_matrix_trans _ _).symm,
    trans_single_of_mem _ (nonbasisg_mem B s),
    trans_single_of_eq_none _ (nonbasis_basisg_eq_none B r)]
end

lemma nonbasis_transpose_mul_single (B : prebasis m n) (i : fin (n - m)) (j : fin k) :
  (B.nonbasis.to_matrixᵀ : matrix _ _ ℚ) ⬝ (single i j).to_matrix =
  (single (B.nonbasisg i) j).to_matrix :=
by rw [← to_matrix_symm, ← to_matrix_trans, trans_single_of_mem _ (nonbasis_nonbasisg _ _)]

lemma basis_transpose_mul_single (B : prebasis m n) (i : fin m) (j : fin k) :
  (B.basis.to_matrixᵀ : matrix _ _ ℚ) ⬝ (single i j).to_matrix =
  (single (B.basisg i) j).to_matrix :=
by rw [← to_matrix_symm, ← to_matrix_trans, trans_single_of_mem _ (basis_basisg _ _)]

@[simp] lemma swap_nonbasis_mul_single_of_eq (B : prebasis m n) (r : fin m) (s : fin (n - m)) :
  ((B.swap r s).nonbasis.to_matrixᵀ : matrix _ _ ℚ) ⬝ (single s (0 : fin 1)).to_matrix =
  B.basis.to_matrixᵀ ⬝ (single r 0).to_matrix  :=
begin
  simp [swap_nonbasis_eq, transpose_add, (to_matrix_symm _).symm, matrix.add_mul],
  simp [to_matrix_symm, nonbasis_transpose_mul_single, basis_transpose_mul_single],
end

@[simp] lemma swap_nonbasis_mul_single_of_ne (B : prebasis m n) (r : fin m) {s : fin (n - m)}
  {j : fin (n - m)} (hsj : s ≠ j) :
  ((B.swap r s).nonbasis.to_matrixᵀ : matrix _ _ ℚ) ⬝ (single j (0 : fin 1)).to_matrix =
  B.nonbasis.to_matrixᵀ ⬝ (single j 0).to_matrix  :=
begin
  simp [swap_nonbasis_eq, transpose_add, (to_matrix_symm _).symm, matrix.add_mul],
  simp [to_matrix_symm, nonbasis_transpose_mul_single, basis_transpose_mul_single,
    single_mul_single_of_ne hsj],
end

lemma reduced_cost_swap (B : prebasis m n) (A_bar : matrix (fin m) (fin n) ℚ) (c : rvec n)
  (r : fin m) (s : fin (n - m)) (hA_bar : A_bar ⬝ B.basis.to_matrixᵀ = 1)
  (hpivot : pivot_element B A_bar r s ≠ 0) :
  reduced_cost (B.swap r s) (simplex.swap_inverse B A_bar r s ⬝ A_bar) c =
  reduced_cost B A_bar c ⬝ (1 - (single s (0 : fin 1)).to_matrix ⬝
    (pivot_element B A_bar r s)⁻¹ ⬝ (single 0 r).to_matrix ⬝ A_bar ⬝ B.nonbasis.to_matrixᵀ -
    (single s 0).to_matrix ⬝ (pivot_element B A_bar r s)⁻¹ ⬝ (single 0 s).to_matrix) :=
have h₁ : simplex.swap_inverse B A_bar r s ⬝ A_bar ⬝ (to_matrix ((swap B r s).basis))ᵀ = 1,
  by rw [matrix.mul_assoc, swap_mul_swap_inverse hA_bar hpivot],
have h₂ : ∀ {k : ℕ}, ∀ {M : matrix (fin 1) (fin k) ℚ},
    to_matrix (single s r) ⬝ (A_bar ⬝ ((to_matrix (B.nonbasis))ᵀ ⬝
    (to_matrix (single s 0) ⬝ ((pivot_element B A_bar r s)⁻¹ ⬝ M)))) =
    (single s 0).to_matrix ⬝ M,
  begin
    intros,
    rw [← single_mul_single s (0 : fin 1) r, matrix.mul_assoc],
    refine congr_arg (matrix.mul _) _,
    simp only [(matrix.mul_assoc _ _ _).symm, pivot_element, inv_eq_inverse] at ⊢ hpivot,
    rw [one_by_one_mul_inv_cancel hpivot, matrix.one_mul]
  end,
begin
  refine mul_single_ext (λ j, _),
  let x : matrix _ _ ℚ := (B.swap r s).nonbasis.to_matrixᵀ ⬝
    (single j (0 : fin 1)).to_matrix,
  have hxdef : x = (B.swap r s).nonbasis.to_matrixᵀ ⬝
    (single j (0 : fin 1)).to_matrix, from rfl,
  have hx : (single j (0 : fin 1)).to_matrix = (B.swap r s).nonbasis.to_matrix ⬝ x,
  { simp [x, (matrix.mul_assoc _ _ _).symm] },
  let b_bar := (simplex.swap_inverse B A_bar r s ⬝ A_bar) ⬝ x,
  rw [hx, ← matrix.mul_assoc, ← add_left_inj (c ⬝ (B.swap r s).basis.to_matrixᵀ ⬝ b_bar),
    ← objective_function_eq rfl h₁, matrix.mul_assoc c _ b_bar],
  have h₃ : A_bar ⬝ ((to_matrix ((swap B r s).basis))ᵀ ⬝ b_bar) = A_bar ⬝ x,
  { simp only [b_bar, x, (matrix.mul_assoc _ _ _).symm],
    rw [mul_eq_one_comm.1 (swap_mul_swap_inverse hA_bar hpivot),
      matrix.one_mul], },
  conv_rhs {rw [objective_function_eq h₃ hA_bar], },
  conv_lhs {rw [objective_function_eq rfl hA_bar] },
  simp [x, b_bar, simplex.swap_inverse, matrix.mul_add, matrix.mul_assoc,
    mul_right_eq_of_mul_eq (nonbasis_mul_nonbasis_transpose _),
    matrix.add_mul, mul_right_eq_of_mul_eq (nonbasis_mul_swap_basis_tranpose _ _ _), h₂],
  by_cases hjs : j = s,
  { simp only [pivot_element, matrix.mul_assoc] at hpivot,
    simp [hjs, mul_right_eq_of_mul_eq hA_bar, matrix.mul_assoc,
      mul_right_eq_of_mul_eq (nonbasis_mul_basis_transpose _),
      pivot_element, inv_eq_inverse, one_by_one_inv_mul_cancel hpivot] },
  { simp [mul_right_eq_of_mul_eq hA_bar, single_mul_single_of_ne (ne.symm hjs),
      swap_nonbasis_mul_single_of_ne _ _ (ne.symm hjs),
      mul_right_eq_of_mul_eq (nonbasis_mul_nonbasis_transpose _)] }
end

set_option eqn_compiler.zeta true

def simplex : Π (B : prebasis m n) (AN_bar : matrix (fin m) (fin (n - m)) ℚ) (b_bar : cvec m)
  (c : rvec (n - m)),
  option (prebasis m n × matrix (fin m) (fin (n - m)) ℚ × (cvec m) × (rvec (n - m)))
| B AN_bar b_bar c :=
  match choose_pivot_column AN_bar c with
  | none   := some (B, AN_bar, b_bar, c)
  | some s :=
    match choose_pivot_row AN_bar b_bar s with
    | none   := none
    | some r :=
      have wf : false, from sorry,
      let S := simplex'.swap_inverse AN_bar r s in
      let AN_bar' : matrix (fin m) (fin (n - m)) ℚ :=
        AN_bar.write_column s (λ j, if j = r then (1 : ℚ) else 0) in
      simplex (B.swap r s) (S ⬝ AN_bar') (S ⬝ b_bar)
        ((c - (c 0 s / AN_bar r s) • (λ _, AN_bar r) -
          (0 : matrix _ _ ℚ).write_column s (λ _, c 0 s / AN_bar r s)))
    end
  end
using_well_founded { rel_tac := λ _ _, `[exact ⟨_, empty_wf⟩], dec_tac := tactic.assumption }

lemma simplex_spec : Π (B : prebasis m n) (A_bar : matrix (fin m) (fin n) ℚ)
  (b_bar : cvec m) (c : rvec n) (hA_bar : A_bar ⬝ B.basis.to_matrixᵀ = 1) (h0b : 0 ≤ b_bar),
  (option.cases_on (simplex B (A_bar ⬝ B.nonbasis.to_matrixᵀ) b_bar (reduced_cost B A_bar c))
    (is_unbounded A_bar b_bar c)
    (λ P, is_optimal_basis P.1 A_bar b_bar c) : Prop)
| B A_bar b_bar c := assume hA_bar h0b,
  begin
    rw [simplex'.simplex],
    cases hs : choose_pivot_column (A_bar ⬝ B.nonbasis.to_matrixᵀ)
      (reduced_cost B A_bar c) with s,
    { dsimp [simplex'.simplex._match_3],
      exact choose_pivot_column_eq_none _ _ _ _ hA_bar h0b hs },
    { dsimp [simplex'.simplex._match_3],
      cases hr : choose_pivot_row (A_bar ⬝ B.nonbasis.to_matrixᵀ) b_bar s with r,
      { dsimp [simplex'.simplex._match_4],
        have : 0 < reduced_cost B A_bar c ⬝ (single s (0 : fin 1)).to_matrix,
        { rw [cvec_one_lt_iff, matrix_mul_apply],
          exact choose_pivot_column_spec _ _ _ hs },
        exact is_unbounded_of_pivot_element_nonpos b_bar _ hA_bar h0b this
          (λ r i j, by rw [pivot_element_eq];
            exact choose_pivot_row_eq_none _ _ _ _ _ hr) },
      { dsimp [simplex'.simplex._match_4],
        let AN_bar := A_bar ⬝ B.nonbasis.to_matrixᵀ,
        let S := simplex'.swap_inverse AN_bar r s,
        let AN_bar' : matrix (fin m) (fin (n - m)) ℚ :=
          AN_bar.write_column s (λ j, if j = r then (1 : ℚ) else 0),
        have := simplex_spec (B.swap r s) _ _ _ _ _,
         } },
  end

end simplex'

def ex.A := list.to_matrix 3 4 [[1/64443321,   18932,    -1, 9],
                                [1/2, -7/145931, -1/145903, 3],
                                [  -11,     -1111,     22, 100]]

def ex.b : cvec 3 := (λ i _, list.nth_le [0,0,1] i sorry)
--#eval ex.b
def ex.c : rvec 4 := λ _ i, (list.nth_le [3/4, -20, 1/2, -6] i sorry)

#eval @_root_.simplex 3 7 ex.A ex.b ex.c
