import data.matrix tactic.fin_cases .matrix_pequiv
import linear_algebra.finite_dimensional

local infix ` ⬝ `:70 := matrix.mul
local postfix `ᵀ` : 1500 := matrix.transpose

universes u v w

namespace matrix

section
variables {l m n o : Type u} [fintype l] [fintype m] [fintype n] [fintype o]
variables {one : Type u} [unique one] [fintype one] [decidable_eq one] {R : Type*} --[comm_ring R]

open function pequiv

local notation `£` := default _

instance matrix.vector_space [discrete_field R] : vector_space R (matrix m n R) :=
{ ..matrix.module }

instance [discrete_field R] : finite_dimensional R (matrix m n R) :=
@is_noetherian_pi R m _ _ _ _ _ (λ _, is_noetherian_pi)

@[simp] lemma symm_single_apply {α β : Type*} [decidable_eq α] [decidable_eq β] (a : α) (b : β) :
  (single a b).symm b = some a := by dsimp; simp

lemma mul_single_ext' [semiring R] (one : Type u) [unique one] [fintype one] [decidable_eq one]
  [decidable_eq m] [decidable_eq n] {A B : matrix m n R}
  (h : ∀ j, A ⬝ (single j (default one)).to_matrix = B ⬝
    (single j (default one)).to_matrix) : A = B :=
begin
  ext i j,
  have := congr_fun (congr_fun (h j) i) (default one),
  rwa [matrix_mul_apply, matrix_mul_apply, symm_single_apply] at this
end

lemma single_mul_ext' [semiring R] (one : Type u) [unique one] [fintype one] [decidable_eq one]
  [decidable_eq m] [decidable_eq n] {A B : matrix m n R}
  (h : ∀ i, (single (default one) i).to_matrix ⬝ A =
    (single (default one) i).to_matrix ⬝ B) : A = B :=
begin
  ext i j,
  have := congr_fun (congr_fun (h i) (default one)) j,
  rwa [mul_matrix_apply, mul_matrix_apply, single_apply] at this
end

lemma matrix_eq_sum_single_mul [semiring R] [decidable_eq m] (M : matrix m n R) :
  M = finset.univ.sum (λ i : m, (single i i).to_matrix ⬝ M) :=
by letI := classical.dec_eq n; exact single_mul_ext' punit (begin
  assume i,
  simp only [matrix.mul_sum, single_mul_single],
  rw [finset.sum_eq_single i],
  { simp },
  { assume _ _ hbi,
    rw [← matrix.mul_assoc, single_mul_single_of_ne hbi.symm, matrix.zero_mul] },
  { simp }
end)

lemma matrix_eq_sum_mul_single [semiring R] [decidable_eq n] (M : matrix m n R) :
  M = finset.univ.sum (λ j : n, M ⬝ (single j j).to_matrix) :=
by letI := classical.dec_eq m; exact mul_single_ext' punit (begin
  assume j,
  simp only [matrix.sum_mul, single_mul_single],
  rw [finset.sum_eq_single j],
  { simp [matrix.mul_assoc] },
  { assume _ _ hbj,
    rw [matrix.mul_assoc, single_mul_single_of_ne hbj, matrix.mul_zero] },
  { simp }
end)

@[simp] lemma univ_unique {α : Type*} [unique α] [f : fintype α] : @finset.univ α _ = {default α} :=
by rw [subsingleton.elim f (@unique.fintype α _)]; refl

lemma mul_eq_smul [comm_semiring R] {M : matrix n one R} (a : matrix one one R) :
  M ⬝ a = a (default one) (default one) • M :=
begin
  ext i j,
  rw unique.eq_default j,
  simp [matrix.mul, mul_comm]
end

set_option class.instance_max_depth 100
def linear_equiv_linear_map (m n one : Type u) (R : Type v) [fintype m] [fintype n]
  [unique one] [fintype one] [decidable_eq one] [comm_ring R] [decidable_eq m] [decidable_eq n] :
  matrix m n R ≃ₗ[R] ((matrix n one R) →ₗ[R] (matrix m one R)) :=
{ to_fun := λ A,
  { to_fun := λ x, A ⬝ x,
    add := matrix.mul_add A,
    smul := matrix.mul_smul A },
  inv_fun := λ f, finset.univ.sum
    (λ j : n, f (single j (default one)).to_matrix ⬝
        (single (default one) j).to_matrix),
  left_inv := λ A, begin
      conv_rhs {rw [matrix_eq_sum_mul_single A]},
      dsimp, simp [matrix.mul_assoc],
    end,
  right_inv := λ f, linear_map.ext $ λ v, begin
      dsimp,
      rw [matrix.sum_mul],
      simp only [matrix.mul_assoc, mul_eq_smul, (f.map_smul _ _).symm, finset.sum_hom f],
      simp only [(mul_eq_smul _).symm],
      conv_rhs { rw [matrix_eq_sum_single_mul v] },
      simp,
    end,
  add := by simp only [matrix.add_mul]; intros; refl,
  smul := λ f g, linear_map.ext $ λ x, by dsimp; simp only [matrix.smul_mul]; refl }

lemma linear_equiv_linear_map_comp [comm_ring R] [decidable_eq m] [decidable_eq n] [decidable_eq o]
  {M : matrix m n R} {N : matrix n o R} :
  (linear_equiv_linear_map m o one R).to_equiv (M ⬝ N) =
  ((linear_equiv_linear_map m n one R).to_equiv M).comp
    ((linear_equiv_linear_map n o one R).to_equiv N) :=
linear_map.ext $ matrix.mul_assoc M N

lemma linear_equiv_linear_map_one [comm_ring R] [decidable_eq n] :
  (linear_equiv_linear_map n n one R).to_equiv (1 : matrix n n R) = linear_map.id :=
linear_map.ext matrix.one_mul

def ring_equiv_linear_map (n one : Type u) (R : Type v) [fintype n]
  [unique one] [fintype one] [decidable_eq one] [comm_ring R] [decidable_eq n] :
  matrix n n R ≃r ((matrix n one R) →ₗ[R] (matrix n one R)) :=
{ hom :=
  { map_add := (linear_equiv_linear_map n n one R).add,
    map_mul := @linear_equiv_linear_map_comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    map_one := @linear_equiv_linear_map_one _ _ _ _ _ _ _ _ _ },
  ..linear_equiv_linear_map n n one R }

/-- the same as row free if `R` is a field -/
def has_right_inverse [semiring R] [decidable_eq m] (M : matrix m n R) : Prop :=
∃ N : matrix n m R, M ⬝ N = 1

/-- the same as column free if `R` is a field -/
def has_left_inverse [semiring R] [decidable_eq n] (M : matrix m n R) : Prop :=
∃ N : matrix n m R, N ⬝ M = 1

lemma has_left_inverse_one [semiring R] [decidable_eq n] : (1 : matrix n n R).has_left_inverse :=
⟨1, matrix.one_mul 1⟩

lemma has_right_inverse_one [semiring R] [decidable_eq n] : (1 : matrix n n R).has_right_inverse :=
⟨1, matrix.one_mul 1⟩

lemma has_left_inverse_mul [semiring R] [decidable_eq m] [decidable_eq n] {M : matrix l m R}
  {N : matrix m n R} (hM : M.has_left_inverse) : N.has_left_inverse ↔ (M ⬝ N).has_left_inverse :=
let ⟨Mi, hMi⟩ := hM in
⟨λ ⟨Ni, hNi⟩, ⟨Ni ⬝ Mi, by rw [matrix.mul_assoc, ← Mi.mul_assoc, hMi, matrix.one_mul, hNi]⟩,
  λ ⟨MNi, hMNi⟩, ⟨MNi ⬝ M, by rw [matrix.mul_assoc, hMNi]⟩⟩

lemma has_right_inverse_mul [semiring R] [decidable_eq l] [decidable_eq m] {M : matrix l m R}
  {N : matrix m n R} (hN : N.has_right_inverse) : M.has_right_inverse ↔ (M ⬝ N).has_right_inverse :=
let ⟨Ni, hNi⟩ := hN in
⟨λ ⟨Mi, hMi⟩, ⟨Ni ⬝ Mi, by rw [M.mul_assoc, ← N.mul_assoc, hNi, matrix.one_mul, hMi]⟩,
  λ ⟨MNi, hMNi⟩, ⟨N ⬝ MNi, by rw [← matrix.mul_assoc, hMNi]⟩⟩

lemma mul_eq_one_comm [discrete_field R] [decidable_eq n] {M N : matrix n n R} :
  M ⬝ N = 1 ↔ N ⬝ M = 1 :=
by rw [← matrix.mul_eq_mul, ← matrix.mul_eq_mul,
  ← (ring_equiv_linear_map n punit R).to_equiv.injective.eq_iff,
  ← (ring_equiv_linear_map n punit R).to_equiv.injective.eq_iff,
  is_ring_hom.map_mul (ring_equiv_linear_map n punit R).to_equiv,
  is_ring_hom.map_one (ring_equiv_linear_map n punit R).to_equiv,
  linear_map.mul_eq_one_comm,
  ← is_ring_hom.map_mul (ring_equiv_linear_map n punit R).to_equiv,
  ← is_ring_hom.map_one (ring_equiv_linear_map n punit R).to_equiv]

lemma has_right_inverse_iff_has_left_inverse [discrete_field R] [decidable_eq n]
  {M : matrix n n R} : has_right_inverse M ↔ has_left_inverse M :=
by simp [has_left_inverse, has_right_inverse, mul_eq_one_comm]

lemma mul_right_inj [semiring R] [decidable_eq m] {L M : matrix l m R} {N : matrix m n R}
  (hN : N.has_right_inverse) : L ⬝ N = M ⬝ N ↔ L = M :=
let ⟨I, hI⟩ := hN in
⟨λ h, by rw [← L.mul_one, ← hI, ← matrix.mul_assoc, h, matrix.mul_assoc, hI, matrix.mul_one],
  λ h, by rw h⟩

lemma mul_left_inj [semiring R] [decidable_eq m] {L : matrix l m R} {M N : matrix m n R}
  (hL : L.has_left_inverse) : L ⬝ M = L ⬝ N ↔ M = N :=
let ⟨I, hI⟩ := hL in
⟨λ h, by rw [← M.one_mul, ← hI, matrix.mul_assoc, h, ← matrix.mul_assoc, hI, matrix.one_mul],
  λ h, by rw h⟩

def write [decidable_eq m] [decidable_eq n] (A : matrix m n R) (i : m) (j : n) (x : R) :
  matrix m n R
| i' j' := if i' = i ∧ j' = j then x else A i' j'

@[simp] lemma write_apply [decidable_eq m] [decidable_eq n] (A : matrix m n R) (i : m) (j : n)
  (x : R) : (A.write i j x) i j = x :=
if_pos ⟨rfl, rfl⟩

lemma write_apply_of_ne [decidable_eq m] [decidable_eq n] (A : matrix m n R) {i i' : m} {j j' : n}
  (h : i' ≠ i ∨ j' ≠ j) (x : R) : (A.write i j x) i' j' = A i' j' :=
if_neg (not_and_distrib.2 h)

def write_row [decidable_eq m] (A : matrix m n R) (i : m) (x : n → R) :
  matrix m n R
| i' j := if i = i' then x j else A i' j

def write_column [decidable_eq n] (A : matrix m n R) (j : n) (x : m → R) :
  matrix m n R
| i j' := if j = j' then x i else A i j'

@[simp] lemma write_row_apply_of_eq [decidable_eq m] (A : matrix m n R) (i : m)
  (j : n) (x : n → R) : (A.write_row i x) i j = x j :=
if_pos rfl

@[simp] lemma write_column_apply_of_eq [decidable_eq n] (A : matrix m n R) (i : m)
  (j : n) (x : m → R) : (A.write_column j x) i j = x i :=
if_pos rfl

lemma write_row_apply [decidable_eq m] (A : matrix m n R) {i i' : m}
  (j : n) (x : n → R) : (A.write_row i x) i' j = ite (i = i') (x j) (A i' j) := rfl

lemma write_column_apply [decidable_eq n] (A : matrix m n R) (i : m) (j j' : n)
  (x : m → R) : (A.write_column j x) i j' = ite (j = j') (x i) (A i j') := rfl

lemma write_row_apply_of_ne [decidable_eq m] (A : matrix m n R) {i i' : m} (h : i ≠ i')
  (j : n) (x : n → R) : (A.write_row i x) i' j = A i' j := dif_neg h

lemma write_column_apply_of_ne [decidable_eq n] (A : matrix m n R) {j j' : n} (h : j ≠ j') (i : m)
  (x : m → R) : (A.write_column j x) i j' = A i j' := dif_neg h

section inverse

variables [discrete_field R]

/-- noncomputable inverse function for square matrices,
  returns `0` for noninvertible matrices -/
noncomputable def inverse (M : matrix n n R) : matrix n n R :=
by classical; exact if h : has_left_inverse M then classical.some h else 0

lemma inverse_mul [decidable_eq n] {M : matrix n n R} (h : M.has_left_inverse) : inverse M ⬝ M = 1 :=
begin
  rw [inverse, dif_pos],
  swap,
  convert h,
  convert classical.some_spec h, funext, congr
end

/-- false with current inverse definition. True when `M` is square -/
lemma mul_inverse [decidable_eq n] {M : matrix n n R} (h : M.has_right_inverse) :
  M ⬝ inverse M = 1 :=
by rw [mul_eq_one_comm, inverse_mul (has_right_inverse_iff_has_left_inverse.1 h)]

lemma mul_inverse_rev [decidable_eq n] {M : matrix n n R} {N : matrix n n R}
  (hM : M.has_left_inverse) (hN : N.has_left_inverse) :
  inverse (M ⬝ N) = inverse N ⬝ inverse M :=
by rw [← mul_left_inj hN, ← matrix.mul_assoc,
  mul_inverse (has_right_inverse_iff_has_left_inverse.2 hN), matrix.one_mul,
  ← mul_left_inj hM, mul_inverse (has_right_inverse_iff_has_left_inverse.2 hM),
  ← matrix.mul_assoc, mul_inverse
  (has_right_inverse_iff_has_left_inverse.2 ((has_left_inverse_mul hM).1 hN))]

lemma inverse_has_right_inverse [decidable_eq n] {M : matrix n n R} (h : M.has_left_inverse) :
  M.inverse.has_right_inverse :=
⟨_, inverse_mul h⟩

lemma inverse_has_left_inverse [decidable_eq n] {M : matrix n n R} (h : M.has_right_inverse) :
  M.inverse.has_left_inverse :=
⟨_, mul_inverse h⟩

lemma eq_inverse_of_mul_eq_one [decidable_eq n] {M N : matrix n n R} (h : M ⬝ N = 1) :
  M = inverse N :=
by rw [← matrix.one_mul (inverse N), ← h, matrix.mul_assoc, mul_inverse
    (has_right_inverse_iff_has_left_inverse.2 ⟨_, h⟩), matrix.mul_one]

@[simp] lemma inverse_one [decidable_eq n] : inverse (1 : matrix n n R) = 1 :=
(eq_inverse_of_mul_eq_one (matrix.one_mul 1)).symm

@[simp] lemma inverse_zero : inverse (0 : matrix n n R) = 0 :=
by letI := classical.dec_eq n; exact
if h01 : (0 : matrix n n R) = 1
then (eq_inverse_of_mul_eq_one $ by rw [h01, matrix.one_mul]).symm
else begin
  rw [inverse, dif_neg],
  rintros ⟨M, h⟩,
  rw [matrix.mul_zero] at h,
  apply h01, convert h
end

end inverse

-- lemma minor_mul [ring R] (M : matrix m n R) (N : matrix n o R) (row : l → m) :
--   minor M row id ⬝ N = minor (M ⬝ N) row id := rfl

-- lemma mul_minor [ring R] {M : matrix m n R} {N : matrix n l R} (col : o → l) :
--   M ⬝ minor N id col = minor (M ⬝ N) id col := rfl

-- lemma minor_eq_mul_minor_one [ring R] [decidable_eq m] [decidable_eq n] (M : matrix m n R)
--   (row : l → m) : minor M row id = minor 1 row id ⬝ M :=
-- by rw [minor_mul, M.one_mul]

-- lemma minor_eq_minor_one_mul [ring R] [decidable_eq m] [decidable_eq n] (M : matrix m n R)
--   (col : o → n) : minor M id col = M ⬝ minor 1 id col :=
-- by rw [mul_minor, M.mul_one]

-- lemma transpose_diagonal [has_zero R] [decidable_eq n] (d : n → R) :
--   (diagonal d)ᵀ = diagonal d :=
-- by ext; dsimp [diagonal, transpose]; split_ifs; cc

-- @[simp] lemma transpose_one [has_zero R] [has_one R] [decidable_eq n] :
--   (1 : matrix n n R)ᵀ = 1 := transpose_diagonal _

-- lemma transpose_minor [ring R] [decidable_eq m] [decidable_eq n] (M : matrix m n R)
--   (row : l → m) (col : o → n) : (minor M row col)ᵀ = minor Mᵀ col row := rfl

-- lemma minor_minor {k l m n o p : Type u} [fintype k] [fintype l] [fintype m] [fintype n]
--   [fintype o] [fintype p] (M : matrix m n R)
--   (row₁ : l → m) (row₂ : k → l) (col₁ : o → n) (col₂ : p → o) :
--   minor (minor M row₁ col₁) row₂ col₂ = minor M (row₁ ∘ row₂) (col₁ ∘ col₂) := rfl

-- lemma minor_diagonal_eq_diagonal [has_zero R] [decidable_eq m] [decidable_eq n]
--   {f : m → n} (hf : injective f) (d : n → R) : minor (diagonal d) f f = diagonal (d ∘ f) :=
-- by ext; simp [diagonal, minor, hf.eq_iff]; congr

-- lemma minor_one_eq_one [has_zero R] [has_one R] [decidable_eq m] [decidable_eq n]
--   {f : m → n} (hf : injective f) : minor (1 : matrix n n R) f f = 1 :=
-- minor_diagonal_eq_diagonal hf _

-- open finset

-- lemma minor_one_mul_transpose_eq_one [ring R] [decidable_eq n] [decidable_eq m] {f : m → n}
--   (hf : injective f) : minor (1 : matrix n n R) f id ⬝ (minor 1 f id)ᵀ = 1 :=
-- by rw [minor_mul, transpose_minor, mul_minor, transpose_one, matrix.one_mul, minor_minor];
--   exact minor_one_eq_one hf

-- lemma transpose_mul_minor_one_eq_diagonal [ring R] [decidable_eq n] [decidable_eq m] {f : m → n}
--   (hf : injective f) : (minor (1 : matrix n n R) f id)ᵀ ⬝ (minor (1 : matrix n n R) f id) =
--   diagonal (λ i, if i ∈ set.range f then 1 else 0) :=
-- begin
--   ext i j,
--   dsimp [transpose_minor, transpose_one, minor, minor, matrix.mul, diagonal, transpose, one_val],
--   by_cases hi : i ∈ set.range f,
--   { cases id hi with k hk,
--     rw [sum_eq_single k];
--     simp [hk.symm, hi, -set.mem_range, hf.eq_iff] {contextual := tt}; try {congr} },
--   { rw [sum_eq_zero, if_neg hi]; simp * at * }
-- end

-- lemma transpose_mul_minor_one_eq_diagonal [ring R] [decidable_eq n] [decidable_eq m]
--   {f : m → n} {g : l → n} (hf : injective f) (hg : injective g) :
--   (minor (1 : matrix n n R) f id) ⬝ (minor (1 : matrix n n R) g id)ᵀ =
--   diagonal (λ i, if i ∈ set.range f then 1 else 0) :=


-- lemma tranpose_mul_minor_one_add_transpose_mul_minor_one
--   [ring R] [decidable_eq l] [decidable_eq m] [decidable_eq n] {f : m → n} {g : l → n}
--   (hf : injective f) (hg : injective g) (hfg : ∀ i, i ∈ set.range f ∪ set.range g)
--   (hd : disjoint (set.range f) (set.range g)):
--   (minor (1 : matrix n n R) f id)ᵀ ⬝ (minor (1 : matrix n n R) f id) +
--   (minor (1 : matrix n n R) g id)ᵀ ⬝ (minor (1 : matrix n n R) g id) = 1 :=
-- matrix.ext $ λ i j, begin
--   have : i ∈ set.range f → i ∈ set.range g → false,
--     from λ hf hg, set.disjoint_iff.1 hd ⟨hf, hg⟩,
--   have := hfg i,
--   rw [transpose_mul_minor_one_eq_diagonal hf, transpose_mul_minor_one_eq_diagonal hg,
--     diagonal_add, diagonal],
--   dsimp only,
--   split_ifs;
--   simp * at *
-- end

-- local attribute [instance] finsupp.add_comm_group finsupp.module

-- def finsupp_equiv_cvec [ring R] [decidable_eq R] [decidable_eq m] :
--   (m →₀ R) ≃ₗ[R] matrix m one R :=
-- { to_fun := λ x i _, x i,
--   inv_fun := λ v, finsupp.equiv_fun_on_fintype.2 (λ i, v i £),
--   left_inv := λ _, finsupp.ext (λ _, rfl),
--   right_inv := λ _, cvec.ext (λ _, rfl),
--   add := λ x y, rfl,
--   smul := λ c x, rfl }

-- def to_lin' (one : Type u) [unique one] [comm_ring R] (A : matrix m n R) :
--   matrix n one R →ₗ[R] matrix m one R :=
-- { to_fun := (⬝) A,
--   add := matrix.mul_add _,
--   smul := matrix.mul_smul _, }

-- def is_invertible [comm_ring R] : Prop :=
-- bijective (A.to_lin' punit : matrix n punit R → matrix m punit R)

def one_by_one_equiv (one R : Type*) [unique one] [ring R] [decidable_eq one] :
  matrix one one R ≃ R :=
{ to_fun := λ M, M (default _) (default _),
  inv_fun := λ x _ _, x,
  left_inv := λ _, matrix.ext
    (λ i j, by rw [unique.eq_default i, unique.eq_default j]),
  right_inv := λ _, rfl }

lemma one_by_one_equiv.is_ring_hom (one R : Type*) [unique one] [decidable_eq one] [ring R] :
  is_ring_hom (one_by_one_equiv one R) :=
{ map_one := if_pos rfl,
  map_add := λ _ _, rfl,
  map_mul := λ _ _, by dsimp [one_by_one_equiv, matrix.mul]; simp }

instance [comm_ring R] : comm_ring (matrix one one R) :=
{ mul_comm := λ a b, show a ⬝ b = b ⬝ a, from
    matrix.ext $ λ i j, by rw [unique.eq_default i, unique.eq_default j];
      simp [matrix.mul]; exact mul_comm _ _,
  ..matrix.ring }

/- should be changed once there is a computable matrix inverse -/
instance [discrete_field R] : discrete_field (matrix one one R) :=
have mul_inv : ∀ (M : matrix one one R), M ≠ 0 →
    (λ i j, M i j) ⬝ (λ i j, (M i j)⁻¹) = 1,
  begin
    assume M h,
    ext i j,
    have h : M (default one) (default one) ≠ 0,
      from λ hM, h (matrix.ext $ λ i j, by convert hM),
    rw [unique.eq_default i, unique.eq_default j],
    simp [matrix.mul, mul_inv_cancel h],
  end,
{ mul := (*),
  inv := λ M i j, (M i j)⁻¹,
  zero_ne_one := mt (matrix.ext_iff).2 (λ h, absurd (h (default one) (default one)) $
    by rw [matrix.one_val, if_pos rfl]; exact zero_ne_one),
  mul_inv_cancel := mul_inv,
  inv_mul_cancel := λ M h, eq.trans (mul_comm _ _) (mul_inv M h),
  has_decidable_eq := by apply_instance,
  inv_zero := matrix.ext $ λ _ _, inv_zero,
  ..matrix.comm_ring }

section matrix_order
variables {α : Type*}

def matrix.partial_order [partial_order α] :
  partial_order (matrix m n α) := pi.partial_order

def matrix.ordered_comm_group [ordered_comm_group α] :
  ordered_comm_group (matrix m n α) :=
pi.ordered_comm_group

local attribute [instance] matrix.partial_order matrix.ordered_comm_group

lemma matrix.mul_nonneg [ordered_semiring α] {M : matrix m n α}
  {N : matrix n o α} (hM : 0 ≤ M) (hN : 0 ≤ N) : 0 ≤ M ⬝ N :=
λ i j, by classical; exact finset.zero_le_sum' (λ _ _, mul_nonneg (hM _ _) (hN _ _))

lemma matrix.mul_nonpos_of_nonpos_of_nonneg [ordered_semiring α] {M : matrix m n α}
  {N : matrix n o α} (hM : M ≤ 0) (hN : 0 ≤ N) : M ⬝ N ≤ 0 :=
λ i j, by classical; exact finset.sum_le_zero'
  (λ _ _, mul_nonpos_of_nonpos_of_nonneg (hM _ _) (hN _ _))

lemma pequiv_nonneg [decidable_eq m] [decidable_eq n] [linear_ordered_semiring α] (f : pequiv m n) :
  (0 : matrix _ _ α) ≤ f.to_matrix :=
λ i j, by rw [pequiv.to_matrix]; split_ifs; [exact zero_le_one, exact le_refl _]

def matrix.decidable_le [partial_order α] [decidable_rel ((≤) : α → α → Prop)] :
  decidable_rel ((≤) : Π a b : matrix m n α, Prop) :=
λ M N, show decidable (∀ i j, M i j ≤ N i j), by apply_instance

lemma le_iff_single_mul_le [decidable_eq l] [decidable_eq m] [decidable_eq n]
  [linear_ordered_semiring R] (x : l) (a b : matrix m n R) : a ≤ b ↔
  (∀ i : m, (single x i).to_matrix ⬝ a ≤ (single x i).to_matrix ⬝ b) :=
show (∀ i j, a i j ≤ b i j) ↔
  (∀ i j k, ((single x i).to_matrix ⬝ a) j k ≤ ((single x i).to_matrix ⬝ b) j k),
begin
  simp only [mul_matrix_apply],
  split,
  { intros h i j k,
    dsimp [single], split_ifs,
    { rw if_pos h_1, exact h _ _ },
    { rw if_neg h_1 } },
  { intros h i j,
    convert h i x j;
    dsimp [single]; rw [if_pos rfl] }
end

lemma le_iff_mul_single_le [decidable_eq l] [decidable_eq m] [decidable_eq n]
  [linear_ordered_semiring R] (x : l) (a b : matrix m n R) : a ≤ b ↔
  (∀ j : n, a ⬝ (single j x).to_matrix ≤ b ⬝ (single j x).to_matrix) :=
show (∀ i j, a i j ≤ b i j) ↔
  (∀ (j : n) (i k), (a ⬝ (single j x).to_matrix) i k ≤ (b ⬝ (single j x).to_matrix) i k),
begin
  simp only [matrix_mul_apply],
  split,
  { intros h i j k,
    dsimp [single, pequiv.symm], split_ifs,
    { rw if_pos h_1, exact h _ _ },
    { rw if_neg h_1 } },
  { intros h i j,
    convert h j i x;
    dsimp [single, pequiv.symm]; rw [if_pos rfl] }
end

lemma one_by_one_lt_iff [partial_order α] {a b : matrix one one α} : a < b ↔
  a (default one) (default one) < b (default one) (default one) :=
begin
  simp only [lt_iff_le_not_le],
  show (∀ i j, a i j ≤ b i j) ∧ (¬ ∀ i j, b i j ≤ a i j) ↔ _,
  simp [unique.forall_iff],
end

instance [decidable_linear_order α] : decidable_linear_order (matrix one one α) :=
{ le_total := λ a b, (le_total (a (default one) (default one)) (b (default one) (default one))).elim
    (λ hab, or.inl $ λ i j, by rw [unique.eq_default i, unique.eq_default j]; exact hab)
    (λ hba, or.inr $ λ i j, by rw [unique.eq_default i, unique.eq_default j]; exact hba),
  decidable_le := matrix.decidable_le,
  ..matrix.partial_order }

instance [discrete_linear_ordered_field R] : discrete_linear_ordered_field
  (matrix one one R) :=
{ mul_nonneg := λ a b ha0 hb0 i j, by simp [matrix.mul];
    exact mul_nonneg (ha0 _ _) (hb0 _ _),
  mul_pos := λ a b ha0 hb0,
    begin
      rw [one_by_one_lt_iff] at *,
      simp [matrix.mul],
      exact mul_pos ha0 hb0
    end,
  one := 1,
  zero_lt_one := one_by_one_lt_iff.2 $ by rw [one_val, if_pos rfl]; exact zero_lt_one,
  ..matrix.discrete_field,
  ..matrix.ordered_comm_group,
  ..matrix.decidable_linear_order }

lemma inv_def [discrete_field R] (a : matrix one one R) :
  a⁻¹ = (λ _ _, (a (default one) (default one))⁻¹) :=
by ext i j; rw [unique.eq_default i, unique.eq_default j]; refl

end matrix_order

lemma mul_right_eq_of_mul_eq [semiring R] {M : matrix l m R} {N : matrix m n R} {O : matrix l n R}
  {P : matrix n o R} (h : M ⬝ N = O) : M ⬝ (N ⬝ P) = O ⬝ P :=
by classical; rw [← matrix.mul_assoc, h]

lemma inv_eq_inverse [discrete_field R] (a : matrix one one R) : a⁻¹ = inverse a :=
if ha : a = 0 then by simp [ha]
else eq_inverse_of_mul_eq_one (by rw [← matrix.mul_eq_mul, inv_mul_cancel ha]; congr)

lemma one_by_one_mul_inv_cancel {M : matrix one one ℚ} (hM : M ≠ 0) :
  M ⬝ inverse M = 1 :=
by rw [← matrix.mul_eq_mul, ← inv_eq_inverse, mul_inv_cancel hM]

lemma one_by_one_inv_mul_cancel {M : matrix (fin 1) (fin 1) ℚ} (hM : M ≠ 0) :
  inverse M ⬝ M = 1 :=
by rw [← matrix.mul_eq_mul, ← inv_eq_inverse, inv_mul_cancel hM]

end
end matrix
open pequiv

lemma mul_single_ext {R : Type*} {m n : ℕ} [semiring R]
  {A B : matrix (fin m) (fin n) R} (h : ∀ j : fin n, A ⬝ (single j (0 : fin 1)).to_matrix = B ⬝
    (single j (0 : fin 1)).to_matrix) : A = B :=
by ext i j; simpa [matrix_mul_apply] using congr_fun (congr_fun (h j) i) 0

lemma single_mul_ext {R : Type*} {m n : ℕ} [semiring R]
  {A B : matrix (fin m) (fin n) R} (h : ∀ i, (single (0 : fin 1) i).to_matrix ⬝ A =
    (single (0 : fin 1) i).to_matrix ⬝ B) : A = B :=
by ext i j; simpa [mul_matrix_apply] using congr_fun (congr_fun (h i) 0) j
