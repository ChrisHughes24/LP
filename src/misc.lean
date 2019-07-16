import data.matrix tactic.fin_cases linear_algebra.determinant .matrix_pequiv

local infix ` ⬝ `:70 := matrix.mul
local postfix `ᵀ` : 1500 := matrix.transpose

universes u v w

namespace matrix

section
variables {l m n o : Type u} [fintype l] [fintype m] [fintype n] [fintype o]
variables {one : Type u} [unique one]

open function

local notation `£` := default _

-- @[reducible] def cvec (R : Type*) (m : ℕ) := matrix (fin m) (fin 1) R
-- @[reducible] def rvec (R : Type*) (n : ℕ) := matrix (fin 1) (fin n) R

variables {R : Type*}
variables (A M : matrix m n R)
variables (b : matrix m one R) (c x : matrix n one R)

@[extensionality] lemma cvec.ext {x y : matrix m one R}
  (h : ∀ i, x i £ = y i £) : x = y :=
matrix.ext (λ i j, by fin_cases j; exact h _)

@[extensionality] lemma rvec.ext {x y : matrix one n R}
 (h : ∀ j, x £ j = y £ j) : x = y :=
matrix.ext (λ i j, by fin_cases i; exact h _)

/-- the same as row free if `R` is a field -/
def has_right_inverse [ring R] [decidable_eq m] (M : matrix m n R) : Prop :=
∃ N : matrix n m R, M ⬝ N = 1

/-- the same as column free if `R` is a field -/
def has_left_inverse [ring R] [decidable_eq n] (M : matrix m n R) : Prop :=
∃ N : matrix n m R, N ⬝ M = 1

lemma has_left_inverse_one [ring R] [decidable_eq n] : (1 : matrix n n R).has_left_inverse :=
⟨1, matrix.one_mul 1⟩

lemma has_right_inverse_one [ring R] [decidable_eq n] : (1 : matrix n n R).has_right_inverse :=
⟨1, matrix.one_mul 1⟩

lemma has_left_inverse_mul [ring R] [decidable_eq m] [decidable_eq n] {M : matrix l m R}
  {N : matrix m n R} (hM : M.has_left_inverse) : N.has_left_inverse ↔ (M ⬝ N).has_left_inverse :=
let ⟨Mi, hMi⟩ := hM in
⟨λ ⟨Ni, hNi⟩, ⟨Ni ⬝ Mi, by rw [matrix.mul_assoc, ← Mi.mul_assoc, hMi, matrix.one_mul, hNi]⟩,
  λ ⟨MNi, hMNi⟩, ⟨MNi ⬝ M, by rw [matrix.mul_assoc, hMNi]⟩⟩

lemma has_right_inverse_iff_has_left_inverse [integral_domain R] [decidable_eq n]
  {M : matrix n n R} : has_left_inverse M ↔ has_right_inverse M := sorry

lemma mul_right_inj [ring R] [decidable_eq m] {L M : matrix l m R} {N : matrix m n R}
  (hN : N.has_right_inverse) : L ⬝ N = M ⬝ N ↔ L = M :=
let ⟨I, hI⟩ := hN in
⟨λ h, by rw [← L.mul_one, ← hI, ← matrix.mul_assoc, h, matrix.mul_assoc, hI, matrix.mul_one],
  λ h, by rw h⟩

lemma mul_left_inj [ring R] [decidable_eq m] {L : matrix l m R} {M N : matrix m n R}
  (hL : L.has_left_inverse) : L ⬝ M = L ⬝ N ↔ M = N :=
let ⟨I, hI⟩ := hL in
⟨λ h, by rw [← M.one_mul, ← hI, matrix.mul_assoc, h, ← matrix.mul_assoc, hI, matrix.one_mul],
  λ h, by rw h⟩
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

def to_lin' (one : Type u) [unique one] [comm_ring R] (A : matrix m n R) :
  matrix n one R →ₗ[R] matrix m one R :=
{ to_fun := (⬝) A,
  add := matrix.mul_add _,
  smul := matrix.mul_smul _, }

def is_invertible [comm_ring R] : Prop :=
bijective (A.to_lin' punit : matrix n punit R → matrix m punit R)

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

-- def one_by_one_ring_equiv (one R : Type*) [unique one] [ring R] [decidable_eq one] :
--   matrix one one R ≃r R :=
-- { hom := one_by_one_equiv.is_ring_hom one R,
--   ..one_by_one_equiv one R }


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

end matrix_order

lemma mul_right_eq_of_mul_eq [semiring R] {M : matrix l m R} {N : matrix m n R} {O : matrix l n R}
  {P : matrix n o R} (h : M ⬝ N = O) : M ⬝ (N ⬝ P) = O ⬝ P :=
by classical; rw [← matrix.mul_assoc, h]

end


section inverse
variables {l m n : ℕ} {}

def comatrix (M : matrix (fin n) (fin n) ℚ) : matrix (fin n) (fin n) ℚ :=
begin
  cases n,
  { exact fin.elim0 },
  { exact λ i j, (-1) ^ (i + j : ℕ) * det (minor M
      (λ i' : fin n, if i'.1 < i.1 then i'.cast_succ
        else i'.succ)
      (λ j' : fin n, if j'.1 < j.1 then j'.cast_succ
        else j'.succ)) }
end

def inverse (M : matrix (fin m) (fin n) ℚ) : matrix (fin n) (fin m) ℚ :=
if h : m = n then by subst h; exact (det M)⁻¹ • (comatrix M)ᵀ else 0
#eval inverse (λ i j : fin 1, 0) 0 0
/-- false with current inverse definition. True when `M` is square -/
lemma inverse_mul {M : matrix (fin m) (fin n) ℚ} (h : M.has_left_inverse) :
  inverse M ⬝ M = 1 := sorry

/-- false with current inverse definition. True when `M` is square -/
lemma mul_inverse {M : matrix (fin m) (fin n) ℚ} (h : M.has_right_inverse) :
  M ⬝ inverse M = 1 := sorry

lemma mul_inverse_rev {M : matrix (fin l) (fin m) ℚ} {N : matrix (fin m) (fin n) ℚ}
  (hM : M.has_left_inverse) (hN : N.has_left_inverse) :
  inverse (M ⬝ N) = inverse N ⬝ inverse M := sorry

lemma inverse_has_right_inverse {M : matrix (fin m) (fin n) ℚ} (h : M.has_left_inverse) :
  M.inverse.has_right_inverse :=
⟨_, inverse_mul h⟩

lemma inverse_has_left_inverse {M : matrix (fin m) (fin n) ℚ} (h : M.has_right_inverse) :
  M.inverse.has_left_inverse :=
⟨_, mul_inverse h⟩

@[simp] lemma inverse_one : inverse (1 : matrix (fin n) (fin n) ℚ) = 1 := sorry

lemma mul_eq_one_comm {M N : matrix (fin n) (fin n) ℚ} :
  M ⬝ N = 1 ↔ N ⬝ M = 1 := sorry

instance : discrete_field (matrix (fin 1) (fin 1) ℚ) :=
{ inv := inverse,
  zero_ne_one := mt (matrix.ext_iff).2 (λ h, absurd (h 0 0) dec_trivial),
  mul_inv_cancel := sorry,
  inv_mul_cancel := sorry,
  has_decidable_eq := by apply_instance,
  mul_comm := sorry,
  inv_zero := dec_trivial,
  ..matrix.ring }

lemma inverse_eq_inv (a : matrix (fin 1) (fin 1) ℚ) : inverse a = a⁻¹ := rfl

lemma one_by_one_mul_inv_cancel {M : matrix (fin 1) (fin 1) ℚ} (hM : M ≠ 0) :
  M ⬝ inverse M = 1 := sorry

lemma one_by_one_inv_mul_cancel {M : matrix (fin 1) (fin 1) ℚ} (hM : M ≠ 0) :
  inverse M ⬝ M = 1 := sorry

end inverse

end matrix




section lex

variables {α : Type*} {β : Type*}

instance (r : α → α → Prop) (s : β → β → Prop) [decidable_eq α]
  [decidable_rel r] [decidable_rel s] : decidable_rel (prod.lex r s) :=
λ a b, if hr : r a.1 b.1
  then is_true (by cases a; cases b; exact prod.lex.left _ _ _ hr)
  else if heq : a.1 = b.1
    then if hs : s a.2 b.2
      then is_true (by cases a; cases b; cases heq; exact prod.lex.right _ _ hs)
      else is_false (λ h, begin
        cases h with a₁ b₁ a₂ b₂ hr' a₁ b₁ b₂ hs',
        { exact hr hr' },
        { exact hs hs' },
      end)
    else is_false (λ h, begin
        cases h with a₁ b₁ a₂ b₂ hr' a₁ b₁ b₂ hs',
        { exact hr hr' },
        { exact heq rfl }
      end)

end lex

lemma array.mem_decidable {α : Type*} [decidable_eq α] {n : ℕ} {a : array n α} :
  decidable_pred (∈ a) :=
λ _, show decidable ∃ _, _, by apply_instance

namespace vector
variables {α : Type*} [decidable_eq α] {n : ℕ}

def update_nth (a : α) (i : fin n) (v : vector α n) : vector α n :=
⟨v.to_list.update_nth i a, by erw [list.update_nth_length, v.2]⟩

@[simp] lemma nth_update_nth (a : α) (i : fin n) (v : vector α n) :
  (v.update_nth a i).nth i = a :=
option.some_inj.1 (by rw [update_nth, nth, ← list.nth_le_nth];
  convert list.nth_update_nth_of_lt a (show (i : ℕ) < v.1.length, from v.2.symm ▸ i.2))

lemma nth_update_nth_of_ne {i j : fin n} (v : vector α n) (h : i ≠ j) (a : α) :
  (v.update_nth a i).nth j = v.nth j :=
by cases v; erw [← option.some_inj, update_nth, nth, ← list.nth_le_nth,
    list.nth_update_nth_ne _ _ (fin.vne_of_ne h), nth, ← list.nth_le_nth]; refl

end vector
