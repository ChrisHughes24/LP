import data.matrix

def fmatrix (m : ℕ) (n : ℕ) (R : Type*) := array (m * n) R

variables {R : Type*} [semiring R] {l m n : ℕ}

instance : has_add (fmatrix m n R) := ⟨array.map₂ (+)⟩
instance : has_zero (fmatrix m n R) := ⟨mk_array _ 0⟩

lemma add_def (a b : fmatrix m n R) : a + b = a.map₂ (+) b := rfl

namespace d_array

universes u v

variables {α : fin n → Type u} {β : Type v}

def foreach_aux (a : d_array n α) (f : Π i : fin n, α i → α i)
  (i : ℕ) (hi : i ≤ n) : d_array n α :=
a.iterate_aux (λ i v (a' : d_array n α), a'.write i (f i v)) i hi a

lemma foreach_aux_succ (a : d_array n α) (f : Π i : fin n, α i → α i)
  (i : ℕ) (hi : (i + 1) ≤ n) :
a.foreach_aux f (i + 1) hi = (a.foreach_aux f i (nat.le_of_succ_le hi)).write
  ⟨i, hi⟩ (f _ (a.read _)) := rfl

lemma read_foreach_aux (a : d_array n α) (f : Π i : fin n, α i → α i) :
 Π (i : ℕ) (hi : i ≤ n) (j : ℕ) (hj : j < i),
  (a.foreach_aux f i hi).read ⟨j, lt_of_lt_of_le hj hi⟩ =
    f ⟨j, lt_of_lt_of_le hj hi⟩ (a.read _)
| 0 hi j hj := (nat.not_lt_zero _ hj).elim
| (i+1) hi j hj :=
  if hij : i = j
    then begin
        subst hij,
        erw [foreach_aux_succ, read_write],
        refl
      end
    else
    have j < i, from lt_of_le_of_ne (nat.le_of_lt_succ hj) (ne.symm hij),
    by rw [foreach_aux_succ, read_write_of_ne _ _
      (show fin.mk i hi ≠ ⟨j, _⟩, from fin.ne_of_vne hij), read_foreach_aux _ _ _ this]

@[simp] lemma read_foreach (a : d_array n α)( f : Π i : fin n, α i → α i) (i : fin n) :
  read (a.foreach f) i = f i (a.read i) :=
by cases i with i hi; exact read_foreach_aux a f n (le_refl n) i hi

end d_array


namespace fmatrix

def fin.pair (i : fin m) (j : fin n) : fin (m * n) :=
⟨j + n * i,
  calc ((j : ℕ) + n * i) + 1 = i * n + (j + 1) : by simp [mul_comm, add_comm]
  ... ≤ i * n + n : add_le_add (le_refl _) j.2
  ... = (i + 1) * n : by simp [add_mul]
  ... ≤ m * n : mul_le_mul i.2 (le_refl _) (nat.zero_le _) (nat.zero_le _)⟩

def fin.unpair₁ (x : fin (m * n)) : fin m :=
⟨x / n, nat.div_lt_of_lt_mul (mul_comm m n ▸ x.2)⟩

def fin.unpair₂ (x : fin (m * n)) : fin n :=
⟨x % n, nat.mod_lt _ (nat.pos_of_ne_zero (λ hn0, by rw [hn0, mul_zero] at x; exact x.elim0))⟩

@[simp] lemma fin.pair_unpair (x : fin (m * n)) : fin.pair (fin.unpair₁ x) (fin.unpair₂ x) = x :=
fin.eq_of_veq (nat.mod_add_div _ _)

@[simp] lemma fin.unpair₁_pair (i : fin m) (j : fin n) : fin.unpair₁ (fin.pair i j) = i :=
fin.eq_of_veq $ show ((j : ℕ) + n * i) / n = i,
  by erw [nat.add_mul_div_left _ _ (lt_of_le_of_lt (nat.zero_le _) j.2),
    nat.div_eq_of_lt j.2, zero_add]

@[simp] lemma fin.unpair₂_pair (i : fin m) (j : fin n) : fin.unpair₂ (fin.pair i j) = j :=
fin.eq_of_veq $ show ((j : ℕ) + n * i) % n = j,
  by erw [nat.add_mul_mod_self_left, nat.mod_eq_of_lt j.2]; refl

def read (M : fmatrix m n R) (i : fin m) (j : fin n) : R :=
array.read M (fin.pair i j)

def write (M : fmatrix m n R) (i : fin m) (j : fin n) : R → fmatrix m n R :=
array.write M (fin.pair i j)

def mul (M : fmatrix l m R) (N : fmatrix m n R) : fmatrix l n R :=
(0 : fmatrix l n R).foreach (λ x _,
  let i := fin.unpair₁ x in
  let k := fin.unpair₂ x in
  finset.univ.sum (λ j : fin m, M.read i j * N.read j k))

@[simp] lemma array.read_foreach {n : ℕ} {α : Type*} (x : array n α)
  (f : Π i : fin n, α → α) (i : fin n) :
  (x.foreach f).read i = f i (x.read i) :=
d_array.read_foreach x _ _

def to_matrix (a : fmatrix m n R) : matrix (fin m) (fin n) R := a.read

def equiv_matrix : fmatrix m n R ≃ matrix (fin m) (fin n) R :=
{ to_fun := fmatrix.read,
  inv_fun := λ M, (0 : fmatrix m n R).foreach (λ x _, M (fin.unpair₁ x) (fin.unpair₂ x)),
  left_inv := λ M, by ext; simp [fmatrix.read],
  right_inv := λ M, by ext; simp [fmatrix.read] }

lemma to_matrix_add (a b : fmatrix m n R) : (a + b).to_matrix = a.to_matrix + b.to_matrix :=
by ext; simp [to_matrix, fmatrix.read, add_def, array.map₂]

lemma to_matrix_mul (a : fmatrix l m R) (b : fmatrix m n R) : (a.mul b).to_matrix =
  a.to_matrix.mul b.to_matrix :=
by ext; simp [to_matrix, matrix.mul, fmatrix.mul, fmatrix.read]

end fmatrix
