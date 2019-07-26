import data.matrix data.array.lemmas data.rat.basic

def fmatrix (m : ℕ) (n : ℕ) := array (m * n) ℚ

namespace fmatrix

variables {l m n : ℕ}

instance : has_add (fmatrix m n) := ⟨array.map₂ (+)⟩
instance : has_zero (fmatrix m n) := ⟨mk_array _ 0⟩

lemma add_def (a b : fmatrix m n) : a + b = a.map₂ (+) b := rfl

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

lemma fin.pair_eq_pair {i i' : fin m} {j j' : fin n} :
  fin.pair i j = fin.pair i' j' ↔ i' = i ∧ j' = j :=
⟨λ h, ⟨by rw [← fin.unpair₁_pair i j, h, fin.unpair₁_pair],
       by rw [← fin.unpair₂_pair i j, h, fin.unpair₂_pair]⟩,
  λ ⟨hi, hj⟩, by rw [hi, hj]⟩

def read (A : fmatrix m n) (i : fin m) (j : fin n) : ℚ :=
array.read A (fin.pair i j)

def write (A : fmatrix m n) (i : fin m) (j : fin n) : ℚ → fmatrix m n :=
array.write A (fin.pair i j)

@[extensionality] lemma ext {A B : fmatrix m n} (h : ∀ i j, A.read i j = B.read i j) : A = B :=
array.ext $ λ x, by simpa [fmatrix.read] using h (fin.unpair₁ x) (fin.unpair₂ x)

@[simp] lemma read_write (A : fmatrix m n) (i : fin m) (j : fin n) (x : ℚ) :
  (A.write i j x).read i j = x :=
array.read_write _ _ _

lemma read_write_of_ne (A : fmatrix m n) {i i' : fin m} {j j': fin n} (x : ℚ)
  (h : i' ≠ i ∨ j' ≠ j) : (A.write i j x).read i' j' = A.read i' j' :=
array.read_write_of_ne _ _ (by rwa [ne.def, fin.pair_eq_pair, not_and_distrib])

def foreach_aux (A : fmatrix m n) (f : fin m → fin n → ℚ → ℚ) :
  Π (i : ℕ) (j : ℕ) (hi : i ≤ m) (hj : j ≤ n), fmatrix m n
| 0     j     := λ hi hj, A
| (i+1) 0     := λ hi hj, foreach_aux i n (nat.le_of_succ_le hi) (le_refl _)
| (i+1) (j+1) := λ hi hj, (foreach_aux (i+1) j hi (nat.le_of_succ_le hj)).write
  ⟨i, hi⟩ ⟨j, hj⟩ (f ⟨i, hi⟩ ⟨j, hj⟩ (A.read ⟨i, hi⟩ ⟨j, hj⟩))

def foreach (A : fmatrix m n) (f : fin m → fin n → ℚ → ℚ) : fmatrix m n :=
foreach_aux A f m n (le_refl _) (le_refl _)

lemma read_foreach_aux (A : fmatrix m n) (f : fin m → fin n → ℚ → ℚ) :
  Π (i : ℕ) (j : ℕ) (hi : i ≤ m) (hj : j ≤ n) (i' : fin m) (j' : fin n)
  (hij' : i'.1 + 1 < i ∨ (i'.1 + 1 = i ∧ j'.1 < j)),
  (A.foreach_aux f i j hi hj).read i' j' = f i' j' (A.read i' j')
| 0     j     := λ hi hj i' j' hij', hij'.elim (λ hi', (nat.not_lt_zero _ hi').elim)
  (λ hij', (nat.succ_ne_zero _ hij'.1).elim)
| (i+1) 0     := λ hi hj i' j' hij',
  hij'.elim
  (λ hi', begin
      rw [foreach_aux, read_foreach_aux],
      cases lt_or_eq_of_le (nat.le_of_lt_succ hi') with hi' hi',
      { exact or.inl hi' },
      { exact or.inr ⟨hi', j'.2⟩ }
    end)
  (λ hij', (nat.not_lt_zero _ hij'.2).elim)
| (i+1) (j+1) := λ hi hj i' j' hij',
  begin
    rw [foreach_aux], dsimp only,
    by_cases hij : i' = ⟨i, hi⟩ ∧ j' = ⟨j, hj⟩,
    { rw [hij.1, hij.2, read_write] },
    { rw not_and_distrib at hij,
      rw [read_write_of_ne _ _ hij, read_foreach_aux],
      cases hij' with hi' hij',
      { exact or.inl hi' },
      { exact or.inr ⟨hij'.1, lt_of_le_of_ne (nat.le_of_lt_succ hij'.2)
          (fin.vne_of_ne (hij.resolve_left (not_not_intro (fin.eq_of_veq
            (nat.succ_inj hij'.1)))))⟩ } }
  end

@[simp] lemma read_foreach (A : fmatrix m n) (f : fin m → fin n → ℚ → ℚ) (i : fin m)
  (j : fin n) : (A.foreach f).read i j = f i j (A.read i j) :=
read_foreach_aux _ _ _ _ _ _ _ _ ((lt_or_eq_of_le (nat.succ_le_of_lt i.2)).elim
  or.inl (λ hi, or.inr ⟨hi, j.2⟩))

def to_matrix (A : fmatrix m n) : matrix (fin m) (fin n) ℚ
| i j := A.read i j

def of_matrix (A : matrix (fin m) (fin n) ℚ) : fmatrix m n :=
(0 : fmatrix m n).foreach (λ i j _, A i j)

@[simp] lemma to_matrix_of_matrix (A : matrix (fin m) (fin n) ℚ) :
  (of_matrix A).to_matrix = A :=
by ext; simp [to_matrix, of_matrix]

@[simp] lemma of_matrix_to_matrix (A : fmatrix m n) : of_matrix A.to_matrix = A :=
by ext; simp [of_matrix, to_matrix]

def mul (B : fmatrix l m) (C : fmatrix m n) : fmatrix l n :=
let s : finset (fin m) := finset.univ in
(0 : fmatrix l n).foreach
  (λ i j _, s.sum (λ k : fin m, B.read i k * C.read k j))

instance : has_mul (fmatrix n n) := ⟨mul⟩

instance : has_one (fmatrix n n) :=
⟨(0 : fmatrix n n).foreach (λ i j _, _)⟩

instance : has_le (fmatrix m n) := ⟨λ A B, ∀ i, array.read A i ≤ array.read B i⟩

instance : decidable_rel ((≤) : fmatrix m n → fmatrix m n → Prop) :=
λ A B, show decidable (∀ i, array.read A i ≤ array.read B i), by apply_instance

def mul₂ (M : fmatrix l m) (N : fmatrix m n) : fmatrix l n :=
array.foreach (0 : fmatrix l n) (λ x _,
  let i := fin.unpair₁ x in
  let k := fin.unpair₂ x in
  finset.univ.sum (λ j : fin m, M.read i j * N.read j k))

def equiv_matrix : fmatrix m n ≃ matrix (fin m) (fin n) ℚ :=
{ to_fun := to_matrix,
  inv_fun :=  of_matrix,
  left_inv := of_matrix_to_matrix,
  right_inv := to_matrix_of_matrix }

lemma to_matrix_add (A B : fmatrix m n) : (A + B).to_matrix = A.to_matrix + B.to_matrix :=
by ext; simp [to_matrix, fmatrix.read, add_def, array.read_map₂]

lemma to_matrix_mul (A : fmatrix l m) (B : fmatrix m n) : (A.mul B).to_matrix =
  A.to_matrix.mul B.to_matrix :=
by ext; simp [to_matrix, matrix.mul, fmatrix.mul]

end fmatrix

-- #eval (fmatrix.mul (show fmatrix 50 50 ℚ, from ((list.range 2500).map nat.cast).to_array))
--   (show fmatrix 50 50 ℚ, from ((list.range 2500).map nat.cast).to_array))

-- #eval let m := 213 in let n := 100 in
--   let l : array (m * n) ℚ := unchecked_cast (list.to_array (((list.range (m * n)).map
--      (rat.of_int ∘ int.of_nat: ℕ → ℚ)))) in
-- array.to_list
--  (fmatrix.mul(show fmatrix m n, from unchecked_cast l)
--   (show fmatrix n m , from unchecked_cast l))
