import .refactor_iterate logic.relator .transfer_mathlib

def fmatrix (m n : ℕ) := array m (array n ℚ)

variables {m n : ℕ}

namespace matrix

def read (A : matrix (fin m) (fin n) ℚ) (i : fin m) (j : fin n) : ℚ := A i j

def write (A : matrix (fin m) (fin n) ℚ) (i : fin m) (j : fin n) (a : ℚ) :=
λ i' j', if i' = i ∧ j'  = j then a else A.read i j

@[irreducible] def of_fun (A : fin m → fin n → ℚ) := A

def zero : matrix (fin m) (fin n) ℚ := 0

end matrix

namespace tableau

def pivot' : Π (T : tableau m n) (r : fin m) (c : fin n), tableau m n :=
λ T r c,
let p := (T.to_matrix.read r c)⁻¹ in
{ to_matrix := matrix.of_fun (λ i j,
    if i = r
      then if j = c
        then p
        else -T.to_matrix.read r j * p
      else if j = c
        then T.to_matrix.read i c * p
        else T.to_matrix.read i j - T.to_matrix.read i c * T.to_matrix.read r j * p),
  to_partition := T.to_partition.swap r c,
  offset := matrix.of_fun $ λ i k,
    if i = r
      then -T.offset.read r k * p
      else T.offset.read i k - T.to_matrix.read i c * T.offset.read r k * p,
  restricted := T.restricted }

end tableau


namespace equiv
variables {α : Sort*} {β : Sort*}

def rel (e : α ≃ β) (a : α) (b : β) : Prop := e a = b

end equiv

namespace fmatrix

def read (A : fmatrix m n) (i : fin m) (j : fin n) : ℚ :=
(array.read A i).read j

def to_matrix (A : fmatrix m n) : matrix (fin m) (fin n) ℚ := sorry

def zero : fmatrix m n := sorry

/-- maybe this can be replaced with matrix.to_fmatrix -/
@[irreducible] def of_fun (A : fin m → fin n → ℚ) : fmatrix m n :=
sorry

end fmatrix


def matrix.to_fmatrix (A : fin m → fin n → ℚ) : fmatrix m n := sorry

def equiv_matrix : matrix (fin m) (fin n) ℚ ≃ fmatrix m n :=
{ to_fun := matrix.to_fmatrix,
  inv_fun := fmatrix.to_matrix,
  left_inv := sorry,
  right_inv := sorry }

#check ((@equiv_matrix m n).rel ⇒ (eq : Π a b : fin n, Prop) )
#where
lemma read_rel :
  ((@equiv_matrix m n).rel ⇒ eq ⇒ eq ⇒ eq) matrix.read fmatrix.read := sorry

lemma eq_to_equiv_matrix.rel : ((eq ⇒ eq ⇒ eq) ⇒
  (@equiv_matrix m n).rel) matrix.of_fun fmatrix.of_fun := sorry

lemma equiv_matrix_rel : ((@equiv_matrix m n).rel ⇒ (@equiv_matrix m n).rel ⇒ iff) eq eq := sorry

lemma zero_rel : (@equiv_matrix m n).rel matrix.zero fmatrix.zero := sorry

#print array
open fmatrix

structure ftableau (m n : ℕ) :=
(to_fmatrix : fmatrix m n)
(offset : fmatrix m 1)
(to_partition : partition m n)
(restricted : finset (fin (m + n)))

def equiv_tableau : tableau m n ≃ ftableau m n :=
{ to_fun := λ ⟨M, O, P, R⟩, ⟨equiv_matrix.to_fun M, equiv_matrix.to_fun O, P, R⟩,
  inv_fun := λ ⟨M, O, P, R⟩, ⟨equiv_matrix.inv_fun M, equiv_matrix.inv_fun O, P, R⟩,
  left_inv := sorry,
  right_inv := sorry }

lemma to_matrix_rel : ((@equiv_tableau m n).rel ⇒ equiv_matrix.rel)
  tableau.to_matrix ftableau.to_fmatrix := sorry

lemma offset_rel : ((@equiv_tableau m n).rel ⇒ (@equiv_matrix m 1).rel)
  tableau.offset ftableau.offset := sorry

lemma to_partition_rel : ((@equiv_tableau m n).rel ⇒ eq)
  tableau.to_partition ftableau.to_partition := sorry

lemma restricted_rel : ((@equiv_tableau m n).rel ⇒ eq)
  tableau.restricted ftableau.restricted := sorry

lemma mk_rel : ((@equiv_matrix m n).rel ⇒ (@equiv_matrix m 1).rel ⇒ eq ⇒ eq ⇒
  (@equiv_tableau m n).rel) tableau.mk ftableau.mk := sorry

lemma equiv_tableau_rel : ((@equiv_tableau m n).rel ⇒ (@equiv_tableau m n).rel ⇒ iff) eq eq := sorry

namespace ftableau

def pivot' : Π (T : ftableau m n) (r : fin m) (c : fin n), ftableau m n :=
λ T r c,
let p := (T.to_fmatrix.read r c)⁻¹ in
{ to_fmatrix := matrix.to_fmatrix (λ i j,
    if i = r
      then if j = c
        then p
        else -T.to_fmatrix.read r j * p
      else if j = c
        then T.to_fmatrix.read i c * p
        else T.to_fmatrix.read i j - T.to_fmatrix.read i c * T.to_fmatrix.read r j * p),
  to_partition := T.to_partition.swap r c,
  offset := matrix.to_fmatrix $ λ i k,
    if i = r
      then -T.offset.read r k * p
      else T.offset.read i k - T.to_fmatrix.read i c * T.offset.read r k * p,
  restricted := T.restricted }

end ftableau
#where
#print read_rel
#print has_to_tactic_format
#print list.to_string

attribute [irreducible] matrix.read matrix.of_fun matrix.zero
  tableau.to_matrix tableau.offset tableau.to_partition tableau.restricted
  -- ftableau.to_matrix tableau.offset tableau.to_partition tableau.restricted tableau.mk

lemma fin_zero_rel {n : ℕ} : (0 : fin (n + 1)) = 0 := rfl

instance bi_total_equiv {α β} (e : α ≃ β) : relator.bi_total e.rel := sorry
-- lemma fin_zero_rel {n : ℕ} : (0 : fin (n + 1)) = 0

lemma equiv_matrix_rel2 : (eq ⇒ eq ⇒ iff) (@equiv_matrix m n).rel equiv_matrix.rel := sorry

lemma tableau_equiv_rel2 : (eq ⇒ eq ⇒ iff) (@equiv_tableau m n).rel equiv_tableau.rel

run_cmd do rds ← transfer.analyse_decls
  [ ``read_rel,``zero_rel, ``fin_zero_rel],
    rds_fmt ← rds.mmap has_to_tactic_format.to_tactic_format,
    tactic.trace (((rds_fmt.map to_string).intersperse "; ").to_string),
  transfer.compute_transfer rds [] `((eq (@matrix.read 3 2 (matrix.zero) 0 0)))
#print rel_forall_of_total
lemma pivot_rel :
  (equiv_tableau.rel ⇒ eq ⇒ eq ⇒ equiv_tableau.rel) (@tableau.pivot' m n) ftableau.pivot' :=
begin
  dunfold tableau.pivot' ftableau.pivot',
  transfer.transfer
  [``equiv_matrix_rel2, `tableau_equiv_rel2, `relator.rel_forall_of_total, `to_matrix_rel, `offset_rel, `to_partition_rel, `restricted_rel, `mk_rel,
    `read_rel, `eq_to_equiv_matrix.rel, `equiv_matrix_rel, `equiv_tableau_rel],

end

-- def pivot : { p : Π (T : ftableau m n) (r : fin m) (c : fin n), ftableau m n //
--   (equiv_tableau.rel ⇒ eq ⇒ eq ⇒ equiv_tableau.rel) tableau.pivot' p } :=
-- begin
--   dunfold tableau.pivot',
--   refine ⟨_, _⟩, swap,
--   { transfer.transfer [`to_matrix_rel, `offset_rel, `to_partition_rel, `restricted_rel, `mk_rel,
--     `read_rel, `eq_to_equiv_matrix.rel, `equiv_matrix_rel] },

-- end


end ftableau

-- open matrix fintype finset function pequiv

-- local notation `rvec`:2000 n := matrix (fin 1) (fin n) ℚ
-- local notation `cvec`:2000 m := matrix (fin m) (fin 1) ℚ
-- local infix ` ⬝ `:70 := matrix.mul
-- local postfix `ᵀ` : 1500 := transpose

-- structure tableau' (m n : ℕ) :=
-- (to_matrix : matrix (fin m) (fin n) ℚ)
-- (offset : cvec m)
-- (to_partition : partition m n)
-- (restricted : finset (fin (m + n)))
