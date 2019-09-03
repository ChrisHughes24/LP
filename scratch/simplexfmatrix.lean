import .simplex_new_pivot .fmatrix

namespace fmatrix
open pequiv simplex
variables {m n : ℕ}

def pivot_element (B : prebasis m n) (A_bar : fmatrix m n) (r : fin m) (s : fin (n - m)) : ℚ :=
A_bar.read r (B.nonbasisg s)

def choose_pivot_row (B : prebasis m n) (A_bar : fmatrix m n) (b_bar : fmatrix m 1)
  (c : fmatrix 1 n) (s : fin (n - m)) : option (fin m) :=
fin.find (λ r : fin m,
  0 < pivot_element B A_bar r s ∧
  ∀ i : fin m, 0 < pivot_element B A_bar i s) →
    ratio B A_bar b_bar r s ≤ ratio B A_bar b_bar i s)

def simplex : Π (B : prebasis m n) (A_bar : fmatrix m n) (b_bar : fmatrix m 1) (c : fmatrix 1 n)

end fmatrix
