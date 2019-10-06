import simplex

class is_tableau (ftableau : ℕ → ℕ → Type) : Type :=
(to_tableau {m n : ℕ} : ftableau m n → tableau m n)
(pivot {m n : ℕ} : ftableau m n → fin m → fin n → ftableau m n)
(pivot_col {m n : ℕ} (T : ftableau m n) (obj : fin m) : option (fin n))
(pivot_row {m n : ℕ} (T : ftableau m n) (obj : fin m) : fin n → option (fin m))
(to_tableau_pivot {m n : ℕ} (T : ftableau m n) (i : fin m) (j : fin n) :
  to_tableau (pivot T i j) = (to_tableau T).pivot i j)
(to_tableau_pivot_col {m n : ℕ} (T : ftableau m n) :
  pivot_col T = (to_tableau T).pivot_col)
(to_tableau_pivot_row {m n : ℕ} (T : ftableau m n) :
  pivot_row T = (to_tableau T).pivot_row)

namespace is_tableau
section
parameters {m n : ℕ} {ftableau : ℕ → ℕ → Type}
variable [is_tableau ftableau]

def to_matrix (T : ftableau m n) : matrix (fin m) (fin n) ℚ :=
(to_tableau T).to_matrix

def const (T : ftableau m n) : matrix (fin m) (fin 1) ℚ :=
(to_tableau T).const

def to_partition (T : ftableau m n) : partition m n :=
(to_tableau T).to_partition

def restricted (T : ftableau m n) : finset (fin (m + n)) :=
(to_tableau T).restricted

def dead (T : ftableau m n) : finset (fin n) :=
(to_tableau T).dead

end
end is_tableau
