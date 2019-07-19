import data.matrix .matrix_pequiv

variables {K : Type*} [discrete_field K]

def row_reduce : Π {m n : ℕ} (A : matrix (fin m) (fin n) K), matrix (fin m) (fin n) K
| 0 0    A := A 
| (n+1)  A := _
