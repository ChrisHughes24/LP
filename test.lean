import simplex

open tableau finset
variables {m n : ℕ}

def list.to_matrix (m :ℕ) (n : ℕ) (l : list (list ℚ)) : matrix (fin m) (fin n) ℚ :=
λ i j, (l.nth_le i sorry).nth_le j sorry

def vector.to_matrix (m :ℕ) (n : ℕ) (l : vector (vector ℚ n) m) : matrix (fin m) (fin n) ℚ:=
λ i j, (l.nth i).nth j

instance has_repr_fin_fun {n : ℕ} {α : Type*} [has_repr α] : has_repr (fin n → α) :=
⟨λ f, repr (vector.of_fn f).to_list⟩

def matrix.to_vector (A : matrix (fin m) (fin n) ℚ) :  vector (vector ℚ n) m :=
(vector.of_fn A).map (λ v, (vector.of_fn v))

instance {m n} : has_repr (matrix (fin m) (fin n) ℚ) := has_repr_fin_fun

def T : tableau 25 10 :=
{ to_matrix := list.to_matrix 25 10
  [[0, 0, 0, 0, 1, 0, 1, 0, 1, -1], [-1, 1, 0, -1, 1, 0, 1, -1, 0, 0],
    [0, -1, 1, 1, 1, 0, 0, 0, 1, 0], [1, 1, 1, 0, 1, -1, 1, -1, 1, -1],
    [0, 1, 1, -1, -1, 1, -1, 1, -1, 1], [0, -1, 1, -1, 1, 1, 0, 1, 0, -1],
    [-1, 0, 0, -1, -1, 1, 1, 0, -1, -1], [-1, 0, 0, -1, 0, -1, 0, 0, -1, 1],
    [-1, 0, 0, 1, -1, 1, -1, -1, 1, 0], [1, 0, 0, 0, 1, -1, 1, 0, -1, 1],
    [0, -1, 1, 0, 0, 1, 0, -1, 0, 0], [-1, 1, -1, 1, 1, 0, 1, 0, 1, 0],
    [1, 1, 1, 1, -1, 0, 0, 0, -1, 0], [-1, -1, 0, 0, 1, 0, 1, 1, -1, 0],
    [0, 0, -1, 1, -1, 0, 0, 1, 0, -1], [-1, 0, -1, 1, 1, 1, 0, 0, 0, 0],
    [1, 0, -1, 1, 0, -1, -1, 1, -1, 1], [-1, 1, -1, 1, -1, -1, -1, 1, -1, 1],
    [-1, 0, 0, 0, 1, -1, 1, -1, -1, 1], [-1, -1, -1, 1, 0, 1, -1, 1, 0, 0],
    [-1, 0, 0, 0, -1, -1, 1, -1, 0, 1], [-1, 0, 0, -1, 1, 1, 1, -1, 1, 0],
    [0, -1, 0, 0, 0, -1, 0, 1, 0, -1], [1, -1, 1, 0, 0, 1, 0, 1, 0, -1],
    [0, -1, -1, 0, 0, 0, -1, 0, 1, 0]],
  const := λ i _, 1,
  to_partition := default _,
  restricted := univ,
  dead := ∅ }

set_option trace.compiler.code_gen true
set_option profiler true
#eval let l := ((list.fin_range 10).product (list.fin_range 25)).bind
  (λ i : fin 10 × fin 25, if T.to_matrix i.1 i.2 = 0 then [] else [(T.pivot i.1 i.2).to_matrix])
  in (l.length, l)

def s := let s := T.simplex (λ _, tt) 0 dec_trivial in
(s.1.const, s.1.to_partition.row_indices.1, s.2)

#eval s
