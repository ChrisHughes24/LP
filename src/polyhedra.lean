import .misc data.matrix .simplex tactic.fin_cases linear_algebra.matrix

#eval (encodable.choose)

import linear_algebra.dimension data.finsupp
#print prod.map
universes u v w

variables {m n k : Type u} [fintype m] [fintype n] [fintype k]
variables {one : Type u} [unique one]
variables {R : Type*} [discrete_linear_ordered_field R]
variables (A : matrix m n R)
open matrix

variables (x c : cvec R n) (b : cvec R m)

local notation M `⬝`:70 N := M.mul N
local postfix `ᵀ` : 1500 := transpose

section

variables {ι : Type*} {ι' : Type*} {α : Type*} {β : Type*} {γ : Type*} {δ : Type*} {v : ι → β}

variables [ring α] [add_comm_group β] [add_comm_group γ] [add_comm_group δ]
variables [module α β] [module α γ] [module α δ]

variables (α) (v)

local attribute [instance] finsupp.add_comm_group finsupp.module

end

local attribute [instance] finsupp.add_comm_group finsupp.module

def polyhedron : set (cvec R n) := { x | b ≤ A ⬝ x }

def dual_polyhedron : set (cvec R m) := { u | Aᵀ ⬝ u = c ∧ 0 ≤ u }

lemma row_mul (B : matrix n k R) (i) :
  (row' A one i ⬝ B) = row' (A ⬝ B) one i := rfl

lemma polyhedron_row_inE :
  x ∈ polyhedron A b ↔ ∀ i, b i 0 ≤ (row' A i ⬝ x) 0 0 :=
⟨λ h i, h _ _, λ h i j, by fin_cases j; apply h⟩

def active_ineq : set (fin m) :=
{i | (A ⬝ x) i 0 = b i 0}

/-- called feasible_dir in Coq paper -/
def unbounded_dir := { d : cvec R n | 0 ≤ A ⬝ d }

def pointed : Prop := n ≤ A.rank



lemma not_pointed_iff : ¬ pointed A ↔ ∃ d, d ≠ 0 ∧
  (d : cvec R n) ∈ unbounded_dir A ∧ (-d) ∈ unbounded_dir A :=
have ¬ pointed A ↔ ∃ y : cvec R n, y ∈ linear_map.ker A.to_lin' ∧ y ≠ 0,
  begin
    rw [pointed, ← rank_transpose, row_le_rank_iff (Aᵀ), row_free], sorry,
  end,
begin
  rw this,
  simp only [unbounded_dir, linear_map.mem_ker, set.mem_set_of_eq,
    mul_neg, neg_zero, neg_nonneg],
  split,
  { rintros ⟨y, yker, y0⟩,
    exact ⟨y, y0, le_of_eq yker.symm, le_of_eq yker⟩ },
  { rintros ⟨d, d0, ubd, ubnd⟩,
    exact ⟨d, le_antisymm ubnd ubd, d0⟩ }
end
