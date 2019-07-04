import data.matrix
import data.rat
import data.set data.set.enumerate data.set.finite data.finset

variables {α : Type} {n m l s t : Type} [fintype n] [fintype m] [fintype s] [fintype t]

variables {n1 n2 : nat}

section matrix
def le [partial_order α] (M N : matrix n m α)  :=
∀i:n, ∀j:m, M i j ≤ N i j

instance [partial_order α] : has_le (matrix n m α) :=
{ le := le }

protected lemma matrix.le_refl [partial_order α] (A: matrix n m α) :
A ≤ A :=
by intros i j; refl

protected lemma matrix.le_trans [partial_order α] (a b c: matrix n m α)
  (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c :=
by intros i j; transitivity; solve_by_elim

protected lemma matrix.le_antisymm [partial_order α] (a b: matrix n m α)
  (h1 : a ≤ b) (h2 : b ≤ a) : a = b :=
by ext i j; exact le_antisymm (h1 i j) (h2 i j)

instance [partial_order α] : partial_order (matrix n m α) :=
{
  le := le,
  le_refl := matrix.le_refl,
  le_trans := matrix.le_trans,
  le_antisymm := matrix.le_antisymm
}
end matrix

local infixl ` *ₘ ` : 70 := matrix.mul

def polyhedron [ordered_ring α] (A : matrix m n α) (b : matrix m unit α) :
  set (matrix n unit α) :=
{ x : matrix n unit α | A *ₘ x ≥ b }

def vec (n: Type) (α : Type) [fintype n] :=
n → α

instance [ordered_ring α] [decidable_rel ((≤) : α → α → Prop)]
  (A : matrix m n α) (b : matrix m unit α) (x : matrix n unit α) :
  decidable (x ∈ polyhedron A b) :=
show decidable (∀i:m, ∀j:unit, b i j ≤ (A *ₘ x) i j),
  by apply_instance

variables [ordered_ring α] (A B : matrix m n α) (b : matrix m unit α)

protected def matrix.row (A : matrix m n α) (row : m) : matrix unit n α :=
λ x: unit, λ y: n, (A row) y

lemma polyhedron_rowinE [ordered_ring α]
        (x: matrix n unit α) (A: matrix m n α) (b: matrix m unit α):
    x ∈ (polyhedron A b) = ∀ i:m, (matrix.row4
     A i *ₘ x) () () ≥ b i () :=

propext $ iff.intro
  (assume h: x ∈ (polyhedron A b),
   assume d: m,
   show (matrix.row A d *ₘ x) () () ≥ b d (),
   begin
     rw polyhedron at h,
     rw set.mem_set_of_eq at h,
     exact h d ()
   end
  )
  (assume h: ∀ i:m, (matrix.row A i *ₘ x) () () ≥ b i (),
   show x ∈ (polyhedron A b),
   begin
   assume d : m,
   assume j : unit,
   rw <-(≥),
   cases j,
   apply h,
   end
  )

def active_ineq [ordered_ring α] (x: matrix n unit α)
    (A: matrix m n α) (b: matrix m unit α) : set m :=
{ i | ((A *ₘ x) i () == b i ())}