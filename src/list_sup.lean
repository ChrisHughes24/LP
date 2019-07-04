import data.list.basic order.lattice data.list.min_max tactic.tauto

open lattice

namespace list
variables {α : Type*} {β : Type*} [decidable_linear_order β] [inhabited α]


instance order_dual.inhabited {α : Type*} : Π [inhabited α], inhabited (order_dual α) := id

lemma min_eq_max_order_dual : @min β _ = @max (order_dual β) _ :=
funext $ λ a, funext $ λ b,
  le_antisymm (le_min_iff.2
    ⟨@le_max_left (order_dual β) _ _ _, @le_max_right (order_dual β) _ _ _⟩)
  ((@max_le_iff (order_dual β) _ _ _ _).2
    ⟨min_le_left _ _, min_le_right _ _⟩)

lemma list.minimum_eq_maximum_order_dual [inhabited β] :
  @list.minimum β _ _ = @list.maximum (order_dual β) _ _ :=
by ext; rw [list.minimum, min_eq_max_order_dual]; refl

def argmax (f : α → β) (l : list α) : α :=
l.foldl (λ max a, if f max ≤ f a then a else max) l.head

def argmin : Π (f : α → β) (l : list α), α :=
@argmax _ (order_dual β) _ _

@[simp] lemma argmax_nil (f : α → β) : argmax f [] = default α := rfl

@[simp] lemma argmin_nil (f : α → β) : argmin f [] = default α := rfl

@[simp] lemma map_nil {α β : Type*} (f : α → β) : list.map f [] = [] := rfl

@[simp] lemma map_eq_nil {α β : Type*} {f : α → β} {l : list α} :
  list.map f l = [] ↔ l = [] :=
⟨by cases l; simp, λ h, h.symm ▸ map_nil _⟩

lemma argmax_eq_maximum_of_ne_nil [inhabited β] (l : list α) : ∀ (f : α → β) (hl : l ≠ []),
  f (argmax f l) = list.maximum (l.map f) :=
list.reverse_rec_on l (λ _ h, (h rfl).elim)
  (λ l a ih f hl, by classical; exact
    if hl : l = [] then by simp [hl, argmax]
    else
    begin
      have : map f l ≠ [], from mt map_eq_nil.1 hl,
      simp only [argmax, maximum, foldl_append, foldl_cons, foldl_nil,
        map_append, map_cons, map_nil, head_append _ hl,
        head_append _ this, max] at ⊢ ih,
      rw [← ih _ hl],
      split_ifs; refl
    end)

lemma argmin_eq_minimum_of_ne_nil [inhabited β] : ∀ (l : list α) (f : α → β) (hl : l ≠ []),
  f (argmin f l) = list.minimum (l.map f) :=
by rw [list.minimum_eq_maximum_order_dual];
  exact @argmax_eq_maximum_of_ne_nil _ (order_dual β) _ _ _

@[simp] lemma argmax_singleton (f : α → β) (a : α) : argmax f [a] = a :=
by simp [argmax, foldl_cons, foldl_nil]

@[simp] lemma argmin_singleton (f : α → β) (a : α) : argmin f [a] = a :=
@argmax_singleton _ (order_dual β) _ _ _ _

lemma argmax_cons (f : α → β) : Π {l : list α} (hl : l ≠ []) (a : α),
  argmax f (a :: l) = if f (argmax f l) ≤ f a then a else argmax f l
| []       hl a := (hl rfl).elim
| (b :: l) _  a := begin
  rw [argmax, foldl_cons],
  simp [-foldl_cons],

end

lemma argmax_mem (f : α → β) {l : list α} (hl : l ≠ []) : argmax f l ∈ l :=
suffices f (argmax f l) ∈ l.map f,
  by rw [mem_map] at this; tauto

end list
