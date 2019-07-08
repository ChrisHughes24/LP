import data.equiv.basic data.set.lattice tactic.tauto
universes u v w x

structure pequiv (α : Type u) (β : Type v) :=
(to_fun : α → option β)
(inv_fun : β → option α)
(inv : ∀ (a : α) (b : β), a ∈ inv_fun b ↔ b ∈ to_fun a)

namespace pequiv
variables {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}
open function option

instance : has_coe_to_fun (pequiv α β) := ⟨_, to_fun⟩

@[simp] lemma coe_mk_apply (f₁ : α → option β) (f₂ : β → option α) (h) (x : α) :
  (pequiv.mk f₁ f₂ h : α → option β) x = f₁ x := rfl

@[extensionality] lemma ext : ∀ {f g : pequiv α β} (h : ∀ x, f x = g x), f = g
| ⟨f₁, f₂, hf⟩ ⟨g₁, g₂, hg⟩ h :=
have h : f₁ = g₁, from funext h,
have ∀ b, f₂ b = g₂ b,
  begin
    subst h,
    assume b,
    have hf := λ a, hf a b,
    have hg := λ a, hg a b,
    cases h : g₂ b with a,
    { simp only [h, option.not_mem_none, false_iff] at hg,
      simp only [hg, iff_false] at hf,
      rwa [option.eq_none_iff_forall_not_mem] },
    { rw [← option.mem_def, hf, ← hg, h, option.mem_def] }
  end,
by simp [*, funext_iff]

lemma ext_iff {f g : pequiv α β} : f = g ↔ ∀ x, f x = g x :=
⟨congr_fun ∘ congr_arg _, ext⟩

@[refl] protected def refl (α : Type*) : pequiv α α :=
{ to_fun := some,
  inv_fun := some,
  inv := λ _ _, eq_comm }

@[symm] protected def symm (f : pequiv α β) : pequiv β α :=
{ to_fun := f.2,
  inv_fun := f.1,
  inv := λ _ _, (f.inv _ _).symm }

lemma mem_iff_mem (f : pequiv α β) : ∀ {a : α} {b : β}, a ∈ f.symm b ↔ b ∈ f a:= f.3

lemma eq_some_iff (f : pequiv α β) : ∀ {a : α} {b : β}, f.symm b = some a ↔ f a = some b := f.3

@[trans] protected def trans (f : pequiv α β) (g : pequiv β γ) : pequiv α γ :=
{ to_fun := λ a, (f a).bind g,
  inv_fun := λ a, (g.symm a).bind f.symm,
  inv := λ a b, by simp [*, and.comm, eq_some_iff f, eq_some_iff g] at * }

@[simp] lemma refl_apply (a : α) : pequiv.refl α a = some a := rfl

@[simp] lemma symm_refl : (pequiv.refl α).symm = pequiv.refl α := rfl

@[simp] lemma symm_refl_apply (a : α) : (pequiv.refl α).symm a = some a := rfl

@[simp] lemma symm_symm (f : pequiv α β) : f.symm.symm = f := by cases f; refl

@[simp] lemma symm_symm_apply (f : pequiv α β) (a : α) : f.symm.symm a = f a :=
by rw symm_symm

lemma symm_injective : function.injective (@pequiv.symm α β) :=
injective_of_has_left_inverse ⟨_, symm_symm⟩

lemma trans_assoc (f : pequiv α β) (g : pequiv β γ) (h : pequiv γ δ) :
  (f.trans g).trans h = f.trans (g.trans h) :=
ext (λ _, option.bind_assoc _ _ _)

lemma mem_trans (f : pequiv α β) (g : pequiv β γ) (a : α) (c : γ) :
  c ∈ f.trans g a ↔ ∃ b, b ∈ f a ∧ c ∈ g b := option.bind_eq_some'

lemma trans_eq_some (f : pequiv α β) (g : pequiv β γ) (a : α) (c : γ) :
  f.trans g a = some c ↔ ∃ b, f a = some b ∧ g b = some c := option.bind_eq_some'

lemma trans_eq_none (f : pequiv α β) (g : pequiv β γ) (a : α) :
  f.trans g a = none ↔ (∀ b c, b ∉ f a ∨ c ∉ g b) :=
by simp only [eq_none_iff_forall_not_mem, mem_trans]; push_neg; tauto

@[simp] lemma refl_trans (f : pequiv α β) : (pequiv.refl α).trans f = f :=
by ext; dsimp [pequiv.trans]; refl

@[simp] lemma trans_refl (f : pequiv α β) : f.trans (pequiv.refl β) = f :=
by ext; dsimp [pequiv.trans]; simp

@[simp] lemma refl_trans_apply (f : pequiv α β) (a : α) : (pequiv.refl α).trans f a = f a :=
by rw refl_trans

@[simp] lemma trans_refl_apply (f : pequiv α β) (a : α) : f.trans (pequiv.refl β) a = f a :=
by rw trans_refl

protected lemma inj (f : pequiv α β) {a₁ a₂ : α} {b : β} (h₁ : b ∈ f a₁) (h₂ : b ∈ f a₂) : a₁ = a₂ :=
by rw ← mem_iff_mem at *; cases h : f.symm b; simp * at *

lemma injective_of_forall_ne_is_some (f : pequiv α β) (a₂ : α)
  (h : ∀ (a₁ : α), a₁ ≠ a₂ → is_some (f a₁)) : injective f :=
injective_of_has_left_inverse
  ⟨λ b, option.rec_on b a₂ (λ b', option.rec_on (f.symm b') a₂ id),
    λ x, begin
      classical,
      cases hfx : f x,
      { have : x = a₂, from not_imp_comm.1 (h x) (hfx.symm ▸ by simp), simp [this] },
      { simp only [hfx], rw [(eq_some_iff f).2 hfx], refl }
    end⟩

lemma injective_of_forall_is_some {f : pequiv α β}
  (h : ∀ (a : α), is_some (f a)) : injective f :=
(classical.em (nonempty α)).elim
  (λ hn, injective_of_forall_ne_is_some f (classical.choice hn)
    (λ a _, h a))
  (λ hn x, (hn ⟨x⟩).elim)

section of_set
variables (s : set α) [decidable_pred s]

def of_set (s : set α) [decidable_pred s] : pequiv α α :=
{ to_fun := λ a, if a ∈ s then some a else none,
  inv_fun := λ a, if a ∈ s then some a else none,
  inv := λ a b, by split_ifs; finish [eq_comm] }

lemma mem_of_set_self_iff {s : set α} [decidable_pred s] {a : α} : a ∈ of_set s a ↔ a ∈ s :=
by dsimp [of_set]; split_ifs; simp *

lemma mem_of_set_iff {s : set α} [decidable_pred s] {a b : α} : a ∈ of_set s b ↔ a = b ∧ a ∈ s :=
by dsimp [of_set]; split_ifs; split; finish

@[simp] lemma of_set_eq_some_self_iff {s : set α} {h : decidable_pred s} {a : α} :
  of_set s a = some a ↔ a ∈ s := mem_of_set_self_iff

@[simp] lemma of_set_eq_some_iff {s : set α} {h : decidable_pred s} {a b : α} :
  of_set s b = some a ↔ a = b ∧ a ∈ s := mem_of_set_iff

@[simp] lemma of_set_symm : (of_set s).symm = of_set s := rfl

@[simp] lemma of_set_univ : of_set set.univ = pequiv.refl α :=
by ext; dsimp [of_set]; simp [eq_comm]

@[simp] lemma of_set_eq_refl {s : set α} [decidable_pred s] :
  of_set s = pequiv.refl α ↔ s = set.univ :=
⟨λ h, begin
  rw [set.eq_univ_iff_forall],
  intro,
  rw [← mem_of_set_self_iff, h],
  exact rfl
end, λ h, by simp only [of_set_univ.symm, h]; congr⟩

end of_set

lemma symm_trans_rev (f : pequiv α β) (g : pequiv β γ) : (f.trans g).symm = g.symm.trans f.symm := rfl

lemma trans_symm (f : pequiv α β) : f.trans f.symm = of_set {a | (f a).is_some} :=
begin
  ext,
  dsimp [pequiv.trans],
  simp only [eq_some_iff f, option.is_some_iff_exists, option.mem_def, bind_eq_some', of_set_eq_some_iff],
  split,
  { rintros ⟨b, hb₁, hb₂⟩,
    exact ⟨pequiv.inj _ hb₂ hb₁, b, hb₂⟩ },
  { simp {contextual := tt} }
end

lemma symm_trans (f : pequiv α β) : f.symm.trans f = of_set {b | (f.symm b).is_some} :=
symm_injective $ by simp [symm_trans_rev, trans_symm, -symm_symm]

lemma trans_symm_eq_iff_forall_is_some {f : pequiv α β} :
  f.trans f.symm = pequiv.refl α ↔ ∀ a, is_some (f a) :=
by rw [trans_symm, of_set_eq_refl, set.eq_univ_iff_forall]; refl

instance : lattice.has_bot (pequiv α β) :=
⟨{ to_fun := λ _, none,
   inv_fun := λ _, none,
   inv := by simp }⟩

@[simp] lemma bot_apply (a : α) : (⊥ : pequiv α β) a = none := rfl

@[simp] lemma symm_bot : (⊥ : pequiv α β).symm = ⊥ := rfl

@[simp] lemma trans_bot (f : pequiv α β) : f.trans (⊥ : pequiv β γ) = ⊥ :=
by ext; dsimp [pequiv.trans]; simp

@[simp] lemma bot_trans (f : pequiv β γ) : (⊥ : pequiv α β).trans f = ⊥ :=
by ext; dsimp [pequiv.trans]; simp

lemma is_some_symm_get (f : pequiv α β) {a : α} (h : is_some (f a)) :
  is_some (f.symm (option.get h)) :=
is_some_iff_exists.2 ⟨a, by rw [f.eq_some_iff, some_get]⟩

section subsingle
variables [decidable_eq α] [decidable_eq β]

def subsingle (x : option (α × β)) : pequiv α β :=
{ to_fun := λ y, option.bind x (λ z, if y = z.1 then some z.2 else none),
  inv_fun := λ y, option.bind x (λ z, if y = z.2 then some z.1 else none),
  inv := λ _ _, by rcases x with ⟨a, b⟩ | none; simp; split_ifs; cc }

@[simp] lemma symm_subsingle (x : option (α × β)) : (subsingle x).symm = subsingle (x.map prod.swap) :=
by rcases x with ⟨a, b⟩ | none; refl

@[simp] lemma mem_subsingle {a : α} {b : β} {x : option (α × β)} : b ∈ subsingle x a ↔ (a, b) ∈ x :=
by rcases x with none | ⟨x₁, x₂⟩; dsimp [subsingle]; try {split_ifs}; simp; cc

end subsingle

section single
variables [decidable_eq α] [decidable_eq β] [decidable_eq γ]

def single (a : α) (b : β) : pequiv α β :=
{ to_fun := λ x, if x = a then some b else none,
  inv_fun := λ x, if x = b then some a else none,
  inv := λ _ _, by simp; split_ifs; cc }

@[simp] lemma symm_single (a : α) (b : α) : (single a b).symm = single b a := rfl

lemma single_trans_of_mem (a : α) {b : β} {c : γ} {f : pequiv β γ} (h : c ∈ f b) :
  (single a b).trans f = single a c :=
begin
  ext,
  dsimp [single, subsingle, pequiv.trans],
  split_ifs; simp * at *
end

lemma trans_single_of_mem {a : α} {b : β} (c : γ) {f : pequiv α β} (h : b ∈ f a) :
  f.trans (single b c) = single a c :=
symm_injective $ single_trans_of_mem _ ((mem_iff_mem f).2 h)

lemma trans_single_of_eq_none {b : β} (c : γ) {f : pequiv α β} (h : f.symm b = none) :
  f.trans (single b c) = ⊥ :=
begin
  ext,
  simp only [eq_none_iff_forall_not_mem, option.mem_def, f.eq_some_iff] at h,
  dsimp [pequiv.trans, single],
  simp,
  intros,
  split_ifs;
  simp * at *
end

lemma single_trans_of_eq_none (a : α) {b : β} {f : pequiv β γ} (h : f b = none) :
  (single a b).trans f = ⊥ :=
symm_injective $ trans_single_of_eq_none _ h

lemma single_trans (a : α) (b : β) (f : pequiv β γ) : (single a b).trans f =
  subsingle ((f b).map (prod.mk a)) :=
begin
  ext c d,
  dsimp [single, subsingle, pequiv.trans],
  split_ifs;
  cases h : f b;
  simp *
end

lemma option.map_map (f : α → β) (g : β → γ) (o : option α) : (o.map f).map g = o.map (g ∘ f) :=
by cases o; refl

lemma trans_single (b : β) (c : γ) (f : pequiv α β) : f.trans (single b c) =
  subsingle ((f.symm b).map (λ a, (a, c))) :=
symm_injective $ by rw [symm_subsingle, option.map_map]; exact single_trans _ _ _

end single

section order
open lattice

instance : partial_order (pequiv α β) :=
{ le := λ f g, ∀ (a : α) (b : β), b ∈ f a → b ∈ g a,
  le_refl := λ _ _ _, id,
  le_trans := λ f g h fg gh a b, (gh a b) ∘ (fg a b),
  le_antisymm := λ f g fg gf, ext begin
    assume a,
    cases h : g a with b,
    { exact eq_none_iff_forall_not_mem.2
       (λ b hb, option.not_mem_none b $ h ▸ fg a b hb) },
    { exact gf _ _ h }
  end }

lemma le_def {f g : pequiv α β} : f ≤ g ↔ (∀ (a : α) (b : β), b ∈ f a → b ∈ g a) := iff.rfl

instance : order_bot (pequiv α β) :=
{ bot_le := λ _ _  _ h, (not_mem_none _ h).elim,
  ..pequiv.partial_order,
  ..pequiv.lattice.has_bot }

instance [decidable_eq α] [decidable_eq β] : semilattice_inf_bot (pequiv α β) :=
{ inf := λ f g,
  { to_fun := λ a, if f a = g a then f a else none,
    inv_fun := λ b, if f.symm b = g.symm b then f.symm b else none,
    inv := λ a b, begin
      have := @mem_iff_mem _ _ f a b,
      have := @mem_iff_mem _ _ g a b,
      split_ifs; finish
    end },
  inf_le_left := λ _ _ _ _, by simp; split_ifs; cc,
  inf_le_right := λ _ _ _ _, by simp; split_ifs; cc,
  le_inf := λ f g h fg gh a b, begin
    have := fg a b,
    have := gh a b,
    simp [le_def],
    split_ifs; finish
  end,
  ..pequiv.lattice.order_bot }

end order


end pequiv

namespace equiv
variables {α : Type*} {β : Type*} {γ : Type*}

def to_pequiv (f : α ≃ β) : pequiv α β :=
{ to_fun := some ∘ f,
  inv_fun := some ∘ f.symm,
  inv := by simp [equiv.eq_symm_apply, eq_comm] }

@[simp] lemma to_pequiv_refl : (equiv.refl α).to_pequiv = pequiv.refl α := rfl

lemma to_pequiv_trans (f : α ≃ β) (g : β ≃ γ) : (f.trans g).to_pequiv =
  f.to_pequiv.trans g.to_pequiv := rfl

lemma to_pequiv_symm (f : α ≃ β) : f.symm.to_pequiv = f.to_pequiv.symm := rfl

def option_to_pequiv (f : option α ≃ option β) : pequiv α β :=
{ to_fun := f ∘ some,
  inv_fun := f.symm ∘ some,
  inv := by simp [equiv.eq_symm_apply, eq_comm] }

@[simp] lemma option_to_pequiv_refl : (equiv.refl (option α)).option_to_pequiv = pequiv.refl α := rfl

lemma option_to_pequiv_trans (f : option α ≃ option β) (g : option β ≃ option γ) : (f.trans g).to_pequiv =
  f.to_pequiv.trans g.to_pequiv := rfl
end equiv

variables {α : Type*} {β : Type*} [decidable_eq α] [decidable_eq β]

lemma swap_trans (a₁ a₂ : α) (f : pequiv α β) :
  (equiv.swap a₁ a₂).to_pequiv.trans f = f.trans (equiv.swap (f a₁) (f a₂)).option_to_pequiv :=
begin
  ext,
  dsimp [pequiv.trans, equiv.to_pequiv, equiv.swap_apply_def, equiv.option_to_pequiv,
    equiv.swap_apply_def, function.comp],
  simp,
  split_ifs,
  { cases hx : f x,
    simp *, }

end
