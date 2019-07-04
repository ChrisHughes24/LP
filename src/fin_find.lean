import data.fin

namespace fin

variable {n : ℕ}

def find : Π {n : ℕ} (p : fin n → Prop) [decidable_pred p], option (fin n)
| 0     p _ := none
| (n+1) p _ := by resetI; exact option.cases_on
  (@find n (λ i, p (i.cast_lt (nat.lt_succ_of_lt i.2))) _)
  (if h : p (fin.last n) then some (fin.last n) else none)
  (λ i, some (i.cast_lt (nat.lt_succ_of_lt i.2)))

lemma find_spec : Π {n : ℕ} (p : fin n → Prop) [decidable_pred p] {i : fin n}
  (hi : i ∈ by exactI fin.find p), p i
| 0     p I i hi := option.no_confusion hi
| (n+1) p I i hi := begin
  dsimp [find] at hi,
  resetI,
  cases h : find (λ i : fin n, (p (i.cast_lt (nat.lt_succ_of_lt i.2)))) with j,
  { rw h at hi,
    dsimp at hi,
    split_ifs at hi with hl hl,
    { exact option.some_inj.1 hi ▸ hl },
    { exact option.no_confusion hi } },
  { rw h at hi,
    rw [← option.some_inj.1 hi],
    exact find_spec _ h }
end

lemma is_some_find_iff : Π {n : ℕ} {p : fin n → Prop} [decidable_pred p],
  by exactI (find p).is_some ↔ ∃ i, p i
| 0     p _ := iff_of_false (λ h, bool.no_confusion h) (λ ⟨i, _⟩, fin.elim0 i)
| (n+1) p _ := ⟨λ h, begin
  resetI,
  rw [option.is_some_iff_exists] at h,
  cases h with i hi,
  exact ⟨i, find_spec _ hi⟩
end, λ ⟨⟨i, hin⟩, hi⟩,
begin
  resetI,
  dsimp [find],
  cases h : find (λ i : fin n, (p (i.cast_lt (nat.lt_succ_of_lt i.2)))) with j,
  { split_ifs with hl hl,
    { exact option.is_some_some },
    { have := (@is_some_find_iff n (λ x, p (x.cast_lt (nat.lt_succ_of_lt x.2))) _).2
        ⟨⟨i, lt_of_le_of_ne (nat.le_of_lt_succ hin)
        (λ h, by clear_aux_decl; subst h; exact hl hi)⟩, hi⟩,
      rw h at this,
      exact this } },
  { simp }
end⟩

lemma find_eq_none_iff {n : ℕ} {p : fin n → Prop} [decidable_pred p] :
  find p = none ↔ ∀ i, ¬ p i :=
by rw [← not_exists, ← is_some_find_iff]; cases (find p); simp

lemma find_min : Π {n : ℕ} {p : fin n → Prop} [decidable_pred p] {i : fin n}
  (hi : i ∈ by exactI fin.find p) {j : fin n} (hj : j < i), ¬ p j
| 0     p _ i hi j hj hpj := option.no_confusion hi
| (n+1) p _ i hi ⟨j, hjn⟩ hj hpj := begin
  resetI,
  dsimp [find] at hi,
  cases h : find (λ i : fin n, (p (i.cast_lt (nat.lt_succ_of_lt i.2)))) with k,
  { rw [h] at hi,
    split_ifs at hi with hl hl,
    { have := option.some_inj.1 hi,
      subst this,
      rw [find_eq_none_iff] at h,
      exact h ⟨j, hj⟩ hpj },
    { exact option.no_confusion hi } },
  { rw h at hi,
    dsimp at hi,
    have := option.some_inj.1 hi,
    subst this,
    exact find_min h (show (⟨j, lt_trans hj k.2⟩ : fin n) < k, from hj) hpj }
end

lemma find_min' {p : fin n → Prop} [decidable_pred p] {i : fin n}
  (h : i ∈ fin.find p) {j : fin n} (hj : p j) : i ≤ j :=
le_of_not_gt (λ hij, find_min h hij hj)

lemma nat_find_mem_find {p : fin n → Prop} [decidable_pred p]
  (h : ∃ i, ∃ hin : i < n, p ⟨i, hin⟩) :
  (⟨nat.find h, (nat.find_spec h).fst⟩ : fin n) ∈ find p :=
let ⟨i, hin, hi⟩ := h in
begin
  cases hf : find p with f,
  { rw [find_eq_none_iff] at hf,
    exact (hf ⟨i, hin⟩ hi).elim },
  { refine option.some_inj.2 (le_antisymm _ _),
    { exact find_min' hf (nat.find_spec h).snd },
    { exact nat.find_min' _ ⟨f.2, by convert find_spec p hf;
        exact fin.eta _ _⟩ } }
end

lemma mem_find_of_unique {p : fin n → Prop} [decidable_pred p]
  (h : ∀ i j, p i → p j → i = j) {i : fin n} (hi : p i) : i ∈ fin.find p :=
begin
  cases hfp : fin.find p,
  { rw [find_eq_none_iff] at hfp,
    exact (hfp _ hi).elim },
  { exact option.some_inj.2 (h _ _ (find_spec _ hfp) hi) }
end

end fin
