import dead_tableau order.lexicographic

open matrix fintype finset function pequiv partition
variables {m n : ℕ}

local notation `rvec`:2000 n := matrix (fin 1) (fin n) ℚ
local notation `cvec`:2000 m := matrix (fin m) (fin 1) ℚ
local infix ` ⬝ `:70 := matrix.mul
local postfix `ᵀ` : 1500 := transpose

namespace tableau

def pivot_linear_order (T : tableau m n) : decidable_linear_order (fin n) :=
decidable_linear_order.lift T.to_partition.colg (injective_colg _) (by apply_instance)

def find_pivot_column (T : tableau m n) (obj : fin m) : option (fin n) :=
option.cases_on
  (fin.find (λ c : fin n, T.to_matrix obj c ≠ 0 ∧ T.to_partition.colg c ∉ T.restricted
    ∧ c ∉ T.dead))
  (((list.fin_range n).filter (λ c : fin n, 0 < T.to_matrix obj c ∧ c ∉ T.dead)).argmin
    T.to_partition.colg)
  some

def pivot_row_linear_order (T : tableau m n) (c : fin n) : decidable_linear_order (fin m) :=
decidable_linear_order.lift
  (show fin m → lex ℚ (fin (m + n)),
    from λ r', (abs (T.const r' 0 / T.to_matrix r' c), T.to_partition.rowg r'))
  (λ x y, by simp [T.to_partition.injective_rowg.eq_iff])
  (by apply_instance)

section
local attribute [instance, priority 0] fin.has_le fin.decidable_linear_order

lemma pivot_row_linear_order_le_def (T : tableau m n) (c : fin n) :
  @has_le.le (fin m)
  (by haveI := pivot_row_linear_order T c; apply_instance) =
  (λ i i', abs (T.const i 0 / T.to_matrix i c) < abs (T.const i' 0 / T.to_matrix i' c) ∨
    (abs (T.const i 0 / T.to_matrix i c) = abs (T.const i' 0 / T.to_matrix i' c) ∧
    T.to_partition.rowg i ≤ T.to_partition.rowg i')) :=
funext $ λ i, funext $ λ i', propext $ prod.lex_def _ _

end

def find_pivot_row (T : tableau m n) (obj: fin m) (c : fin n) : option (fin m) :=
let l := (list.fin_range m).filter (λ r : fin m, obj ≠ r ∧ T.to_partition.rowg r ∈ T.restricted
  ∧ T.to_matrix obj c / T.to_matrix r c < 0) in
@list.minimum _ (pivot_row_linear_order T c) l

lemma find_pivot_column_spec {T : tableau m n} {obj : fin m} {c : fin n} :
  c ∈ find_pivot_column T obj → ((T.to_matrix obj c ≠ 0 ∧ T.to_partition.colg c ∉ T.restricted)
  ∨ (0 < T.to_matrix obj c ∧ T.to_partition.colg c ∈ T.restricted)) ∧ c ∉ T.dead :=
begin
  simp [find_pivot_column],
  cases h : fin.find (λ c : fin n, T.to_matrix obj c ≠ 0 ∧ T.to_partition.colg c ∉ T.restricted
    ∧ c ∉ T.dead),
  { finish [h, fin.find_eq_some_iff, fin.find_eq_none_iff, lt_irrefl, list.argmin_eq_some_iff] },
  { finish [fin.find_eq_some_iff] }
end

lemma nonpos_of_lt_find_pivot_column {T : tableau m n} {obj : fin m} {c j : fin n}
  (hc : c ∈ find_pivot_column T obj) (hcres : T.to_partition.colg c ∈ T.restricted)
  (hdead : j ∉ T.dead) (hjc : T.to_partition.colg j < T.to_partition.colg c) :
  T.to_matrix obj j ≤ 0 :=
begin
  rw [find_pivot_column] at hc,
  cases h : fin.find (λ c, T.to_matrix obj c ≠ 0 ∧ colg (T.to_partition) c ∉ T.restricted
    ∧ c ∉ T.dead),
  { rw h at hc,
    refine le_of_not_lt (λ hj0, _),
    exact not_le_of_gt hjc ((list.mem_argmin_iff.1 hc).2.1 j
      (list.mem_filter.2 (by simp [hj0, hdead]))) },
  { rw h at hc,
    simp [*, fin.find_eq_some_iff] at * }
end

lemma find_pivot_column_eq_none {T : tableau m n} {obj : fin m} (hT : T.feasible)
  (h : find_pivot_column T obj = none) : T.is_optimal (T.of_col 0) (T.to_partition.rowg obj) :=
is_optimal_of_col_zero hT
begin
  revert h,
  simp [find_pivot_column],
  cases h : fin.find (λ c : fin n, T.to_matrix obj c ≠ 0 ∧ T.to_partition.colg c ∉ T.restricted
    ∧ c ∉ T.dead),
  { simp only [list.filter_eq_nil, forall_prop_of_true, list.argmin_eq_none,
      list.mem_fin_range, not_and, not_not, fin.find_eq_none_iff] at *,
    assume hj j hdead,
    exact ⟨le_of_not_gt (λ h0, hdead (hj j h0)), by finish⟩ },
  { simp [h] }
end

lemma find_pivot_row_spec {T : tableau m n} {obj r : fin m} {c : fin n} :
  r ∈ find_pivot_row T obj c →
  obj ≠ r ∧ T.to_partition.rowg r ∈ T.restricted ∧
  T.to_matrix obj c / T.to_matrix r c < 0 ∧
  (∀ r' : fin m, obj ≠ r' → T.to_partition.rowg r' ∈ T.restricted →
    T.to_matrix obj c / T.to_matrix r' c < 0 →
  abs (T.const r 0 / T.to_matrix r c) ≤ abs (T.const r' 0 / T.to_matrix r' c)) :=
begin
  simp only [list.mem_filter, find_pivot_row, option.mem_def, with_bot.some_eq_coe,
    list.minimum_eq_coe_iff, list.mem_fin_range, true_and, and_imp],
  rw [pivot_row_linear_order_le_def],
  intros hor hres hr0 h,
  simp only [*, true_and, ne.def, not_false_iff],
  intros r' hor' hres' hr0',
  cases h r' hor' hres' hr0',
  { exact le_of_lt (by assumption) },
  { exact le_of_eq (by tauto) }
end

lemma nonneg_of_lt_find_pivot_row {T : tableau m n} {obj : fin m} {r i : fin m} {c : fin n}
  (hc0 : 0 < T.to_matrix obj c) (hres : T.to_partition.rowg i ∈ T.restricted)
  (hc : c ∈ find_pivot_column T obj) (hr : r ∈ find_pivot_row T obj c)
  (hconst : T.const i 0 = 0)
  (hjc : T.to_partition.rowg i < T.to_partition.rowg r) :
  0 ≤ T.to_matrix i c :=
if hobj : obj = i then le_of_lt $ hobj ▸ hc0
else
le_of_not_gt $ λ hic, not_le_of_lt hjc
begin
  have := ((@list.minimum_eq_coe_iff _ (id _) _ _).1 hr).2 i
    (list.mem_filter.2 ⟨list.mem_fin_range _, hobj, hres, div_neg_of_pos_of_neg hc0 hic⟩),
  rw [pivot_row_linear_order_le_def] at this,
  simp [hconst, not_lt_of_ge (abs_nonneg _), *] at *
end

lemma ne_zero_of_mem_find_pivot_row {T : tableau m n} {obj r : fin m} {c : fin n}
  (hr : r ∈ find_pivot_row T obj c) : T.to_matrix r c ≠ 0 :=
assume hrc, by simpa [lt_irrefl, hrc] using find_pivot_row_spec hr

lemma ne_zero_of_mem_find_pivot_column {T : tableau m n} {obj : fin m} {c : fin n}
  (hc : c ∈ find_pivot_column T obj) : T.to_matrix obj c ≠ 0 :=
λ h, by simpa [h, lt_irrefl] using find_pivot_column_spec hc

lemma find_pivot_row_eq_none_aux {T : tableau m n} {obj : fin m} {c : fin n}
  (hrow : find_pivot_row T obj c = none) (hs : c ∈ find_pivot_column T obj) :
  ∀ r, obj ≠ r → T.to_partition.rowg r ∈ T.restricted → 0 ≤ T.to_matrix obj c / T.to_matrix r c :=
by simpa [find_pivot_row, list.filter_eq_nil] using hrow

lemma find_pivot_row_eq_none {T : tableau m n} {obj : fin m} {c : fin n} (hT : T.feasible)
  (hrow : find_pivot_row T obj c = none) (hs : c ∈ find_pivot_column T obj) :
  T.is_unbounded_above (T.to_partition.rowg obj) :=
have hrow : ∀ r, obj ≠ r → T.to_partition.rowg r ∈ T.restricted →
    0 ≤ T.to_matrix obj c / T.to_matrix r c,
  from find_pivot_row_eq_none_aux hrow hs,
have hc : ((T.to_matrix obj c ≠ 0 ∧ T.to_partition.colg c ∉ T.restricted)
    ∨ (0 < T.to_matrix obj c ∧ T.to_partition.colg c ∈ T.restricted)) ∧ c ∉ T.dead,
  from find_pivot_column_spec hs,
have hToc : T.to_matrix obj c ≠ 0, from λ h, by simpa [h, lt_irrefl] using hc,
(lt_or_gt_of_ne hToc).elim
  (λ hToc : T.to_matrix obj c < 0, is_unbounded_above_rowg_of_nonpos hT c
    (hc.1.elim and.right (λ h, (not_lt_of_gt hToc h.1).elim)) hc.2
    (λ i hi, classical.by_cases
      (λ hoi : obj = i, le_of_lt (hoi ▸ hToc))
      (λ hoi : obj ≠ i, inv_nonpos.1 $ nonpos_of_mul_nonneg_right (hrow _ hoi hi) hToc))
    hToc)
  (λ hToc : 0 < T.to_matrix obj c, is_unbounded_above_rowg_of_nonneg hT c
    (λ i hi, classical.by_cases
      (λ hoi : obj = i, le_of_lt (hoi ▸ hToc))
      (λ hoi : obj ≠ i, inv_nonneg.1 $ nonneg_of_mul_nonneg_left (hrow _ hoi hi) hToc))
    hc.2 hToc)

def feasible_of_mem_pivot_row_and_column {T : tableau m n} {obj : fin m} (hT : T.feasible) {c}
  (hc : c ∈ find_pivot_column T obj) {r} (hr : r ∈ find_pivot_row T obj c) :
  feasible (T.pivot r c) :=
begin
  have := find_pivot_column_spec hc,
  have := find_pivot_row_spec hr,
  have := @feasible_simplex_pivot _ _ _ obj hT r c,
  tauto
end

section blands_rule

local attribute [instance, priority 0] classical.dec
variable (obj : fin m)

lemma not_unique_row_and_unique_col {T T' : tableau m n} {r c c'}
  (hcobj0 : 0 < T.to_matrix obj c)
  (hc'obj0 : 0 < T'.to_matrix obj c')
  (hrc0 : T.to_matrix r c < 0)
  (hflat : T.flat = T'.flat)
  (hs : T.to_partition.rowg r = T'.to_partition.colg c')
  (hrobj : T.to_partition.rowg obj = T'.to_partition.rowg obj)
  (hfickle : ∀ i, T.to_partition.rowg i ≠ T'.to_partition.rowg i → T.const i 0 = 0)
  (hobj : T.const obj 0 = T'.const obj 0)
  (nonpos_of_colg_ne : ∀ j,
    T'.to_partition.colg j ≠ T.to_partition.colg j → j ≠ c' → T'.to_matrix obj j ≤ 0)
  (nonpos_of_colg_eq : ∀ j, j ≠ c' →
    T'.to_partition.colg j = T.to_partition.colg c → T'.to_matrix obj j ≤ 0)
  (unique_row : ∀ i ≠ r, T.const i 0 = 0 → T.to_partition.rowg i ≠ T'.to_partition.rowg i →
    0 ≤ T.to_matrix i c) :
  false :=
let objr := T.to_partition.rowg obj in
let x := λ y : ℚ, T.of_col (y • (single c 0).to_matrix) in
have hxflatT' : ∀ {y}, x y ∈ flat T', from hflat ▸ λ _, of_col_mem_flat _ _,
have hxrow : ∀ y i, x y (T.to_partition.rowg i) 0 = T.const i 0 + y * T.to_matrix i c,
  by simp [x, of_col_single_rowg],
have hxcol : ∀ {y j}, j ≠ c → x y (T.to_partition.colg j) 0 = 0,
  from λ y j hjc, by simp [x, of_col_colg, pequiv.to_matrix, single_apply_of_ne hjc.symm],
have hxcolc : ∀ {y}, x y (T.to_partition.colg c) 0 = y, by simp [x, of_col_colg, pequiv.to_matrix],
let c_star : fin (m + n) → ℚ := λ v, option.cases_on (T'.to_partition.colp.symm v) 0
  (T'.to_matrix obj) in
have hxobj : ∀ y, x y objr 0 = T.const obj 0 + y * T.to_matrix obj c, from λ y, hxrow _ _,
have hgetr : ∀ {y v}, c_star v * x y v 0 ≠ 0 → (T'.to_partition.colp.symm v).is_some,
  from λ y v, by cases h : T'.to_partition.colp.symm v; dsimp [c_star]; rw h; simp,
have c_star_eq_get : ∀ {v} (hv : (T'.to_partition.colp.symm v).is_some),
    c_star v = T'.to_matrix obj (option.get hv),
  from λ v hv, by dsimp only [c_star]; conv_lhs{rw [← option.some_get hv]}; refl,
have hsummmn : ∀ {y}, sum univ (λ j, T'.to_matrix obj j * x y (T'.to_partition.colg j) 0) =
    sum univ (λ v, c_star v * x y v 0),
  from λ y, sum_bij_ne_zero (λ j _ _, T'.to_partition.colg j) (λ _ _ _, mem_univ _)
    (λ _ _ _ _ _ _ h, T'.to_partition.injective_colg h)
    (λ v _ h0, ⟨option.get (hgetr h0), mem_univ _,
      by rw [← c_star_eq_get (hgetr h0)]; simpa using h0, by simp⟩)
    (λ _ _ h0, by dsimp [c_star]; rw [colp_colg]),
have hgetc : ∀ {y v}, c_star v * x y v 0 ≠ 0 → v ≠ T.to_partition.colg c →
    (T.to_partition.rowp.symm v).is_some,
  from λ y v, (eq_rowg_or_colg T.to_partition v).elim
    (λ ⟨i, hi⟩, by rw [hi, rowp_rowg]; simp)
    (λ ⟨j, hj⟩ h0 hvc,
      by rw [hj, hxcol (mt (congr_arg T.to_partition.colg) (hvc ∘ hj.trans)), mul_zero] at h0;
        exact (h0 rfl).elim),
have hsummmnn : ∀ {y}, (univ.erase (T.to_partition.colg c)).sum (λ v, c_star v * x y v 0) =
    univ.sum (λ i, c_star (T.to_partition.rowg i) * x y (T.to_partition.rowg i) 0),
  from λ y, eq.symm $ sum_bij_ne_zero (λ i _ _, T.to_partition.rowg i) (by simp)
    (λ _ _ _ _ _ _ h, T.to_partition.injective_rowg h)
    (λ v hvc h0, ⟨option.get (hgetc h0 (mem_erase.1 hvc).1), mem_univ _, by simpa using h0⟩)
    (by intros; refl),
have hsumm : ∀ {y}, univ.sum (λ i, c_star (T.to_partition.rowg i) * x y (T.to_partition.rowg i) 0) =
    univ.sum (λ i, c_star (T.to_partition.rowg i) * T.const i 0) +
    y * univ.sum (λ i, c_star (T.to_partition.rowg i) * T.to_matrix i c),
  from λ y, by simp only [hxrow, mul_add, add_mul, sum_add_distrib, mul_assoc,
    mul_left_comm _ y, mul_sum.symm],
have hxobj' : ∀ y, x y objr 0 = univ.sum (λ v, c_star v * x y v 0) + T'.const obj 0,
  from λ y, by dsimp [objr]; rw [hrobj, mem_flat_iff.1 hxflatT', hsummmn],
have hy : ∀ {y}, y * T.to_matrix obj c = c_star (T.to_partition.colg c) * y +
    univ.sum (λ i, c_star (T.to_partition.rowg i) * T.const i 0) +
      y * univ.sum (λ i, c_star (T.to_partition.rowg i) * T.to_matrix i c),
  from λ y, by rw [← add_left_inj (T.const obj 0), ← hxobj, hxobj',
    ← insert_erase (mem_univ (T.to_partition.colg c)), sum_insert (not_mem_erase _ _),
    hsummmnn, hobj, hsumm, hxcolc]; simp,
have hy' : ∀ (y), y * (T.to_matrix obj c - c_star (T.to_partition.colg c) -
    univ.sum (λ i, c_star (T.to_partition.rowg i) * T.to_matrix i c)) =
    univ.sum (λ i, c_star (T.to_partition.rowg i) * T.const i 0),
  from λ y, by rw [mul_sub, mul_sub, hy]; simp [mul_comm, mul_assoc, mul_left_comm],
have h0 : T.to_matrix obj c - c_star (T.to_partition.colg c) -
    univ.sum (λ i, c_star (T.to_partition.rowg i) * T.to_matrix i c) = 0,
  by rw [← (domain.mul_left_inj (@one_ne_zero ℚ _)), hy', ← hy' 0, zero_mul, mul_zero],
have hcolnec' : T'.to_partition.colp.symm (T.to_partition.colg c) ≠ some c',
  from λ h,
    by simpa [hs.symm] using congr_arg T'.to_partition.colg (option.eq_some_iff_get_eq.1 h).snd,
have eq_of_roweqc' : ∀ {i}, T'.to_partition.colp.symm (T.to_partition.rowg i) = some c' → i = r,
  from λ i h, by simpa [hs.symm, T.to_partition.injective_rowg.eq_iff] using
    congr_arg T'.to_partition.colg (option.eq_some_iff_get_eq.1 h).snd,
have sumpos : 0 < univ.sum (λ i, c_star (T.to_partition.rowg i) * T.to_matrix i c),
  by rw [← sub_eq_zero.1 h0]; exact add_pos_of_pos_of_nonneg hcobj0
    (begin
      simp only [c_star, neg_nonneg],
      cases h : T'.to_partition.colp.symm (T.to_partition.colg c) with j,
      { refl },
      { exact nonpos_of_colg_eq j (mt (congr_arg some) (h ▸ hcolnec'))
          (by rw [← (option.eq_some_iff_get_eq.1 h).snd]; simp) }
    end),
have hexi : ∃ i, 0 < c_star (T.to_partition.rowg i) * T.to_matrix i c,
  from imp_of_not_imp_not _ _ (by simpa using @sum_nonpos _ _ (@univ (fin m) _)
    (λ i, c_star (T.to_partition.rowg i) * T.to_matrix i c) _ _) sumpos,
let ⟨i, hi⟩ := hexi in
have hi0 : T.const i 0 = 0, from hfickle i
  (λ h, by dsimp [c_star] at hi; rw [h, colp_rowg_eq_none] at hi; simpa [lt_irrefl] using hi),
have hi_some : (T'.to_partition.colp.symm (T.to_partition.rowg i)).is_some,
  from option.ne_none_iff_is_some.1 (λ h, by dsimp only [c_star] at hi; rw h at hi;
    simpa [lt_irrefl] using hi),
have hi' : 0 < T'.to_matrix obj (option.get hi_some) * T.to_matrix i c,
  by dsimp only [c_star] at hi; rwa [← option.some_get hi_some] at hi,
have hir : i ≠ r, from λ hir, begin
    have : option.get hi_some = c', from T'.to_partition.injective_colg
      (by rw [colg_get_colp_symm, ← hs, hir]),
    rw [this, hir] at hi',
    exact not_lt_of_gt hi' (mul_neg_of_pos_of_neg hc'obj0 hrc0)
  end,
have hnec' : option.get hi_some ≠ c',
  from λ eq_c', hir $ @eq_of_roweqc' i (eq_c' ▸ by simp),
have hic0 : T.to_matrix i c < 0,
  from neg_of_mul_pos_right hi' (nonpos_of_colg_ne _ (by simp) hnec'),
not_le_of_gt hic0 (unique_row _ hir hi0
  (by rw [← colg_get_colp_symm _ _ hi_some]; exact colg_ne_rowg _ _ _))

inductive rel : tableau m n → tableau m n → Prop
| pivot : ∀ {T}, feasible T → ∀ {r c}, c ∈ find_pivot_column T obj →
  r ∈ find_pivot_row T obj c → rel (T.pivot r c) T
| trans_pivot : ∀ {T₁ T₂ r c}, rel T₁ T₂ → c ∈ find_pivot_column T₁ obj →
  r ∈ find_pivot_row T₁ obj c → rel (T₁.pivot r c) T₂

lemma feasible_of_rel_right {T T' : tableau m n} (h : rel obj T' T) : T.feasible :=
rel.rec_on h (by tauto) (by tauto)

lemma feasible_of_rel_left {T T' : tableau m n} (h : rel obj T' T) : T'.feasible :=
rel.rec_on h (λ _ hT _ _ hc hr, feasible_of_mem_pivot_row_and_column hT hc hr)
  (λ _ _ _ _ _ hc hr hT, feasible_of_mem_pivot_row_and_column hT hc hr)

/-- Slightly stronger recursor than the default recursor -/
@[elab_as_eliminator]
lemma rel.rec_on' {obj : fin m} {C : tableau m n → tableau m n → Prop} {T T' : tableau m n}
  (hrel : rel obj T T')
  (hpivot : ∀ {T : tableau m n} {r : fin m} {c : fin n},
     feasible T → c ∈ find_pivot_column T obj → r ∈ find_pivot_row T obj c → C (pivot T r c) T)
  (hpivot_trans : ∀ {T₁ T₂ : tableau m n} {r : fin m} {c : fin n},
    rel obj (T₁.pivot r c) T₁ → rel obj T₁ T₂ →
     c ∈ find_pivot_column T₁ obj →
     r ∈ find_pivot_row T₁ obj c → C (T₁.pivot r c) T₁ → C T₁ T₂ → C (pivot T₁ r c) T₂) :
  C T T' :=
rel.rec_on hrel (λ T hT r c  hc hr, hpivot hT hc hr) (λ T₁ T₂ r c hrelT₁₂ hc hr ih, hpivot_trans
  (rel.pivot (feasible_of_rel_left obj hrelT₁₂) hc hr) hrelT₁₂ hc hr
  (hpivot (feasible_of_rel_left obj hrelT₁₂) hc hr) ih)

lemma rel.trans {obj : fin m} {T₁ T₂ T₃ : tableau m n} (h₁₂ : rel obj T₁ T₂) :
  rel obj T₂ T₃ → rel obj T₁ T₃ :=
rel.rec_on h₁₂
  (λ T r c hT hc hr hrelT, rel.trans_pivot hrelT hc hr)
  (λ T₁ T₂ r c hrelT₁₂ hc hr ih hrelT₂₃, rel.trans_pivot (ih hrelT₂₃) hc hr)

instance : is_trans (tableau m n) (rel obj) := ⟨@rel.trans _ _ obj⟩

lemma flat_eq_of_rel {T T' : tableau m n} (h : rel obj T' T) : flat T' = flat T :=
rel.rec_on' h (λ _ _ _ _ _ hr, flat_pivot (ne_zero_of_mem_find_pivot_row hr))
  (λ _ _ _ _ _ _ _ _, eq.trans)

lemma rowg_obj_eq_of_rel {T T' : tableau m n} (h : rel obj T T') : T.to_partition.rowg obj =
  T'.to_partition.rowg obj :=
rel.rec_on' h (λ T r c hfT hc hr, by simp [rowg_swap_of_ne _ (find_pivot_row_spec hr).1])
  (λ _ _ _ _ _ _ _ _, eq.trans)

lemma restricted_eq_of_rel {T T' : tableau m n} (h : rel obj T T') : T.restricted = T'.restricted :=
rel.rec_on' h (λ _ _ _ _ _ _, rfl) (λ _ _ _ _ _ _ _ _, eq.trans)

lemma exists_mem_pivot_row_column_of_rel {T T' : tableau m n} (h : rel obj T' T) :
  ∃ r c, c ∈ find_pivot_column T obj ∧ r ∈ find_pivot_row T obj c :=
rel.rec_on' h (λ _ r c _ hc hr, ⟨r, c, hc, hr⟩) (λ _ _ _ _ _ _ _ _ _, id)

lemma exists_mem_pivot_row_of_rel {T T' : tableau m n} (h : rel obj T' T) {c : fin n}
  (hc : c ∈ find_pivot_column T obj) : ∃ r, r ∈ find_pivot_row T obj c :=
let ⟨r, c', hc', hr⟩ := exists_mem_pivot_row_column_of_rel obj h in ⟨r, by simp * at *⟩

lemma colg_eq_or_exists_mem_pivot_column {T₁ T₂ : tableau m n} (h : rel obj T₂ T₁) {c : fin n} :
  T₁.to_partition.colg c = T₂.to_partition.colg c ∨
  ∃ T₃, (T₃ = T₁ ∨ rel obj T₃ T₁) ∧ (rel obj T₂ T₃) ∧
  T₃.to_partition.colg c = T₁.to_partition.colg c ∧
  c ∈ find_pivot_column T₃ obj :=
rel.rec_on' h begin
    assume T r c' hT hc' hr,
    by_cases hcc : c = c',
    { subst hcc,
      exact or.inr ⟨T, or.inl rfl, rel.pivot hT hc' hr, rfl, hc'⟩ },
    { simp [colg_swap_of_ne _ hcc] }
  end
  (λ T₁ T₂ r c hrelp₁ hrel₁₂ hc hr ihp₁ ih₁₂,
    ih₁₂.elim
      (λ ih₁₂, ihp₁.elim
        (λ ihp₁, or.inl (ih₁₂.trans ihp₁))
        (λ ⟨T₃, hT₃⟩, or.inr ⟨T₃,
          hT₃.1.elim (λ h, h.symm ▸ or.inr hrel₁₂) (λ h, or.inr $ h.trans hrel₁₂),
          hT₃.2.1, hT₃.2.2.1.trans ih₁₂.symm, hT₃.2.2.2⟩))
      (λ ⟨T₃, hT₃⟩, or.inr ⟨T₃, hT₃.1, hrelp₁.trans hT₃.2.1, hT₃.2.2⟩))

lemma rowg_eq_or_exists_mem_pivot_row {T₁ T₂ : tableau m n} (h : rel obj T₂ T₁) (r : fin m) :
  T₁.to_partition.rowg r = T₂.to_partition.rowg r ∨
  ∃ (T₃ : tableau m n) c, (T₃ = T₁ ∨ rel obj T₃ T₁) ∧ (rel obj T₂ T₃) ∧
    T₃.to_partition.rowg r = T₁.to_partition.rowg r ∧
    c ∈ find_pivot_column T₃ obj ∧ r ∈ find_pivot_row T₃ obj c :=
rel.rec_on' h
  begin
    assume T r' c hT hc hr',
    by_cases hrr : r = r',
    { subst hrr,
      exact or.inr ⟨T, c, or.inl rfl, rel.pivot hT hc hr', rfl, hc, hr'⟩ },
    { simp [rowg_swap_of_ne _ hrr] }
  end
  (λ T₁ T₂ r c hrelp₁ hrel₁₂ hc hr ihp₁ ih₁₂,
    ih₁₂.elim
      (λ ih₁₂, ihp₁.elim
        (λ ihp₁, or.inl $ ih₁₂.trans ihp₁)
        (λ ⟨T₃, c', hT₃⟩, or.inr ⟨T₃, c', hT₃.1.elim (λ h, h.symm ▸ or.inr hrel₁₂)
           (λ h, or.inr $ h.trans hrel₁₂), hT₃.2.1, ih₁₂.symm ▸ hT₃.2.2.1, hT₃.2.2.2⟩))
      (λ ⟨T₃, c', hT₃⟩, or.inr ⟨T₃, c', hT₃.1,
        (rel.pivot (feasible_of_rel_left _ hrel₁₂) hc hr).trans hT₃.2.1, hT₃.2.2⟩))

lemma eq_or_rel_pivot_of_rel {T₁ T₂ : tableau m n} (h : rel obj T₁ T₂) : ∀ {r c}
  (hc : c ∈ find_pivot_column T₂ obj) (hr : r ∈ find_pivot_row T₂ obj c),
  T₁ = T₂.pivot r c ∨ rel obj T₁ (T₂.pivot r c) :=
rel.rec_on' h (λ T r c hT hc hr r' c' hc' hr', by simp * at *)
  (λ T₁ T₂ r c hrelp₁ hrel₁₂ hc hr ihp₁ ih₁₂ r' c' hc' hr',
    (ih₁₂ hc' hr').elim
      (λ ih₁₂, or.inr $ ih₁₂ ▸ rel.pivot (feasible_of_rel_left _ hrel₁₂) hc hr)
      (λ ih₁₂, or.inr $ (rel.pivot (feasible_of_rel_left _ hrel₁₂) hc hr).trans ih₁₂))

lemma exists_mem_pivot_column_of_mem_pivot_row {T : tableau m n} (hrelTT : rel obj T T)
  {r c} (hc : c ∈ find_pivot_column T obj) (hr : r ∈ find_pivot_row T obj c) :
  ∃ (T' : tableau m n), c ∈ find_pivot_column T' obj ∧ T'.to_partition.colg c =
  T.to_partition.rowg r ∧ rel obj T' T ∧ rel obj T T' :=
have hrelTTp : rel obj T (T.pivot r c),
  from (eq_or_rel_pivot_of_rel _ hrelTT hc hr).elim (λ h, h ▸ hrelTT ) id,
let ⟨T', hT'⟩ := (colg_eq_or_exists_mem_pivot_column obj hrelTTp).resolve_left
  (show (T.pivot r c).to_partition.colg c ≠ T.to_partition.colg c, by simp) in
⟨T', hT'.2.2.2, by simp [hT'.2.2.1], hT'.1.elim
  (λ h, h.symm ▸ rel.pivot (feasible_of_rel_left _ hrelTT) hc hr)
  (λ h, h.trans $ rel.pivot (feasible_of_rel_left _ hrelTT) hc hr), hT'.2.1⟩

lemma exists_mem_pivot_column_of_rowg_ne {T T' : tableau m n} (hrelTT' : rel obj T T') {r : fin m}
  (hrelT'T : rel obj T' T) (hrow : T.to_partition.rowg r ≠ T'.to_partition.rowg r) :
  ∃ (T₃ : tableau m n) c, c ∈ find_pivot_column T₃ obj ∧ T₃.to_partition.colg c =
  T.to_partition.rowg r ∧ rel obj T₃ T ∧ rel obj T T₃ :=
let ⟨T₃, c, hT₃, hrelT₃T, hrow₃, hc, hr⟩ :=
  (rowg_eq_or_exists_mem_pivot_row obj hrelT'T _).resolve_left hrow in
let ⟨T₄, hT₄⟩ := exists_mem_pivot_column_of_mem_pivot_row obj
  (show rel obj T₃ T₃, from hT₃.elim (λ h, h.symm ▸ hrelTT'.trans hrelT'T)
    (λ h, h.trans $ hrelTT'.trans hrelT₃T)) hc hr in
⟨T₄, c, hT₄.1, hT₄.2.1.trans hrow₃, hT₄.2.2.1.trans $ hT₃.elim (λ h, h.symm ▸ hrelTT'.trans hrelT'T)
  (λ h, h.trans $ hrelTT'.trans hrelT'T), hrelTT'.trans (hrelT₃T.trans hT₄.2.2.2)⟩

lemma const_obj_le_of_rel {T₁ T₂ : tableau m n} (h : rel obj T₁ T₂) :
  T₂.const obj 0 ≤ T₁.const obj 0 :=
rel.rec_on' h (λ T r c hT hc hr,
    have hr' : _ := find_pivot_row_spec hr,
    simplex_const_obj_le hT (by tauto) (by tauto))
  (λ _ _ _ _ _ _ _ _ h₁ h₂, le_trans h₂ h₁)

lemma const_obj_eq_of_rel_of_rel {T₁ T₂ : tableau m n} (h₁₂ : rel obj T₁ T₂)
  (h₂₁ : rel obj T₂ T₁) : T₁.const obj 0 = T₂.const obj 0 :=
le_antisymm (const_obj_le_of_rel _ h₂₁) (const_obj_le_of_rel _ h₁₂)

lemma const_eq_const_of_const_obj_eq {T₁ T₂ : tableau m n} (h₁₂ : rel obj T₁ T₂) :
  ∀ (hobj : T₁.const obj 0 = T₂.const obj 0) (i : fin m), T₁.const i 0 = T₂.const i 0 :=
rel.rec_on' h₁₂
  (λ T r c hfT hc hr hobj i,
    have hr0 : T.const r 0 = 0, from const_eq_zero_of_const_obj_eq hfT
      (ne_zero_of_mem_find_pivot_column hc) (ne_zero_of_mem_find_pivot_row hr)
      (find_pivot_row_spec hr).1 hobj,
    if hir : i = r
      then by simp [hir, hr0]
      else by simp [const_pivot_of_ne _ hir, hr0])
  (λ T₁ T₂ r c hrelp₁ hrel₁₂ hc hr ihp₁ ih₁₂ hobj i,
    have hobjp : (pivot T₁ r c).const obj 0 = T₁.const obj 0,
      from le_antisymm (hobj.symm ▸ const_obj_le_of_rel _ hrel₁₂)
        (const_obj_le_of_rel _ hrelp₁),
    by rw [ihp₁ hobjp, ih₁₂ (hobjp.symm.trans hobj)])

lemma const_eq_zero_of_rowg_ne_of_rel_self {T T' : tableau m n} (hrelTT' : rel obj T T')
  (hrelT'T : rel obj T' T) (i : fin m) (hrow : T.to_partition.rowg i ≠ T'.to_partition.rowg i) :
  T.const i 0 = 0 :=
let ⟨T₃, c, hT₃₁, hT'₃, hrow₃, hc, hi⟩ := (rowg_eq_or_exists_mem_pivot_row obj hrelT'T _).resolve_left hrow in
have T₃.const i 0 = 0, from const_eq_zero_of_const_obj_eq
  (feasible_of_rel_right _ hT'₃) (ne_zero_of_mem_find_pivot_column hc)
  (ne_zero_of_mem_find_pivot_row hi) (find_pivot_row_spec hi).1
  (const_obj_eq_of_rel_of_rel _ (rel.pivot (feasible_of_rel_right _ hT'₃) hc hi)
    ((eq_or_rel_pivot_of_rel _ hT'₃ hc hi).elim
      (λ h, h ▸ hT₃₁.elim (λ h, h.symm ▸ hrelTT') (λ h, h.trans hrelTT'))
      (λ hrelT'p, hT₃₁.elim (λ h, h.symm ▸ hrelTT'.trans (h ▸ hrelT'p))
        (λ h, h.trans $ hrelTT'.trans hrelT'p)))),
have hobj : T₃.const obj 0 = T.const obj 0,
  from hT₃₁.elim (λ h, h ▸ rfl) (λ h, const_obj_eq_of_rel_of_rel _ h (hrelTT'.trans hT'₃)),
hT₃₁.elim (λ h, h ▸ this) (λ h, const_eq_const_of_const_obj_eq obj h hobj i ▸ this)

lemma colg_mem_restricted_of_rel_self {T : tableau m n} (hrelTT : rel obj T T)
  {c} (hc : c ∈ find_pivot_column T obj) : T.to_partition.colg c ∈ T.restricted :=
let ⟨r, hr⟩ := exists_mem_pivot_row_of_rel obj hrelTT hc in
let ⟨T', c', hT', hrelTT', hrowcol, _, hr'⟩ := (rowg_eq_or_exists_mem_pivot_row obj
    ((eq_or_rel_pivot_of_rel _ hrelTT hc hr).elim
      (λ h, show rel obj T (T.pivot r c), from h ▸ hrelTT) id) _).resolve_left
  (show (T.pivot r c).to_partition.rowg r ≠ T.to_partition.rowg r, by simp) in
(restricted_eq_of_rel _ hrelTT').symm ▸ by convert (find_pivot_row_spec hr').2.1; simp [hrowcol]

lemma eq_zero_of_not_mem_restricted_of_rel_self {T : tableau m n} (hrelTT : rel obj T T)
  {j} (hjres : T.to_partition.colg j ∉ T.restricted) (hdead : j ∉ T.dead) : T.to_matrix obj j = 0 :=
let ⟨r, c, hc, hr⟩ := exists_mem_pivot_row_column_of_rel obj hrelTT in
have hcres : T.to_partition.colg c ∈ T.restricted,
  from colg_mem_restricted_of_rel_self obj hrelTT hc,
by_contradiction $ λ h0,
begin
  simp [find_pivot_column] at hc,
  cases h : fin.find (λ c, T.to_matrix obj c ≠ 0 ∧ colg (T.to_partition) c ∉ T.restricted
    ∧ c ∉ T.dead),
  { simp [*, fin.find_eq_none_iff] at * },
  { rw h at hc, clear_aux_decl,
    have := (fin.find_eq_some_iff.1 h).1,
    simp * at * }
end

lemma rel.irrefl {obj : fin m} : ∀ (T : tableau m n), ¬ rel obj T T :=
λ T1 hrelT1,
let ⟨rT1 , cT1, hrT1, hcT1⟩ := exists_mem_pivot_row_column_of_rel obj hrelT1 in
let ⟨t, ht⟩ := finset.max_of_mem
  (show T1.to_partition.colg cT1 ∈ univ.filter (λ v, ∃ (T' : tableau m n) (c : fin n),
      rel obj T' T' ∧ c ∈ find_pivot_column T' obj ∧ T'.to_partition.colg c = v),
    by simp only [true_and, mem_filter, mem_univ, exists_and_distrib_left];
      exact ⟨T1, hrelT1, cT1, hrT1, rfl⟩) in
let ⟨_, T', c', hrelTT'', hcT', hct⟩ := finset.mem_filter.1 (finset.mem_of_max ht) in
have htmax : ∀ (s : fin (m + n)) (T : tableau m n),
    rel obj T T → ∀ (j : fin n), find_pivot_column T obj = some j →
      T.to_partition.colg j = s → s ≤ t,
  by simpa using λ s (h : s ∈ _), finset.le_max_of_mem h ht,
let ⟨r, hrT'⟩ := exists_mem_pivot_row_of_rel obj hrelTT'' hcT' in
have hrelTT''p : rel obj T' (T'.pivot r c'),
  from (eq_or_rel_pivot_of_rel obj hrelTT'' hcT' hrT').elim (λ h, h ▸ hrelTT'') id,
let ⟨T, c, hTT', hrelT'T, hT'Tr, hc, hr⟩ := (rowg_eq_or_exists_mem_pivot_row obj
  hrelTT''p r).resolve_left (by simp) in
have hfT' : feasible T', from feasible_of_rel_left _ hrelTT'',
have hfT : feasible T, from feasible_of_rel_right _ hrelT'T,
have hrelT'pT' : rel obj (T'.pivot r c') T', from rel.pivot hfT' hcT' hrT',
have hrelTT' : rel obj T T', from hTT'.elim (λ h, h.symm ▸ hrelT'pT') (λ h, h.trans hrelT'pT'),
have hrelTT : rel obj T T, from hrelTT'.trans hrelT'T,
have hc't : T.to_partition.colg c ≤ t, from htmax _ T hrelTT _ hc rfl,
have hoT'T : T'.const obj 0 = T.const obj 0, from const_obj_eq_of_rel_of_rel _ hrelT'T hrelTT',
have hfickle : ∀ i, T.to_partition.rowg i ≠ T'.to_partition.rowg i → T.const i 0 = 0,
  from const_eq_zero_of_rowg_ne_of_rel_self obj hrelTT' hrelT'T,
have hobj : T.const obj 0 = T'.const obj 0, from const_obj_eq_of_rel_of_rel _ hrelTT' hrelT'T,
have hflat : T.flat = T'.flat, from flat_eq_of_rel obj hrelTT',
have hrobj : T.to_partition.rowg obj = T'.to_partition.rowg obj, from rowg_obj_eq_of_rel _ hrelTT',
have hs : T.to_partition.rowg r = T'.to_partition.colg c', by simpa using hT'Tr,
have hc'res : T'.to_partition.colg c' ∈ T'.restricted,
  from hs ▸ restricted_eq_of_rel _ hrelTT' ▸ (find_pivot_row_spec hr).2.1,
have hc'obj0 : 0 < T'.to_matrix obj c', by simpa [hc'res] using find_pivot_column_spec hcT',
have hcres : T.to_partition.colg c ∈ T.restricted,
  from colg_mem_restricted_of_rel_self obj hrelTT hc,
have hcobj0 : 0 < to_matrix T obj c, by simpa [hcres] using find_pivot_column_spec hc,
have hrc0 : T.to_matrix r c < 0,
  from inv_neg'.1 $ neg_of_mul_neg_left (find_pivot_row_spec hr).2.2.1 (le_of_lt hcobj0),
have nonpos_of_colg_ne : ∀ j, T'.to_partition.colg j ≠ T.to_partition.colg j → j ≠ c' →
    T'.to_matrix obj j ≤ 0,
  from λ j hj hjc',
    let ⟨T₃, hT₃⟩ := (colg_eq_or_exists_mem_pivot_column obj hrelTT').resolve_left hj in
    nonpos_of_lt_find_pivot_column hcT' hc'res
      (lt_of_le_of_ne
        (hct.symm ▸ hT₃.2.2.1 ▸ htmax _ T₃ (hT₃.1.elim (λ h, h.symm ▸ hrelTT'')
          (λ h, h.trans (hrelT'T.trans hT₃.2.1))) _ hT₃.2.2.2 rfl)
        (by rwa [ne.def, T'.to_partition.injective_colg.eq_iff])),
have nonpos_of_colg_eq : ∀ j, j ≠ c' →
    T'.to_partition.colg j = T.to_partition.colg c → T'.to_matrix obj j ≤ 0,
  from λ j hjc' hj,
    if hjc : j = c
      then by clear_aux_decl; subst j; exact nonpos_of_lt_find_pivot_column hcT' hc'res
        (lt_of_le_of_ne
          (hj.symm ▸ hct.symm ▸ htmax _ _ hrelTT _ hc rfl)
          (hs ▸ hj.symm ▸ colg_ne_rowg _ _ _))
      else let ⟨T₃, hT₃⟩ := (colg_eq_or_exists_mem_pivot_column obj hrelTT').resolve_left
        (show T'.to_partition.colg j ≠ T.to_partition.colg j,
          by simpa [hj, T.to_partition.injective_colg.eq_iff, eq_comm] using hjc) in
      nonpos_of_lt_find_pivot_column hcT' hc'res
        (lt_of_le_of_ne
          (hct.symm ▸ hT₃.2.2.1 ▸ htmax _ T₃ (hT₃.1.elim (λ h, h.symm ▸ hrelTT'')
            (λ h, h.trans (hrelT'T.trans hT₃.2.1))) _ hT₃.2.2.2 rfl)
          (by rwa [ne.def, T'.to_partition.injective_colg.eq_iff])),
have unique_row : ∀ i ≠ r, T.const i 0 = 0 → T.to_partition.rowg i ≠ T'.to_partition.rowg i →
    0 ≤ T.to_matrix i c,
  from λ i hir hi0 hrow,
    let ⟨T₃, c₃, hc₃, hrow₃, hrelT₃T, hrelTT₃⟩ :=
      exists_mem_pivot_column_of_rowg_ne _ hrelTT' hrelT'T hrow in
    have hrelT₃T₃ : rel obj T₃ T₃, from hrelT₃T.trans hrelTT₃,
    nonneg_of_lt_find_pivot_row (by exact hcobj0)
      (by rw [← hrow₃, ← restricted_eq_of_rel _ hrelT₃T];
        exact colg_mem_restricted_of_rel_self _ hrelT₃T₃ hc₃) hc hr hi0
      (lt_of_le_of_ne (by rw [hs, hct, ← hrow₃]; exact htmax _ _ hrelT₃T₃ _ hc₃ rfl)
        (by simpa [T.to_partition.injective_rowg.eq_iff])),
not_unique_row_and_unique_col obj hcobj0 hc'obj0 hrc0 hflat hs hrobj hfickle hobj
  nonpos_of_colg_ne nonpos_of_colg_eq unique_row

noncomputable instance fintype_rel (T : tableau m n) : fintype {T' | rel obj T' T} :=
fintype.of_injective (λ T', T'.val.to_partition)
  (λ T₁ T₂ h, subtype.eq $ tableau.ext
    (by rw [flat_eq_of_rel _ T₁.2, flat_eq_of_rel _ T₂.2]) h
    (by rw [restricted_eq_of_rel _ T₁.2, restricted_eq_of_rel _ T₂.2]))

lemma rel_wf (m n : ℕ) (obj : fin m): well_founded (@rel m n obj) :=
subrelation.wf
  (show subrelation (@rel m n obj) (measure (λ T, fintype.card {T' | rel obj T' T})),
    from assume T₁ T₂ h,
    set.card_lt_card (set.ssubset_iff_subset_not_subset.2 ⟨λ T' hT', hT'.trans h,
      classical.not_forall.2 ⟨T₁, λ h', rel.irrefl _ (h' h)⟩⟩))
  (measure_wf (λ T, fintype.card {T' | rel obj T' T}))

end blands_rule

@[derive _root_.decidable_eq] inductive termination : Type
| while     : termination
| unbounded : termination
| optimal   : termination

open termination

instance : has_repr termination := ⟨λ t, termination.cases_on t "while" "unbounded" "optimal"⟩

instance : fintype termination := ⟨⟨quotient.mk [while, unbounded, optimal], dec_trivial⟩,
  λ x, by cases x; exact dec_trivial⟩

open termination

/-- The simplex algorithm -/
def simplex (w : tableau m n → bool) (obj : fin m) : Π (T : tableau m n) (hT : feasible T),
  tableau m n × termination
| T := λ hT, cond (w T)
  (match find_pivot_column T obj, @feasible_of_mem_pivot_row_and_column _ _ _ obj hT,
      @rel.pivot m n obj _ hT with
    | none,   hc, hrel := (T, optimal)
    | some c, hc, hrel :=
      match find_pivot_row T obj c, @hc _ rfl, (λ r, @hrel r c rfl) with
      | none,   hr, hrel := (T, unbounded)
      | some r, hr, hrel := have wf : rel obj (pivot T r c) T, from hrel _ rfl,
        simplex (T.pivot r c) (hr rfl)
      end
    end)
  (T, while)
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, rel_wf m n obj⟩],
  dec_tac := tactic.assumption}

lemma simplex_pivot {w : tableau m n → bool} {T : tableau m n} (hT : feasible T)
  (hw : w T = tt) {obj : fin m} {r : fin m} {c : fin n}
  (hc : c ∈ find_pivot_column T obj) (hr : r ∈ find_pivot_row T obj c) :
  (T.pivot r c).simplex w obj  (feasible_of_mem_pivot_row_and_column hT hc hr) =
  T.simplex w obj hT  :=
by conv_rhs { rw simplex };
  simp [hw, show _ = _, from hr, show _ = _, from hc, simplex._match_1, simplex._match_2]

lemma simplex_spec_aux (w : tableau m n → bool) (obj : fin m) :
  Π (T : tableau m n) (hT : feasible T),
  ((T.simplex w obj hT).2 = while ∧ w (T.simplex w obj hT).1 = ff) ∨
  ((T.simplex w obj hT).2 = optimal ∧ w (T.simplex w obj hT).1 = tt ∧
    find_pivot_column (T.simplex w obj hT).1 obj = none) ∨
  ((T.simplex w obj hT).2 = unbounded ∧ w (T.simplex w obj hT).1 = tt ∧
    ∃ c, c ∈ find_pivot_column (T.simplex w obj hT).1 obj ∧
    find_pivot_row (T.simplex w obj hT).1 obj c = none)
| T := λ hT,
  begin
    cases hw : w T,
    { rw simplex, simp [hw] },
    { cases hc : find_pivot_column T obj with c,
      { rw simplex, simp [hc, hw, simplex._match_1] },
      { cases hr : find_pivot_row T obj c with r,
        { rw simplex, simp [hr, hc, hw, simplex._match_1, simplex._match_2] },
        { rw [← simplex_pivot hT hw hc hr],
          exact have wf : rel obj (T.pivot r c) T, from rel.pivot hT hc hr,
            simplex_spec_aux _ _ } } }
  end
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, rel_wf m n obj⟩],
  dec_tac := tactic.assumption}

lemma simplex_while_eq_ff {w : tableau m n → bool} {T : tableau m n} {hT : feasible T}
  {obj : fin m} (hw : w T = ff) : T.simplex w obj hT = (T, while) :=
by rw [simplex, hw]; refl

lemma simplex_find_pivot_column_eq_none {w : tableau m n → bool} {T : tableau m n} {hT : feasible T}
  (hw : w T = tt) {obj : fin m} (hc : find_pivot_column T obj = none) :
  T.simplex w obj hT = (T, optimal) :=
by rw simplex; simp [hc, hw, simplex._match_1]

lemma simplex_find_pivot_row_eq_none {w : tableau m n → bool} {T : tableau m n} {hT : feasible T}
  {obj : fin m} (hw : w T = tt) {c} (hc : c ∈ find_pivot_column T obj)
  (hr : find_pivot_row T obj c = none) : T.simplex w obj hT = (T, unbounded) :=
by rw simplex; simp [hw, show _ = _, from hc, hr, simplex._match_1, simplex._match_2]

lemma simplex_induction (P : tableau m n → Prop) (w : tableau m n → bool) (obj : fin m):
  Π {T : tableau m n} (hT : feasible T)  (h0 : P T)
  (hpivot : ∀ {T' r c}, w T' = tt → c ∈ find_pivot_column T' obj → r ∈ find_pivot_row T' obj c
    → feasible T' → P T' → P (T'.pivot r c)),
  P (T.simplex w obj hT).1
| T := λ hT h0 hpivot,
  begin
    cases hw : w T,
    { rwa [simplex_while_eq_ff hw] },
    { cases hc : find_pivot_column T obj with c,
      { rwa [simplex_find_pivot_column_eq_none hw hc] },
      { cases hr : find_pivot_row T obj c with r,
        { rwa simplex_find_pivot_row_eq_none hw hc hr },
        { rw [← simplex_pivot _ hw hc hr],
          exact have wf : rel obj (pivot T r c) T, from rel.pivot hT hc hr,
            simplex_induction (feasible_of_mem_pivot_row_and_column hT hc hr)
              (hpivot hw hc hr hT h0) @hpivot } } }
  end
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, rel_wf m n obj⟩],
  dec_tac := `[tauto]}

@[simp] lemma feasible_simplex {w : tableau m n → bool} {T : tableau m n}
  {hT : feasible T} {obj : fin m} : feasible (T.simplex w obj hT).1 :=
simplex_induction feasible _ _ hT hT
  (λ _ _ _ _ hc hr _ hT', feasible_of_mem_pivot_row_and_column hT' hc hr)

@[simp] lemma simplex_simplex {w : tableau m n → bool} {T : tableau m n} {hT : feasible T}
  {obj : fin m} : (T.simplex w obj hT).1.simplex w obj feasible_simplex = T.simplex w obj hT :=
simplex_induction (λ T', ∀ (hT' : feasible T'), T'.simplex w obj hT' = T.simplex w obj hT) w _ _
  (λ _, rfl) (λ T' r c hw hc hr hT' ih hpivot, by rw [simplex_pivot hT' hw hc hr, ih]) _

/-- `simplex` does not move the row variable it is trying to maximise. -/
@[simp] lemma rowg_simplex (T : tableau m n) (hT : feasible T) (w : tableau m n → bool)
  (obj : fin m) : (T.simplex w obj hT).1.to_partition.rowg obj = T.to_partition.rowg obj :=
simplex_induction (λ T', T'.to_partition.rowg obj = T.to_partition.rowg obj) _ _ _ rfl
  (λ T' r c hw hc hr, by simp [rowg_swap_of_ne _ (find_pivot_row_spec hr).1])

@[simp] lemma flat_simplex (T : tableau m n) (hT : feasible T) (w : tableau m n → bool)
  (obj : fin m) : (T.simplex w obj hT).1.flat = T.flat :=
simplex_induction (λ T', T'.flat = T.flat) w obj _ rfl
  (λ T' r c hw hc hr hT' ih,
    have T'.to_matrix r c ≠ 0,
      from λ h, by simpa [h, lt_irrefl] using find_pivot_row_spec hr,
    by rw [flat_pivot this, ih])

@[simp] lemma restricted_simplex (T : tableau m n) (hT : feasible T) (w : tableau m n → bool)
  (obj : fin m) : (T.simplex w obj hT).1.restricted = T.restricted :=
simplex_induction (λ T', T'.restricted = T.restricted) _ _ _ rfl (by simp { contextual := tt })

@[simp] lemma sol_set_simplex (T : tableau m n) (hT : feasible T) (w : tableau m n → bool)
  (obj : fin m) : (T.simplex w obj hT).1.sol_set = T.sol_set :=
by simp [sol_set]

@[simp] lemma of_col_simplex_zero_mem_sol_set {w : tableau m n → bool} {T : tableau m n}
  {hT : feasible T} {obj : fin m} : (T.simplex w obj hT).1.of_col 0 ∈ sol_set T :=
by rw [← sol_set_simplex, of_col_zero_mem_sol_set_iff]; exact feasible_simplex

@[simp] lemma of_col_simplex_rowg {w : tableau m n → bool} {T : tableau m n}
  {hT : feasible T} {obj : fin m} (x : cvec n) :
  (T.simplex w obj hT).1.of_col x (T.to_partition.rowg obj) =
  ((T.simplex w obj hT).1.to_matrix ⬝ x + (T.simplex w obj hT).1.const) obj :=
by rw [← of_col_rowg (T.simplex w obj hT).1 x obj, rowg_simplex]

@[simp] lemma is_unbounded_above_simplex {T : tableau m n} {hT : feasible T} {w : tableau m n → bool}
  {obj : fin m} {v : fin (m + n)} : is_unbounded_above (T.simplex w obj hT).1 v ↔
  is_unbounded_above T v := by simp [is_unbounded_above]

@[simp] lemma is_optimal_simplex {T : tableau m n} {hT : feasible T} {w : tableau m n → bool}
  {obj : fin m} {x : cvec (m + n)} {v : fin (m + n)} : is_optimal (T.simplex w obj hT).1 x v ↔
  is_optimal T x v := by simp [is_optimal]

lemma termination_eq_while_iff {T : tableau m n} {hT : feasible T} {w : tableau m n → bool}
  {obj : fin m} : (T.simplex w obj hT).2 = while ↔ w (T.simplex w obj hT).1 = ff :=
by have := simplex_spec_aux w obj T hT; finish

lemma termination_eq_optimal_iff_find_pivot_column_eq_none {T : tableau m n}
  {hT : feasible T} {w : tableau m n → bool} {obj : fin m} : (T.simplex w obj hT).2 = optimal ↔
  w (T.simplex w obj hT).1 = tt ∧ find_pivot_column (T.simplex w obj hT).1 obj = none :=
by have := simplex_spec_aux w obj T hT; finish

lemma termination_eq_unbounded_iff_find_pivot_row_eq_none {T : tableau m n} {hT : feasible T}
  {w : tableau m n → bool} {obj : fin m} : (T.simplex w obj hT).2 = unbounded ↔
  w (T.simplex w obj hT).1 = tt ∧ ∃ c, c ∈ find_pivot_column (T.simplex w obj hT).1 obj ∧
  find_pivot_row (T.simplex w obj hT).1 obj c = none :=
by have := simplex_spec_aux w obj T hT; finish

lemma termination_eq_unbounded_iff_aux {T : tableau m n} {hT : feasible T}
  {w : tableau m n → bool} {obj : fin m} : (T.simplex w obj hT).2 = unbounded →
  w (T.simplex w obj hT).1 = tt ∧
  is_unbounded_above T (T.to_partition.rowg obj) :=
begin
  rw termination_eq_unbounded_iff_find_pivot_row_eq_none,
  rintros ⟨_, c, hc⟩,
  simpa * using find_pivot_row_eq_none feasible_simplex hc.2 hc.1
end

lemma termination_eq_optimal_iff {T : tableau m n} {hT : feasible T}
  {w : tableau m n → bool} {obj : fin m} : (T.simplex w obj hT).2 = optimal ↔
  w (T.simplex w obj hT).1 = tt ∧
  is_optimal T ((T.simplex w obj hT).1.of_col 0) (T.to_partition.rowg obj) :=
begin
  rw [termination_eq_optimal_iff_find_pivot_column_eq_none],
  split,
  { rintros ⟨_, hc⟩,
    simpa * using find_pivot_column_eq_none feasible_simplex hc },
  { cases ht : (T.simplex w obj hT).2,
    { simp [*, termination_eq_while_iff] at * },
    { cases termination_eq_unbounded_iff_aux ht,
      simp [*, not_optimal_of_unbounded_above right] },
    { simp [*, termination_eq_optimal_iff_find_pivot_column_eq_none] at * } }
end

lemma termination_eq_unbounded_iff {T : tableau m n} {hT : feasible T}
  {w : tableau m n → bool} {obj : fin m} : (T.simplex w obj hT).2 = unbounded ↔
  w (T.simplex w obj hT).1 = tt ∧ is_unbounded_above T (T.to_partition.rowg obj) :=
⟨termination_eq_unbounded_iff_aux,
  begin
    have := @not_optimal_of_unbounded_above m n (T.simplex w obj hT).1 (T.to_partition.rowg obj)
      ((T.simplex w obj hT).1.of_col 0),
    cases ht : (T.simplex w obj hT).2;
    simp [termination_eq_optimal_iff, termination_eq_while_iff, *] at *
  end⟩

end tableau
