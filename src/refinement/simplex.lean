import .tableau order.lexicographic

open matrix fintype finset function pequiv partition
variables {m n : ℕ}
variables {X : ℕ → ℕ → Type} [is_tableau X]

local notation `rvec`:2000 n := matrix (fin 1) (fin n) ℚ
local notation `cvec`:2000 m := matrix (fin m) (fin 1) ℚ
local infix ` ⬝ `:70 := matrix.mul
local postfix `ᵀ` : 1500 := transpose

namespace is_tableau

def to_lex (T : X m n) (c : fin n) (r' : fin m) : lex ℚ (fin (m + n)) :=
(abs ((const T) r' 0 / (to_matrix T) r' c), (to_partition T).rowg r')

lemma pivot_col_spec {T : X m n} {obj : fin m} {c : fin n} :
  c ∈ pivot_col T obj → (((to_matrix T) obj c ≠ 0 ∧ (to_partition T).colg c ∉ (restricted T))
  ∨ (0 < (to_matrix T) obj c ∧ (to_partition T).colg c ∈ (restricted T))) ∧ c ∉ (dead T) :=
by simp only [to_matrix, const, to_partition, restricted, feasible, to_tableau_pivot,
  to_tableau_pivot_col] at *; exact tableau.pivot_col_spec

lemma nonpos_of_lt_pivot_col {T : X m n} {obj : fin m} {c j : fin n}
  (hc : c ∈ pivot_col T obj) (hcres : (to_partition T).colg c ∈ (restricted T))
  (hdead : j ∉ (dead T)) (hjc : (to_partition T).colg j < (to_partition T).colg c) :
  (to_matrix T) obj j ≤ 0 :=
by simp only [to_matrix, const, to_partition, restricted, feasible, to_tableau_pivot,
  to_tableau_pivot_col] at *; exact tableau.nonpos_of_lt_pivot_col hc hcres hdead hjc

lemma pivot_col_eq_none {T : X m n} {obj : fin m} (hT : (feasible T))
  (h : pivot_col T obj = none) : 
  (is_optimal T) ((of_col T) 0) ((to_partition T).rowg obj) :=
by simp only [to_matrix, const, to_partition, restricted, feasible, to_tableau_pivot,
  to_tableau_pivot_col] at *; exact tableau.pivot_col_eq_none hT h

lemma pivot_row_spec {T : X m n} {obj r : fin m} {c : fin n} :
  r ∈ pivot_row T obj c →
  obj ≠ r ∧ (to_partition T).rowg r ∈ (restricted T) ∧
  (to_matrix T) obj c / (to_matrix T) r c < 0 ∧
  (∀ r' : fin m, obj ≠ r' → (to_partition T).rowg r' ∈ (restricted T) →
    (to_matrix T) obj c / (to_matrix T) r' c < 0 →
  abs ((const T) r 0 / (to_matrix T) r c) ≤ abs ((const T) r' 0 / (to_matrix T) r' c)) :=
by simp only [to_matrix, const, to_partition, restricted, feasible, to_tableau_pivot,
  to_tableau_pivot_col, to_tableau_pivot_row] at *; exact tableau.pivot_row_spec

lemma nonneg_of_lt_pivot_row {T : X m n} {obj : fin m} {r i : fin m} {c : fin n}
  (hc0 : 0 < (to_matrix T) obj c) (hres : (to_partition T).rowg i ∈ (restricted T))
  (hc : c ∈ pivot_col T obj) (hr : r ∈ pivot_row T obj c)
  (hconst : (const T) i 0 = 0)
  (hjc : (to_partition T).rowg i < (to_partition T).rowg r) :
  0 ≤ (to_matrix T) i c :=
by simp only [to_matrix, const, to_partition, restricted, feasible, to_tableau_pivot,
    to_tableau_pivot_col, to_tableau_pivot_row] at *;
  exact tableau.nonneg_of_lt_pivot_row hc0 hres hc hr hconst hjc

lemma ne_zero_of_mem_pivot_row {T : X m n} {obj r : fin m} {c : fin n}
  (hr : r ∈ pivot_row T obj c) : (to_matrix T) r c ≠ 0 :=
assume hrc, by simpa [lt_irrefl, hrc] using pivot_row_spec hr

lemma ne_zero_of_mem_pivot_col {T : X m n} {obj : fin m} {c : fin n}
  (hc : c ∈ pivot_col T obj) : (to_matrix T) obj c ≠ 0 :=
λ h, by simpa [h, lt_irrefl] using pivot_col_spec hc

lemma pivot_row_eq_none {T : X m n} {obj : fin m} {c : fin n} (hT : (feasible T))
  (hrow : pivot_row T obj c = none) (hs : c ∈ pivot_col T obj) :
  (is_unbounded_above T) ((to_partition T).rowg obj) :=
by simp only [to_matrix, const, to_partition, restricted, feasible, to_tableau_pivot,
    to_tableau_pivot_col, to_tableau_pivot_row] at *;
  exact tableau.pivot_row_eq_none hT hrow hs

def feasible_of_mem_pivot_row_and_col {T : X m n} {obj : fin m} (hT : (feasible T)) {c}
  (hc : c ∈ pivot_col T obj) {r} (hr : r ∈ pivot_row T obj c) :
  feasible (pivot T r c) :=
begin
  have := pivot_col_spec hc,
  have := pivot_row_spec hr,
  have := @feasible_simplex_pivot _ _ _ _ _ obj hT r c,
  tauto
end

def rel (obj : fin m) : Π (T₁ T₂ : X m n), Prop :=
inv_image (tableau.rel obj) to_tableau

lemma rel_wf (m n : ℕ) (obj : fin m): well_founded (@rel m n X _ obj) :=
inv_image.wf _ (tableau.rel_wf _ _ _)

lemma rel.pivot {obj : fin m} {T : X m n} : feasible T → ∀ {r : fin m} {c : fin n},
  c ∈ pivot_col T obj → r ∈ pivot_row T obj c → rel obj (pivot T r c) T :=
by simp only [to_matrix, const, to_partition, restricted, feasible, to_tableau_pivot,
    to_tableau_pivot_col, to_tableau_pivot_row, rel, inv_image] at *;
  exact tableau.rel.pivot

open tableau.termination
local notation `termination`:2000 := tableau.termination

/-- The simplex algorithm -/
def simplex (w : X m n → bool) (obj : fin m) : Π (T : X m n) (hT : feasible T),
  X m n × termination n
| T := λ hT, cond (w T)
  (match pivot_col T obj, @feasible_of_mem_pivot_row_and_col _ _ _ _ _ obj hT,
      @rel.pivot m n X _ obj _ hT with
    | none,   hc, hrel := (T, optimal)
    | some c, hc, hrel :=
      match pivot_row T obj c, @hc _ rfl, (λ r, @hrel r c rfl) with
      | none,   hr, hrel := (T, unbounded c)
      | some r, hr, hrel := have wf : rel obj (pivot T r c) T, from hrel _ rfl,
        simplex (pivot T r c) (hr rfl)
      end
    end)
  (T, while)
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, rel_wf m n obj⟩],
  dec_tac := tactic.assumption}

lemma simplex_pivot {w : X m n → bool} {T : X m n} (hT : feasible T)
  (hw : w T = tt) {obj : fin m} {r : fin m} {c : fin n}
  (hc : c ∈ pivot_col T obj) (hr : r ∈ pivot_row T obj c) :
  simplex w obj (pivot T r c) (feasible_of_mem_pivot_row_and_col hT hc hr) =
  simplex w obj T hT  :=
by conv_rhs { rw simplex };
  simp [hw, show _ = _, from hr, show _ = _, from hc, simplex._match_1, simplex._match_2]

lemma simplex_spec_aux (w : X m n → bool) (obj : fin m) :
  Π (T : X m n) (hT : feasible T),
  ((simplex w obj T hT).2 = while ∧ w (simplex w obj T hT).1 = ff) ∨
  ((simplex w obj T hT).2 = optimal ∧ w (simplex w obj T hT).1 = tt ∧
    pivot_col (simplex w obj T hT).1 obj = none) ∨
  ∃ c, ((simplex w obj T hT).2 = unbounded c ∧ w (simplex w obj T hT).1 = tt ∧
    c ∈ pivot_col (simplex w obj T hT).1 obj ∧
    pivot_row (simplex w obj T hT).1 obj c = none)
| T := λ hT,
  begin
    cases hw : w T,
    { rw simplex, simp [hw] },
    { cases hc : pivot_col T obj with c,
      { rw simplex, simp [hc, hw, simplex._match_1] },
      { cases hr : pivot_row T obj c with r,
        { rw simplex,
          simp [hr, hc, hw, simplex._match_1, simplex._match_2] },
        { rw [← simplex_pivot hT hw hc hr],
          exact have wf : rel obj (pivot T r c) T, from rel.pivot hT hc hr,
            simplex_spec_aux _ _ } } }
  end
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, rel_wf m n obj⟩],
  dec_tac := tactic.assumption}

lemma simplex_while_eq_ff {w : X m n → bool} {T : X m n} {hT : feasible T}
  {obj : fin m} (hw : w T = ff) : simplex w obj T hT = (T, while) :=
by rw [simplex, hw]; refl

lemma simplex_pivot_col_eq_none {w : X m n → bool} {T : X m n} {hT : feasible T}
  (hw : w T = tt) {obj : fin m} (hc : pivot_col T obj = none) :
  simplex w obj T hT = (T, optimal) :=
by rw simplex; simp [hc, hw, simplex._match_1]

lemma simplex_pivot_row_eq_none {w : X m n → bool} {T : X m n} {hT : feasible T}
  {obj : fin m} (hw : w T = tt) {c} (hc : c ∈ pivot_col T obj)
  (hr : pivot_row T obj c = none) : simplex w obj T hT = (T, unbounded c) :=
by rw simplex; simp [hw, show _ = _, from hc, hr, simplex._match_1, simplex._match_2]

lemma simplex_induction (P : X m n → Prop) (w : X m n → bool) (obj : fin m):
  Π {T : X m n} (hT : feasible T)  (h0 : P T)
  (hpivot : ∀ {T' r c}, w T' = tt → c ∈ pivot_col T' obj → r ∈ pivot_row T' obj c
    → feasible T' → P T' → P (pivot T' r c)),
  P (simplex w obj T hT).1
| T := λ hT h0 hpivot,
  begin
    cases hw : w T,
    { rwa [simplex_while_eq_ff hw] },
    { cases hc : pivot_col T obj with c,
      { rwa [simplex_pivot_col_eq_none hw hc] },
      { cases hr : pivot_row T obj c with r,
        { rwa simplex_pivot_row_eq_none hw hc hr },
        { rw [← simplex_pivot _ hw hc hr],
          exact have wf : rel obj (pivot T r c) T, from rel.pivot hT hc hr,
            simplex_induction (feasible_of_mem_pivot_row_and_col hT hc hr)
              (hpivot hw hc hr hT h0) @hpivot } } }
  end
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, rel_wf m n obj⟩],
  dec_tac := `[tauto]}

@[simp] lemma feasible_simplex {w : X m n → bool} {T : X m n}
  {hT : feasible T} {obj : fin m} : feasible (simplex w obj T hT).1 :=
simplex_induction feasible _ _ hT hT
  (λ _ _ _ _ hc hr _ hT', feasible_of_mem_pivot_row_and_col hT' hc hr)

@[simp] lemma simplex_simplex {w : X m n → bool} {T : X m n} {hT : feasible T}
  {obj : fin m} : simplex w obj (simplex w obj T hT).1 feasible_simplex = simplex w obj T hT :=
simplex_induction (λ T', ∀ (hT' : feasible T'), simplex w obj T' hT' = simplex w obj T hT) w _ _
  (λ _, rfl) (λ T' r c hw hc hr hT' ih hpivot, by rw [simplex_pivot hT' hw hc hr, ih]) _

/-- `simplex` does not move the row variable it is trying to maximise. -/
@[simp] lemma rowg_simplex (T : X m n) (hT : feasible T) (w : X m n → bool)
  (obj : fin m) : (to_partition (simplex w obj T hT).1).rowg obj = (to_partition T).rowg obj :=
simplex_induction (λ T', (to_partition T').rowg obj = (to_partition T).rowg obj) _ _ _ rfl
  (λ T' r c hw hc hr, by simp [rowg_swap_of_ne _ (pivot_row_spec hr).1])

@[simp] lemma flat_simplex (T : X m n) (hT : feasible T) (w : X m n → bool)
  (obj : fin m) : flat (simplex w obj T hT).1 = (flat T) :=
simplex_induction (λ T', flat T' = (flat T)) w obj _ rfl
  (λ T' r c hw hc hr hT' ih,
    have to_matrix T' r c ≠ 0,
      from λ h, by simpa [h, lt_irrefl] using pivot_row_spec hr,
    by rw [flat_pivot this, ih])

@[simp] lemma restricted_simplex (T : X m n) (hT : feasible T) (w : X m n → bool)
  (obj : fin m) : restricted (simplex w obj T hT).1 = (restricted T) :=
simplex_induction (λ T', restricted T' = (restricted T)) _ _ _ rfl (by simp { contextual := tt })

@[simp] lemma dead_simplex (T : X m n) (hT : feasible T) (w : X m n → bool)
  (obj : fin m) : dead (simplex w obj T hT).1 = (dead T) :=
simplex_induction (λ T', dead T' = (dead T)) _ _ _ rfl (by simp { contextual := tt })

@[simp] lemma res_set_simplex (T : X m n) (hT : feasible T) (w : X m n → bool)
  (obj : fin m) : res_set (simplex w obj T hT).1 = res_set T :=
simplex_induction (λ T', (res_set T') = (res_set T)) w obj _ rfl
  (λ T' r c hw hc hr, by simp [res_set_pivot (ne_zero_of_mem_pivot_row hr)] {contextual := tt})

@[simp] lemma dead_set_simplex (T : X m n) (hT : feasible T) (w : X m n → bool)
  (obj : fin m) : dead_set (simplex w obj T hT).1 = dead_set T :=
simplex_induction (λ T', dead_set T' = dead_set T) w obj _ rfl
  (λ T' r c hw hc hr,
    by simp [dead_set_pivot (ne_zero_of_mem_pivot_row hr) (pivot_col_spec hc).2] {contextual := tt})

@[simp] lemma sol_set_simplex (T : X m n) (hT : feasible T) (w : X m n → bool)
  (obj : fin m) : sol_set (simplex w obj T hT).1 = (sol_set T) :=
by simp [sol_set_eq_res_set_inter_dead_set]

@[simp] lemma of_col_simplex_zero_mem_sol_set {w : X m n → bool} {T : X m n}
  {hT : feasible T} {obj : fin m} : of_col (simplex w obj T hT).1 0 ∈ sol_set T :=
by rw [← sol_set_simplex, of_col_zero_mem_sol_set_iff]; exact feasible_simplex

@[simp] lemma of_col_simplex_rowg {w : X m n → bool} {T : X m n}
  {hT : feasible T} {obj : fin m} (x : cvec n) :
  of_col (simplex w obj T hT).1 x ((to_partition T).rowg obj) =
  (to_matrix (simplex w obj T hT).1 ⬝ x + const (simplex w obj T hT).1) obj :=
by rw [← of_col_rowg (simplex w obj T hT).1 x obj, rowg_simplex]

@[simp] lemma is_unbounded_above_simplex {T : X m n} {hT : feasible T} {w : X m n → bool}
  {obj : fin m} {v : fin (m + n)} : is_unbounded_above (simplex w obj T hT).1 v ↔
  is_unbounded_above T v := by simp [is_unbounded_above]

@[simp] lemma is_optimal_simplex {T : X m n} {hT : feasible T} {w : X m n → bool}
  {obj : fin m} {x : cvec (m + n)} {v : fin (m + n)} : is_optimal (simplex w obj T hT).1 x v ↔
  is_optimal T x v := by simp [is_optimal]

lemma termination_eq_while_iff {T : X m n} {hT : feasible T} {w : X m n → bool}
  {obj : fin m} : (simplex w obj T hT).2 = while ↔ w (simplex w obj T hT).1 = ff :=
by have := simplex_spec_aux w obj T hT; finish

lemma termination_eq_optimal_iff_pivot_col_eq_none {T : X m n}
  {hT : feasible T} {w : X m n → bool} {obj : fin m} : (simplex w obj T hT).2 = optimal ↔
  w (simplex w obj T hT).1 = tt ∧ pivot_col (simplex w obj T hT).1 obj = none :=
by rcases simplex_spec_aux w obj T hT with _ | ⟨_, _, _⟩ | ⟨⟨_, _⟩, _, _, _, _⟩; simp * at *

lemma termination_eq_unbounded_iff_pivot_row_eq_none {T : X m n} {hT : feasible T}
  {w : X m n → bool} {obj : fin m} {c : fin n} :
  (simplex w obj T hT).2 = unbounded c ↔
  w (simplex w obj T hT).1 = tt ∧ c ∈ pivot_col (simplex w obj T hT).1 obj ∧
    pivot_row (simplex w obj T hT).1 obj c = none :=
by split; intros; rcases simplex_spec_aux w obj T hT with
  _ | ⟨_, _, _⟩ | ⟨⟨⟨_, _⟩, _⟩, _, _, _, _⟩; simp * at *

lemma unbounded_of_termination_eq_unbounded {T : X m n} {hT : feasible T}
  {w : X m n → bool} {obj : fin m} {c : fin n} : (simplex w obj T hT).2 = unbounded c →
  w (simplex w obj T hT).1 = tt ∧
  is_unbounded_above T ((to_partition T).rowg obj) :=
begin
  rw termination_eq_unbounded_iff_pivot_row_eq_none,
  rintros ⟨_, hc⟩,
  simpa * using pivot_row_eq_none feasible_simplex hc.2 hc.1
end

lemma termination_eq_optimal_iff {T : X m n} {hT : feasible T}
  {w : X m n → bool} {obj : fin m} : (simplex w obj T hT).2 = optimal ↔
  w (simplex w obj T hT).1 = tt ∧
  is_optimal T (of_col (simplex w obj T hT).1 0) ((to_partition T).rowg obj) :=
begin
  rw [termination_eq_optimal_iff_pivot_col_eq_none],
  split,
  { rintros ⟨_, hc⟩,
    simpa * using pivot_col_eq_none feasible_simplex hc },
  { cases ht : (simplex w obj T hT).2,
    { simp [*, termination_eq_while_iff] at * },
    { cases unbounded_of_termination_eq_unbounded ht,
      simp [*, not_optimal_of_unbounded_above right] },
    { simp [*, termination_eq_optimal_iff_pivot_col_eq_none] at * } }
end

lemma termination_eq_unbounded_iff {T : X m n} {hT : feasible T}
  {w : X m n → bool} {obj : fin m} {c : fin n}: (simplex w obj T hT).2 = unbounded c ↔
  w (simplex w obj T hT).1 = tt ∧ is_unbounded_above T ((to_partition T).rowg obj)
  ∧ c ∈ pivot_col (simplex w obj T hT).1 obj :=
⟨λ hc, and.assoc.1 $ ⟨unbounded_of_termination_eq_unbounded hc,
  (termination_eq_unbounded_iff_pivot_row_eq_none.1 hc).2.1⟩,
begin
  have := @not_optimal_of_unbounded_above m n _ _ (simplex w obj T hT).1 ((to_partition T).rowg obj)
    (of_col (simplex w obj T hT).1 0),
  cases ht : (simplex w obj T hT).2;
  simp [termination_eq_optimal_iff, termination_eq_while_iff,
    termination_eq_unbounded_iff_pivot_row_eq_none, *] at *
end⟩

end is_tableau
