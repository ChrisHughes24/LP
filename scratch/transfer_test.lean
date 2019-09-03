import .transfer_mathlib

inductive xnat : Type
| zero : xnat
| succ : xnat → xnat

instance : has_zero xnat := ⟨xnat.zero⟩
instance : has_one xnat := ⟨xnat.succ 0⟩

def to_xnat : ℕ → xnat
| 0 := 0
| (nat.succ n) := (to_xnat n).succ

def of_xnat : xnat → ℕ
| 0 := 0
| (xnat.succ n) := (of_xnat n).succ

theorem to_of_xnat : ∀ n, (to_xnat (of_xnat n)) = n
| 0 := rfl
| (xnat.succ n) := congr_arg xnat.succ (to_of_xnat n)

theorem of_to_xnat : ∀ n, (of_xnat (to_xnat n)) = n
| 0 := rfl
| (nat.succ n) := congr_arg nat.succ (of_to_xnat n)

def rel (x : xnat) (n : ℕ) : Prop := to_xnat n = x

lemma rel_zero : rel 0 0 := eq.refl _

run_cmd do rds ← transfer.analyse_decls
  [``rel_zero],
    rds_fmt ← rds.mmap has_to_tactic_format.to_tactic_format,
    tactic.trace (((rds_fmt.map to_string).intersperse "; ").to_string),
  transfer.compute_transfer rds [] `(rel (0 : xnat)) >>= tactic.trace

lemma rel_succ : (rel ⇒ rel) xnat.succ nat.succ :=
sorry
lemma rel_one : rel 1 1 := eq.refl _

instance : has_add xnat :=
⟨λ m n, by induction n; [exact m, exact n_ih.succ]⟩

theorem to_xnat_add (m) : ∀ n, to_xnat (m + n) = to_xnat m + to_xnat n
| 0 := rfl
| (nat.succ n) := congr_arg xnat.succ (to_xnat_add n)

lemma rel_add : (rel ⇒ rel ⇒ rel) (+) (+) :=
sorry

lemma rel_eq : (rel ⇒ rel ⇒ iff) (=) (=) :=
sorry

instance : relator.bi_total rel :=
⟨λ a, ⟨_, to_of_xnat _⟩, λ a, ⟨_, rfl⟩⟩

example : ∀ x y : xnat, x + y = y + x :=
begin
  transfer.transfer [``relator.rel_forall_of_total, ``rel_eq, ``rel_add],
  simp [add_comm]
end

run_cmd do rds ← transfer.analyse_decls
  [``relator.rel_forall_of_total, ``rel_eq, ``rel_add],
    rds_fmt ← rds.mmap has_to_tactic_format.to_tactic_format,
    tactic.trace (((rds_fmt.map to_string).intersperse "; ").to_string),
  transfer.compute_transfer rds []
  `(∀ x y : xnat, x + y = y + x)
