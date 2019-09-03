import data.matrix tactic.ring

open tactic declaration expr binder_info
#print binder_fin

local infix ` ⬝ `:70 := matrix.mul
local postfix `ᵀ` : 1500 := matrix.transpose
#print matrix.mul
--set_option trace.class_instances true
set_option eqn_compiler.max_steps 100000
set_option trace.app_builder true
meta def mk_new_theorem : expr → tactic (expr)
| (pi n b dom cod) := do cod ← mk_new_theorem cod, return (pi n b dom cod)
| `(@matrix.mul %%l %%m %%n %%fl %%fm %%fn ℚ _ _ %%A %%B = %%C) :=
    do k ← mk_fresh_name,
       k' ← mk_local' k implicit `(ℕ),
       fintype_k ← mk_app `fin.fintype [k'],
       D ← mk_fresh_name,
       D_type ← mk_mapp `matrix [n, `(fin %%k'), fn, fintype_k, `(ℚ)],
       B' ← mk_local_def `B B,
       D' ← mk_local' D default D_type,
       B_mul_D ← mk_mapp `matrix.mul [some m, some n, some k', fm, fn,
        fintype_k, `(rat), `(rat.has_mul), `(rat.add_comm_monoid), B', D'],
       trace "x",
       return`(ℕ)
    --    A_mul_B_mul_D ← mk_app `matrix.mul [A, B_mul_D],
    --    C_mul_D ← mk_app `matrix.mul [C, (var (v + 1))],
    --    eeq ← mk_app `eq [A_mul_B_mul_D, C_mul_D],
    -- return (pi k implicit `(nat) (pi D implicit `(matrix (fin %%m) (fin %%(var v)) ℚ) eeq))
    -- let e : expr := `(%%A ⬝ (%%B ⬝ D) = %%C ⬝ D) in
    -- return `(∀ {k : ℕ} (D : matrix (fin %%n) (fin k) ℚ), %%A ⬝ (%%B ⬝ D) = %%C ⬝ D)
| _ := do trace "y", failure

run_cmd do t ← mk_local_pis `(∀ A B : matrix (fin 1) (fin 1) ℚ, A ⬝ B = 1),
  trace (t.1.map to_raw_fmt)

meta def codomain (e : expr) : expr :=
if e.is_pi then codomain e.binding_body else e

#print tactic.interactive.ring
meta def m_assoc_simp_attr : user_attribute :=
{ name := `m_assoc_simp,
  descr := "given a proof A ⬝ B = C, generate the lemma A ⬝ (B ⬝ D) = C ⬝ D, and mark it with a simp attribute",
  after_set := some $ λ n _ _,
    do env ← get_env,
    dec ← get_decl n,
    match dec with
    | thm n _ t _ := let target := codomain t in
      match target with
      | `(@matrix.mul (fin %%l) (fin %%m) (fin %%n) %%_x %%__x %%___x ℚ _ _ %%A %%B = %%C) :=
        sorry
      | _ := trace "declaration has wrong type", fail
    | _ := trace "declaratin is not a theorem", fail
    end }

#reduce  user_attribute_cache_cfg unit
