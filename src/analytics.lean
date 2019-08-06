import .simplex

open declaration tactic

meta def list_constant (e : expr) : tactic (list name) :=
e.fold (return []) $ λ e _ cs,
do env ← get_env,
cs ← cs,
let n := e.const_name in
match (@option.none ℕ) with
| none := if e.is_constant ∧ n ∉ cs
then return (n :: cs)
else return cs
| _ := return cs
end

meta def const_in_def (n : name) : tactic (list name) :=
do d ← get_decl n,
match d with
| thm _ _ t v      :=
   do lv ← list_constant v.get,
  lt ← list_constant t,
  return (lv ∪ lt)
| defn _ _ t v _ _ :=
  do lv ← list_constant v,
  lt ← list_constant t,
  return (lv ∪ lt)
| cnst _ _ t _     := list_constant t
| ax _ _ t         := list_constant t
end

meta def const_in_def_trans_aux₁ : list name × list (name × list name) →
  tactic (list name × list (name × list name))
| ([], l₂) := pure ([], l₂)
| (l₁, l₂) :=
do l' ← l₁.mmap (λ n, do l ← const_in_def n, return (n, l)),
let l2 := l' ++ l₂,
const_in_def_trans_aux₁ ((l'.map prod.snd).join.erase_dup.diff (l2.map prod.fst), l2)

meta def const_in_def_trans_aux₂ : list name × list name →
  tactic (list name × list name)
| ([], l₂) := pure ([], l₂)
| (l₁, l₂) :=
do l' ← l₁.mmap const_in_def,
let l2 := l₁ ∪ l₂,
const_in_def_trans_aux₂ (l'.join.erase_dup.diff l2, l2)

meta def const_in_def_trans (n : name) : tactic unit :=
do l ← const_in_def_trans_aux₂ ([n], []),
trace l.2.length,
trace (list.insertion_sort (≤) (l.2.map to_string)),
return ()
set_option profiler true

#eval const_in_def_trans `simplex.simplex

#print environment.is_projection
-- #eval const_in_def_trans `zmodp.is_square_iff_is_square_of_mod_four_eq_one
#print int.le.dest
meta def list_all_consts : tactic (list name) :=
do e ← get_env,
let l : list name := environment.fold e []
  (λ d l, match d with
    | thm n _ _ _ := n :: l
    | defn n _ _ _ _ _ := n :: l
    | cnst n _ _ _ := n :: l
    | ax n _ _ := n :: l end),
return l
#print unsigned_sz
meta def list_namespace : tactic unit :=
do l ← list_all_consts,
let m := l.filter (λ n, n.get_prefix = `polynomial),
trace m.length,
trace m,
return ()

#eval (name.get_prefix `nat.prime.mod_add_div).to_string

#eval (name.get_prefix (`nat.mod_add_div) = `polynomial : bool)

#eval list_namespace


-- meta def trans_def_all_aux : list name → rbmap name (rbtree name)
--   → rbmap name (rbtree name) → option (rbmap name (rbtree name))
-- | []      m₁ m₂ := pure m₂
-- | (n::l₁) m₁ m₂ :=
-- do l₁ ← m₁.find n,
-- l₂ ← l₁.mmap m₁.find,
-- let l₃ := l₂.join,
-- if l₃ = l₁ then trans_def_all_aux l₁ (m₁.erase n)
-- else sorry



-- meta def trans_def_list (l : list name) : tactic unit :=
-- do
-- map ← l.mmap (λ n, do l' ← const_in_def n, return (n, l)),
-- m ← trans_def_all_aux [`prod.swap] (pure (rbmap.from_list map)),
-- let result := m.to_list,
-- trace (result.map (λ n, (n.1, n.2.length))),
-- return ()

-- meta def trans_def_list_all : tactic unit :=
-- do l ← list_all_consts,
-- trans_def_list l,
-- return ()
#print if_ctx_simp_congr
-- #eval const_in_def_trans `zmodp.quadratic_reciprocity
#print algebra.sub
-- #eval trans_def_list_all


#exit

#print list.union
meta def const_in_def_trans_aux : Π (n : name), tactic (list name)
| n := do d ← get_decl n,
match d with
| thm _ _ t v := do
  let v := v.get,
  let l := list_constant v,
--  do m ← l.mmap const_in_def_trans_aux,
  return (l).erase_dup
| defn _ _ t v _ _ := do
  let l := list_constant v,
  do m ← l.mmap const_in_def_trans_aux,
  return (l).erase_dup
| d := pure []
end

meta def const_in_def_depth_aux : ℕ → name → list name → tactic (list name)
| 0     n p := pure []
| (m+1) n p :=
do d ← get_decl n,
match d with
| thm _ _ t v := do
  let v := v.get,
  let l := (list_constant v).diff p,
  let q := p ++ l,
  l' ← l.mmap (λ n, const_in_def_depth_aux m n q),
  return (l ++ l'.bind id).erase_dup
| defn _ _ t v _ _ := do
  let l := (list_constant v).diff p,
  let q := p ++ l,
  l' ← l.mmap (λ n, const_in_def_depth_aux m n q),
  return (l ++ l'.bind id).erase_dup
| d := pure []
end

meta def const_in_def_depth_aux' : ℕ → Π n : name, tactic (list name)
| 0     n := pure []
| (m+1) n :=
do d ← get_decl n,
match d with
| thm _ _ t v := do
  let v := v.get,
  let l := list_constant v,
  l' ← l.mmap (const_in_def_depth_aux' m),
  return (l'.bind id ++ l).erase_dup
| defn _ _ t v _ _ := do
  let l := list_constant v,
  l' ← l.mmap (const_in_def_depth_aux' m),
  return (l'.bind id ++ l).erase_dup
| d := pure []
end

meta def const_in_def_depth (m : ℕ) (n : name) : tactic unit :=
do l ← const_in_def_depth_aux m n [],
  trace l.length,
  trace l,
  return ()

meta def const_in_def_depth' (m : ℕ) (n : name) : tactic unit :=
do l ← const_in_def_depth_aux' m n,
  trace l.length,
  trace l,
  return ()

meta def const_in_def_trans (n : name) : tactic unit :=
do l ← const_in_def_trans_aux n,
  trace l.length,
  trace l,
  return ()

set_option profiler true

-- #eval const_in_def_depth' 3 `polynomial.euclidean_domain

-- #eval const_in_def_depth 5 `polynomial.euclidean_domain



-- meta def const_in_def₂  (n : name) : tactic (list name) :=
-- do l ← const_in_def n,
-- m ← l.mmap const_in_def,
-- trace m,
-- return l
#print simp_config

#exit
 data.zmod.basic data.polynomial tactic.norm_num data.rat

instance h {p : ℕ} (hp : nat.prime p) : has_repr (zmodp p hp) := fin.has_repr _

open polynomial
#eval (11 * X ^ 20 + 7 * X ^ 9 + 12 * X + 11 :
  polynomial ℚ) / (22 * X ^ 2 - 1)
