/- Lecture 2.2: Functional Programming — Trees -/

/- Binary trees -/

namespace my_bin_tree

inductive tree (α : Type) : Type
| empty {} : tree
| node (a : α) (l : tree) (r : tree) : tree

export tree (empty node)

def t0 : tree ℕ := node 0 empty empty
def t1 : tree ℕ := node 1 empty empty
def t2 : tree ℕ := node 2 t0 t1

def mirror {α : Type} : tree α → tree α
| empty        := empty
| (node a l r) := node a (mirror r) (mirror l)

lemma mirror_eq_empty_iff {α : Type} : ∀t : tree α, mirror t = empty ↔ t = empty
| empty        := by refl
| (node _ _ _) := by simp [mirror]

lemma mirror_mirror {α : Type} : ∀t : tree α, mirror (mirror t) = t
| empty        := by refl
| (node a l r) :=
  begin
    simp [mirror],
    apply and.intro,
    { apply mirror_mirror l },
    { apply mirror_mirror r }
  end

inductive is_full {α : Type} : tree α → Prop
| empty : is_full empty
| node (a : α) (l r : tree α) (hl : is_full l) (hr : is_full r)
    (empty_iff : l = empty ↔ r = empty) :
    is_full (node a l r)

lemma is_full_singleton {α : Type} (a : α) : is_full (node a empty empty) :=
begin
  apply is_full.node,
  repeat { apply is_full.empty },
  refl
end

lemma is_full_t0 : is_full t0 := is_full_singleton _
lemma is_full_t1 : is_full t1 := is_full_singleton _

lemma is_full_t2 : is_full t2 :=
begin
  unfold t2,
  apply is_full.node,
  exact is_full_t0,
  exact is_full_t1,
  unfold t0 t1,
  simp
end

-- proof by structural induction on `t`
lemma is_full_mirror {α : Type} : ∀t : tree α, is_full t → is_full (mirror t)
| empty        := by intro; assumption
| (node a l r) :=
  begin
    intro full_t,
    cases full_t,
    unfold mirror,
    apply is_full.node,
    repeat { apply is_full_mirror, assumption },
    simp [mirror_eq_empty_iff, *]
  end

-- proof by rule induction on `is_full t`
example {α : Type} : ∀t : tree α, is_full t → is_full (mirror t)
| _ is_full.empty                        := by unfold mirror; exact is_full.empty
| _ (is_full.node a l r hl hr empty_iff) :=
  begin
    unfold mirror,
    apply is_full.node,
    repeat { apply _example, assumption },
    simp [mirror_eq_empty_iff, *]
  end

-- inversion rule
lemma is_full_node_iff {α : Type} (a : α) (l r : tree α) :
  is_full (node a l r) ↔ is_full l ∧ is_full r ∧ (l = empty ↔ r = empty) :=
iff.intro
  (assume h,
    match h with
    | is_full.node a l r h_hl h_hr h_empty_iff := ⟨h_hl, h_hr, h_empty_iff⟩
    end)
  (assume h,
    match h with
    | ⟨h_hl, h_hr, h_empty_iff⟩ := is_full.node a l r h_hl h_hr h_empty_iff
    end)

-- proof using rule inversion
example {α : Type} : ∀t : tree α, is_full t → is_full (mirror t)
| _ is_full.empty                        := by unfold mirror; exact is_full.empty
| _ (is_full.node a l r hl hr empty_iff) :=
  by simp [mirror, is_full_node_iff, _example l hl, _example r hr, mirror_eq_empty_iff, empty_iff]

end my_bin_tree


/- Red-black trees -/

namespace my_red_black_tree

inductive color : Type
| red : color
| black : color

export color (red black)

inductive tree (α : Type) : Type
| empty {} : tree
| node (c : color) (k : ℤ) (v : α) (l : tree) (r : tree) : tree

export tree (empty node)

def lookup {α : Type} (x : ℤ) : tree α → option α
| empty            := none
| (node _ k v l r) :=
  if x < k then lookup l
  else if x > k then lookup r
  else some v

inductive is_balanced {α : Type} : tree α → color → ℕ → Prop
| leaf (c : color) : is_balanced empty c 0
| red (k : ℤ) (v : α) (l : tree α) (r : tree α) (n : ℕ)
    (hl : is_balanced l red n) (hr : is_balanced r red n) :
    is_balanced (node red k v l r) black n
| black c k v l r n (hl : is_balanced l black n) (hr : is_balanced r black n) :
    is_balanced (node black k v l r) c (n + 1)

/- We could continue here and define more operations and show that they preserve the `is_balanced`
invariant. -/

end my_red_black_tree


/- Huffman's algorithm -/

namespace huffman

inductive tree (α : Type)
| leaf : ℕ → α → tree
| inner : ℕ → tree → tree → tree

export tree (leaf inner)

def stored_weight {α : Type} : tree α → ℕ
| (leaf w _)    := w
| (inner w _ _) := w

def unite {α : Type} : tree α → tree α → tree α
| l r := inner (stored_weight l + stored_weight r) l r

def insort {α : Type} (u : tree α) : list (tree α) → list (tree α)
| []        := [u]
| (t :: ts) := if stored_weight u ≤ stored_weight t then u :: t :: ts else t :: insort ts

lemma insort_ne_nil {α : Type} (t : tree α) (ts : list (tree α)) :
  insort t ts ≠ [] :=
begin
  cases ts; simp [insort],
  by_cases (stored_weight t ≤ stored_weight ts_hd); simp *
end

lemma length_insort {α : Type} (t : tree α) :
  ∀ts : list (tree α), list.length (insort t ts) = list.length ts + 1
| []         := by refl
| (t' :: ts) := by by_cases stored_weight t ≤ stored_weight t'; simp [insort, *]

def huffman {α : Type} : Πts : list (tree α), ts ≠ [] → tree α
| []             h := absurd (refl _) h
| [t]            _ := t
| (t :: u :: ts) _ :=
  have list.length (insort (unite t u) ts) < 1 + (1 + list.length ts) :=
    by simp [length_insort]; exact nat.lt_add_of_pos_left nat.zero_lt_one,
  huffman (insort (unite t u) ts) (insort_ne_nil _ _)
using_well_founded {rel_tac := λ_ _, `[exact ⟨_, measure_wf (list.length ∘ psigma.fst)⟩]}

#print has_well_founded

/- `measure_wf (list.length ∘ psigma.fst)⟩` tells us that the termination measure is the length of
the first argument `ts`. (The second argument is the proof of `ts ≠ []`.) -/

def ts1 : list (tree char) := [leaf 2 'z', leaf 3 'd', leaf 5 'f', leaf 7 's', leaf 11 'e']

#eval huffman ts1 (by simp [ts1])

def tree.repr {α : Type} [has_repr α] : tree α → string
| (leaf w a)    := "(leaf " ++ repr w ++ " " ++ repr a ++ ")"
| (inner w l r) := "(inner " ++ repr w ++ " " ++ tree.repr l ++ " " ++ tree.repr r ++ ")"

instance {α : Type} [has_repr α] : has_repr (tree α) :=
⟨tree.repr⟩

#eval huffman ts1 (by simp [ts1])

end huffman


/- First-order terms -/

namespace fo_terms

inductive term (α β : Type) : Type
| var {} (x : β) : term
| fn (f : α) (ts : list term) : term

export term (var fn)

inductive well_formed {α β : Type} (ary : α → ℕ) : term α β → Prop
| var (x : β) : well_formed (var x)
| fn (f : α) (ts : list (term α β)) (hargs : ∀t ∈ ts, well_formed t)
    (hlen : list.length ts = ary f) : well_formed (fn f ts)

inductive ground {α β : Type} : term α β → Prop
| fn (f : α) (ts : list (term α β)) (hargs : ∀t ∈ ts, ground t) : ground (fn f ts)

def wf_term (α β : Type) (ary : α → ℕ) : Type :=
{t : term α β // well_formed ary t}

def gr_term (α β : Type) : Type :=
{t : term α β // ground t}

def gr_wf_term (α β : Type) (ary : α → ℕ) : Type :=
{t : term α β // well_formed ary t ∧ ground t}

end fo_terms

/- This fails:

namespace wf_fo_terms

inductive term (α β : Type) (ary : α → ℕ) : Type
| var {} (x : β) : term
| fn (f : α) (ts : list term) (hlen : list.length ts = ary f) : term

export term (var fn)

end wf_fo_terms
-/
