/- Lecture 2.1: Functional Programming — Lists -/

/- Lists -/

namespace my_list

-- length of a list
def length {α : Type} : list α → ℕ
| []        := 0
| (x :: xs) := length xs + 1

#reduce length [2,3,1]

-- count elements in a list
def bcount {α : Type} (p : α → bool) : list α → ℕ
| []        := 0
| (x :: xs) :=
  match p x with
  | tt := bcount xs + 1
  | ff := bcount xs
  end

-- filter elements
def bfilter {α : Type} (p : α → bool) : list α → list α
| []        := []
| (x :: xs) :=
  match p x with
  | tt := x :: bfilter xs
  | ff := bfilter xs
  end

-- `n`th element (actually, `n + 1`st)
def nth {α : Type} : list α → ℕ → option α
| []        _       := none
| (x :: _)  0       := some x
| (_ :: xs) (n + 1) := nth xs n

lemma exists_nth {α : Type} :
  ∀(xs : list α) (n : ℕ), n < length xs → ∃a, nth xs n = some a
| []        _       h := false.elim (not_le_of_gt h (nat.zero_le _))
| (x :: _)  0       _ := ⟨x, rfl⟩
| (_ :: xs) (n + 1) h :=
  have n_lt : n < length xs := lt_of_add_lt_add_right h,
  have ih : ∃a, nth xs n = some a := exists_nth xs n n_lt,
  by simp [nth, ih]

lemma lt_length_of_nth_some {α : Type} (a : α) :
  ∀(xs : list α) (n : ℕ), nth xs n = some a → n < length xs
| []        _       h := by contradiction
| (_ :: xs) 0       _ :=
  show 0 < length xs + 1, from
    lt_add_of_le_of_pos (nat.zero_le _) zero_lt_one
| (_ :: xs) (n + 1) h :=
  have ih : nth xs n = some a,
    by simp [nth] at h; assumption,
  show n + 1 < length xs + 1, from
    add_lt_add_right (lt_length_of_nth_some _ _ ih) 1

-- tail of a list
def tail {α : Type} (xs : list α) : list α :=
match xs with
| []      := []
| _ :: xs := xs
end

-- head of a list
def head {α : Type} (xs : list α) : option α :=
match xs with
| []     := none
| x :: _ := some x
end

-- zip
def zip {α β : Type} : list α → list β → list (α × β)
| (x :: xs) (y :: ys) := (x, y) :: zip xs ys
| []        _         := []
| (_ :: _)  []        := []

lemma map_zip {α α' β β' : Type} (f : α → α') (g : β → β') :
  ∀xs ys, list.map (λp : α × β, (f p.1, g p.2)) (zip xs ys) =
    zip (list.map f xs) (list.map g ys)
| (x :: xs) (y :: ys) := begin simp [zip, list.map], exact (map_zip _ _) end
| []        _         := by refl
| (_ :: _)  []        := by refl

lemma min_add_add (l m n : ℕ) :
  min (l + m) (l + n) = l + min m n :=
have cancel : l + m ≤ l + n ↔ m ≤ n :=
begin
  rw add_comm l,
  rw add_comm l,
  rw nat.add_le_add_iff_le_right
end,
by by_cases m ≤ n; simp [min, *]

lemma length_zip {α β : Type} :
  ∀(xs : list α) (ys : list β), length (zip xs ys) = min (length xs) (length ys)
| (x :: xs) (y :: ys) := by simp [zip, length, length_zip xs ys, min_add_add]
| []        _         := by refl
| (_ :: _)  []        := by refl

end my_list


/- Type classes -/

namespace my_typeclass

class inhabited (α : Type) :=
(default_value : α)

instance : inhabited ℕ :=
⟨0⟩

instance prod_inhabited (α β) [inhabited α] [inhabited β] : inhabited (α × β) :=
⟨(inhabited.default_value α, inhabited.default_value β)⟩

#print instances inhabited

def nat_value : ℕ := inhabited.default_value ℕ

def pair_value : ℕ × ℕ := inhabited.default_value _

section
set_option pp.implicit true
#print nat_value
#print pair_value
end

-- `nth` for inhabited types
def inth {α : Type} [inhabited α] : list α → ℕ → α
| []        _       := inhabited.default_value α
| (x :: xs) 0       := x
| (x :: xs) (n + 1) := inth xs n

-- `head` for inhabited types
def ihead {α : Type} [inhabited α] (xs : list α) : α :=
match xs with
| []     := inhabited.default_value α
| x :: _ := x
end

lemma inth_eq_ihead {α : Type} [inhabited α] (xs : list α) :
  inth xs 0 = ihead xs :=
match xs with
| []     := by refl
| _ :: _ := by refl
end

end my_typeclass


/- Decidable -/

#print decidable
#print decidable_eq
#print decidable_pred

#check ite
#check if_pos
#check if_neg

#check dite
#check dif_pos
#check dif_neg

lemma if_distrib {α β : Type} (f : α → β) (t e : α) (c : Prop) [decidable c] :
  (if c then f t else f e) = f (if c then t else e) :=
by by_cases c; simp *

namespace my_list

def filter {α : Type} (p : α → Prop) [decidable_pred p] : list α → list α
| []        := []
| (x :: xs) := if p x then x :: filter xs else filter xs

#eval filter (λn : ℕ, 2 ≤ n ∧ n ≤ 10) [1, 2, 3, 4, 11, 15, 2]

section
set_option pp.implicit true
#check filter (λn : ℕ, 2 ≤ n ∧ n ≤ 10) [1, 2, 3, 4, 11, 15, 2]
end


/- **Optional**: Vectors as a dependent inductive type -/

inductive vec (α : Type) : ℕ → Type
| vnil {} : vec 0
| vcons (a : α) (n : ℕ) (v : vec n) : vec (n + 1)

export vec (vnil vcons)

#check vnil
#check vcons

def vec_to_list {α : Type} : ∀{n : ℕ}, vec α n → list α
| _ vnil          := []
| _ (vcons a n v) := a :: vec_to_list v

def list_to_vec {α : Type} : ∀(l : list α) (n : ℕ), list.length l = n → vec α n
| []        0       h := vec.vnil
| (x :: xs) (n + 1) h := vcons x n (list_to_vec xs n (nat.succ.inj h))

lemma length_vec_to_list {α : Type} :
  ∀{n : ℕ} (v : vec α n), list.length (vec_to_list v) = n
| _ vnil          := by refl
| _ (vcons a n v) := congr_arg nat.succ (length_vec_to_list v)

lemma list_to_vec_vec_to_list {α : Type} :
  ∀{n : ℕ} (v : vec α n), list_to_vec (vec_to_list v) _ (length_vec_to_list _) = v
| _ vnil          := by refl
| _ (vcons a n v) := by simp [vec_to_list, list_to_vec, list_to_vec_vec_to_list v]

lemma vec_to_list_list_to_vec {α : Type} :
  ∀(l : list α) (n : ℕ) (h : list.length l = n), vec_to_list (list_to_vec l n h) = l
| []        0       h := by refl
| (x :: xs) (n + 1) h := by simp [list_to_vec, vec_to_list, vec_to_list_list_to_vec xs]


/- **Optional**: Vectors as a dependent quotient type -/

def vec2 (α : Type) (n : ℕ) : Type := { l : list α // list.length l = n }

def vec_to_vec2 {α : Type} {n : ℕ} (v : vec α n) : vec2 α n :=
⟨vec_to_list v, length_vec_to_list v⟩

def vec2_to_vec {α : Type} : ∀{n : ℕ}, vec2 α n → vec α n
| n ⟨l, hn⟩ := list_to_vec l n hn

lemma vec_to_vec2_vec2_to_vec {α : Type} :
  ∀{n : ℕ} (v : vec2 α n), vec_to_vec2 (vec2_to_vec v) = v
| _ ⟨l, rfl⟩ :=
  begin
    simp [vec2_to_vec, vec_to_vec2],
    apply subtype.eq,
    apply vec_to_list_list_to_vec
  end

lemma vec2_to_vec_vec_to_vec2 {α : Type} {n : ℕ} (v : vec α n) :
  vec2_to_vec (vec_to_vec2 v) = v :=
by simp [vec_to_vec2, vec2_to_vec, list_to_vec_vec_to_list]

def list_to_vec' {α : Type} : ∀(l : list α), vec α (list.length l)
| []        := vnil
| (x :: xs) := vcons x _ (list_to_vec' xs)

def vec2_to_vec' {α : Type} : ∀{n : ℕ}, vec2 α n → vec α n
| n ⟨l, hn⟩ :=
  begin
    rw ← hn,
    exact list_to_vec' l
  end

end my_list
