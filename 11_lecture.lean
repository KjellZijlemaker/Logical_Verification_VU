/- Lecture 1.1: Basics — Specifications -/

/- Natural numbers -/

namespace my_nat

inductive nat
| zero : nat
| succ : nat → nat

#check nat
#check nat.zero
#check nat.succ

#print nat

def add : nat → nat → nat
| m nat.zero     := m
| m (nat.succ n) := nat.succ (add m n)

#reduce add (nat.succ nat.zero) (nat.succ nat.zero)

lemma add_comm (m n : nat) : add m n = add n m :=
_

lemma add_assoc (l m n : nat) : add (add l m) n = add l (add m n) :=
_

def mul : nat → nat → nat
| _ nat.zero     := nat.zero
| m (nat.succ n) := add m (mul m n)

#reduce mul (nat.succ (nat.succ nat.zero)) (nat.succ (nat.succ nat.zero))

lemma mul_comm (m n : nat) : mul m n = mul n m :=
_

lemma mul_assoc (l m n : nat) : mul (mul l m) n = mul l (mul m n) :=
_

lemma mul_add (l m n : nat) : mul l (add m n) = add (mul l m) (mul l n) :=
_

#print mul
#print mul._main

-- illegal
def evil : nat → nat
| n := nat.succ (evil n)

end my_nat

def power : ℕ → ℕ → ℕ
| _ 0            := 1
| m (nat.succ n) := m * power m n

#reduce power 2 5

def power' (m : ℕ) : ℕ → ℕ
| 0            := 1
| (nat.succ n) := m * power' n

#reduce power' 2 5

def iter (α : Type) (z : α) (f : α → α) : ℕ → α
| 0            := z
| (nat.succ n) := f (iter n)

#check iter

def power'' (m n : ℕ) :=
iter _ 1 (λl, m * l) n

#reduce power'' 2 5


/- Lists -/

namespace my_list

inductive list (α : Type)
| nil : list
| cons : α → list → list

#check list.nil
#check list.cons
#check @list.cons

def append (α : Type) : list α → list α → list α
| (list.nil _)     ys := ys
| (list.cons x xs) ys := list.cons x (append xs ys)

#check append
#reduce append _ (list.cons 1 (list.nil _)) (list.cons 2 (list.nil _))

def append' {α : Type} : list α → list α → list α
| (list.nil _)     ys := ys
| (list.cons x xs) ys := list.cons x (append' xs ys)

#check append'
#reduce append' (list.cons 1 (list.nil _)) (list.cons 2 (list.nil _))

end my_list

#print list

def reverse {α : Type} : list α → list α
| []        := []
| (x :: xs) := reverse xs ++ [x]

lemma reverse_reverse {α : Type} (xs : list α) : reverse (reverse xs) = xs :=
_


/- Some basic types -/

#print bool

#reduce ff || tt

#print prod
#print sum

#print empty

#check (ℕ → ℕ) → list ℕ → list ℕ
#check Πα β, (α → β) → list α → list β


/- RGB values -/

structure rgb :=
(red green blue : ℕ)

structure rgba extends rgb :=
(alpha : ℕ)

#print rgb
#print rgba

#reduce rgb.mk 0xff 0xcc 0xff
#reduce ({red := 0xff, green := 0xcc, blue := 0xff} : rgb)
#reduce ({red := 0xff, green := 0xcc, blue := 0xff, alpha := 0x7f} : rgba)

def red : rgb := {red := 0xff, green := 0x00, blue := 0x00}
def semitransparent_red : rgba := {alpha := 0x7f, ..red}
def green : rgb := ⟨0x00, 0xff, 0x00⟩

#print red
#print semitransparent_red
#print green

def shuffle (c : rgb) : rgb :=
{red := c.green, green := c.blue, blue := c.red}

lemma shuffle_shuffle_shuffle (c : rgb) : shuffle (shuffle (shuffle c)) = c :=
by cases c; refl
