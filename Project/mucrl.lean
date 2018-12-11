namespace test

inductive Set
|  true : Set
| false : Set

inductive types
|   onetype         : types
|   booltype        : types
|   nattype         : types
|   Dtype           : types
|   Frametype       : types
|   bool_Errtype    : types
|   Frame_Errtype   : types

def type := types → Set
def one (t: type) := t types.onetype
def bool (t: type) := t types.booltype
def nat (t: type) := t types.nattype
def D (t: type) := t types.Dtype
def Frame (t: type) := t types.Frametype
def bool_Err (t: type) := t types.bool_Errtype
def Frame_Err (t: type) := t types.Frame_Errtype

notation `i` := one 
notation `true` := bool
notation `false` := bool
notation `o` := nat
notation `S` := nat → nat

axiom t1 one (j: one) : j = i
axiom t2 bool : true = false
axiom t3 bool (b:bool) : b=true ∨ b=false
axiom nat_ind (P: nat → Prop) (n:nat)


end test
