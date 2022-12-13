import fol.language

open language

universe u

structure Structure (S : signature) :=
(Dom : Type u)
(const : Const S → Dom)
(func : Func S → Dom → Dom)
(op : Op S → Dom → Dom → Dom)
(rel : Rel S → Dom → Dom → Prop)

variables {S : signature}

def assignment (A : Structure S) := var → A.Dom

def subs_assignment {S : signature} {A : Structure S} 
(β : assignment A) (a : A.Dom) (x : var) : assignment A :=
λ v, ite (v = x) a (β v)