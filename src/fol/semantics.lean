import fol.language

open language

universe u

structure Structure (S : Signature) :=
(dom : Type u)
(const : Const S → dom)
(func : Func S → dom → dom)
(op : Op S → dom → dom → dom)
(rel : Rel S → dom → dom → Prop)

instance {S : Signature} : has_coe_to_sort (Structure S) (Type u) := ⟨Structure.dom⟩

variables {S : Signature}

structure assignment (A : Structure S) :=
(ass : var → A)

section assignment

variable {A : Structure S}

def subs_assignment (β : assignment A) (a : A) (x : var) : assignment A :=
⟨λ v, ite (v = x) a (β.ass v)⟩ 

notation _[_ / _] := subs_assignment

def interp (β : assignment A) : Term S → A :=
λ t,
begin
  induction t with v c f t a o t₁ t₂ a₁ a₂,
  exact β.ass v,
  exact A.const c,
  exact A.func f a,
  exact A.op o a₁ a₂
end

instance : has_coe_to_fun (assignment A) (λ _, Term S → A) :=
⟨λ β, interp β⟩

def eval : ∀ (β : assignment A) (φ : Formula S), Prop
| β (Formula.Eq t₁ t₂) := β t₁ = β t₂ 
| β (Formula.RelF R t₁ t₂) := A.rel R (β t₁) (β t₂)
| β (Formula.Not φ) := ¬eval β φ
| β (Formula.OpL LogicalOp.To φ₁ φ₂) := (eval β φ₁) → (eval β φ₂)
| β (Formula.QuantifierL Quantifier.All v φ) := ∀ (a : A), eval (subs_assignment β a v) φ

end assignment

namespace semantics

variable {A : Structure S}

section interp

lemma interp_var {β : assignment A} {v : var} : β v = β.ass v := rfl

lemma interp_const {β : assignment A} {c : Const S} : β c = A.const c := rfl

lemma interp_func {β : assignment A} {f : Func S} {t : Term S} : 
interp β (f t) = A.func f (β t) := rfl

lemma interp_op {β : assignment A} {o : Op S} {t₁ t₂ : Term S} :
interp β (o t₁ t₂) = A.op o (β t₁) (β t₂) := rfl

end interp

section eval

lemma eval_eq {β : assignment A} {t₁ t₂ : Term S} 

end eval

end semantics