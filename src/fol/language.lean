import order
import data.finset
import data.pfun
import data.set.finite
import data.list.alist
import data.vector

open classical
open alist

noncomputable theory

-- Sadly, lean does not support good inductive types.
-- Hence we won't have arbitrary arity functions and relations.
structure Signature : Type :=
(consts : ℕ)
(funcs : ℕ)
(ops : ℕ)
(rels : ℕ)

@[derive [decidable_eq]]
structure Const (S : Signature) : Type :=
(const : ℕ)
(const_le : const < S.consts)

@[derive [decidable_eq]]
structure Func (S : Signature) : Type := 
(func : ℕ)
(func_le : func < S.funcs)

@[derive [decidable_eq]]
structure Op (S : Signature) : Type := 
(op : ℕ)
(op_le : op < S.ops)

@[derive [decidable_eq]]
structure Rel (S : Signature) : Type := 
(rel : ℕ)
(rel_le : rel < S.rels)

@[derive [decidable_eq, has_zero, has_one]]
def var := ℕ

@[derive [decidable_eq]]
inductive Term (S : Signature) : Type
| Var : var → Term
| ConstT : Const S → Term
| FuncT : Func S → Term → Term   
| OpT : Op S → Term → Term → Term

instance var_has_coe {S : Signature} : has_coe var (Term S) :=
⟨λ v, Term.Var v⟩

instance const_has_coe {S : Signature} : has_coe (Const S) (Term S) :=
⟨λ c, Term.ConstT c⟩

instance func_has_coe {S : Signature} : has_coe_to_fun (Func S) (λ _, Term S → Term S) :=
⟨λ f, Term.FuncT f⟩

instance op_has_coe {S : Signature} : has_coe_to_fun (Op S) (λ _, Term S → Term S → Term S) :=
⟨λ o, Term.OpT o⟩

instance {S : Signature} : inhabited (Term S) :=
⟨Term.Var 0⟩

def vars (S : Signature) : Term S → set var := 
λ t, begin
  induction t with v c f t st o t₁ t₂ st₁ st₂,
  exact {v},
  exact ∅,
  exact st,
  exact st₁ ∪ st₂,
end

@[derive decidable_eq]
inductive LogicalOp : Type
| To : LogicalOp

@[derive decidable_eq]
inductive Quantifier : Type
| All : Quantifier

@[derive [decidable_eq]]
inductive Formula (S : Signature) : Type
| Eq : Term S → Term S → Formula
| RelF : Rel S → Term S → Term S → Formula
| Not : Formula → Formula
| OpL  : LogicalOp → Formula → Formula → Formula
| QuantifierL : Quantifier → var → Formula → Formula 

instance {S : Signature} : inhabited (Formula S) :=
⟨Formula.Eq (Term.Var 0) (Term.Var 0)⟩

def free (S : Signature) : Formula S → set var :=
λ φ, 
begin
  induction φ with t₁ t₂ r t₁ t₂ φ sφ o φ₁ φ₂ sφ₁ sφ₂ q v φ sφ,
  exact vars S t₁ ∪ vars S t₂,
  exact vars S t₁ ∪ vars S t₂,
  exact sφ,
  exact sφ₁ ∪ sφ₂,
  exact sφ \ {v},
end

def sentence {S : Signature} (φ : Formula S) : Prop := free S φ = ∅ 

namespace language

variable {S : Signature}

section term

end term

section vars

lemma vars_var {v : var} : vars S (Term.Var v) = {v} := rfl

lemma vars_const {c : Const S} : vars S (Term.ConstT c) = ∅ := rfl

lemma vars_func {f : Func S} {t : Term S} : vars S (Term.FuncT f t) = vars S t := rfl

lemma vars_op {o : Op S} {t₁ t₂ : Term S} : 
vars S (Term.OpT o t₁ t₂) = vars S t₁ ∪ vars S t₂ := rfl

end vars

section formula

end formula

section free

lemma free_eq {t₁ t₂ : Term S} : 
free S (Formula.Eq t₁ t₂) = vars S t₁ ∪ vars S t₂ := rfl 

lemma free_rel {r : Rel S} {t₁ t₂ : Term S} : 
free S (Formula.RelF r t₁ t₂) = vars S t₁ ∪ vars S t₂ := rfl 

lemma free_not {φ : Formula S} : 
free S (Formula.Not φ) = free S φ := rfl

lemma free_opl {o : LogicalOp} {φ₁ φ₂ : Formula S} :
free S (Formula.OpL o φ₁ φ₂) = free S φ₁ ∪ free S φ₂ := rfl

lemma free_quantifier {q : Quantifier} {v : var} {φ : Formula S} :
free S (Formula.QuantifierL q v φ) = free S φ \ {v} := rfl

end free

end language

-- @[derive [has_mem, has_singleton Formula, has_union, has_emptyc, has_subset, complete_lattice]]
def Theory (S : Signature) := set (Formula S)
