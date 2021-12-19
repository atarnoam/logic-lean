import order
import data.finset
import data.pfun

open classical

noncomputable theory

@[derive [decidable_eq]]
def var := ℕ

inductive Formula : Type
| Var : var → Formula
| To  : Formula → Formula → Formula
| Not : Formula → Formula

instance : inhabited Formula :=
⟨Formula.Var (0 : ℕ)⟩

instance : has_mem var Formula :=
{mem := λ n φ, begin
  induction φ with m φ ψ φmem ψmem φ φmem,
  exact m = n,
  exact φmem ∨ ψmem,
  exact φmem,
end}

structure SubstitutionData := 
(fn : pfun var Formula)
(finite_dom : ∃ A : finset var, (A : set var) = fn.dom)


class has_substitution (α : Type*) :=
(substitute : α → SubstitutionData → α)

namespace formula

def Var := Formula.Var

infix ` →ᶠ `:60 := Formula.To
prefix `¬ᶠ `:70 := Formula.Not

/-instance : has_substitution Formula :=
⟨λ φ s,
begin
  induction φ with n,
  refine @dite _ (n ∈ s.dom) (dec _) (λ _, pfun.fn s n ‹_›) (λ _, Var n),
  exact Formula.To ‹_› ‹_›,
  exact Formula.Not ‹_›,
end⟩-/
--⟨λ φ s, Formula.rec s (λ _ _, Formula.To) (λ _, Formula.Not) φ⟩

end formula

@[derive [has_mem Formula, has_singleton Formula, has_union, has_emptyc, has_subset]]
def Theory := set Formula
