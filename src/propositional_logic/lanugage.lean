import order
import data.finset
import data.pfun
import data.set.finite

open classical

noncomputable theory

@[derive [decidable_eq, has_zero]]
def var := ℕ

@[derive [decidable_eq]]
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
(finite_dom : set.finite fn.dom)


class has_substitution (α : Type*) :=
(substitute : α → SubstitutionData → α)

namespace formula

def Var := Formula.Var

infix ` →ᶠ `:60 := Formula.To
prefix `¬ᶠ `:70 := Formula.Not

instance : has_substitution Formula :=
⟨λ φ s,
begin
  induction φ with n,
  {
    refine pfun.eval_opt s.fn _,
  },
  exact Formula.To ‹_› ‹_›,
  exact Formula.Not ‹_›,
end⟩
--⟨λ φ s, Formula.rec s (λ _ _, Formula.To) (λ _, Formula.Not) φ⟩

end formula

@[derive [has_mem Formula, has_singleton Formula, has_union, has_emptyc, has_subset, complete_lattice]]
def Theory := set Formula
