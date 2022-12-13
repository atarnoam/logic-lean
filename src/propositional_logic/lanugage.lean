import order
import data.finset
import data.pfun
import data.set.finite
import data.list.alist

open classical
open alist

noncomputable theory

@[derive [decidable_eq, has_zero, has_one]]
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

def SubstitutionData := alist (λ v : var, Formula)

namespace formula

def Var := Formula.Var

infix ` →ᶠ `:60 := Formula.To
prefix `¬ᶠ `:70 := Formula.Not

def substitute : Formula → SubstitutionData → Formula :=
λ φ s,
begin
  induction φ with v,
  {
    cases s.lookup v with ψ,
    exact Var v,
    exact ψ,
  },
  exact Formula.To ‹_› ‹_›,
  exact Formula.Not ‹_›,
end

end formula

@[derive [has_mem Formula, has_singleton Formula, has_union, has_emptyc, has_subset, complete_lattice]]
def Theory := set Formula
