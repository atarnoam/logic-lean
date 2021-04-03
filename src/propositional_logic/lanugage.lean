import order

def index := ℕ

inductive Formula : Type
| Var : index → Formula
| To  : Formula → Formula → Formula
| Not : Formula → Formula

namespace formula

def Var := Formula.Var

infix ` →ᶠ `:60 := Formula.To
prefix `¬ᶠ `:40 := Formula.Not

end formula

@[derive [has_mem Formula, has_singleton Formula, has_union, has_emptyc, has_subset]]
def Theory := set Formula
