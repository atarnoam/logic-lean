import propositional_logic.lanugage
import data.set
open formula

@[derive [has_mem Formula, has_union, has_subset]]
def Axioms := set Formula

inductive deduction_consequence (ax : Axioms) (T : Theory) : Formula → Prop
| is_theory : ∀ {φ : Formula}, φ ∈ T → deduction_consequence φ
| is_axiom : ∀ {φ : Formula}, φ ∈ ax → deduction_consequence φ
| is_modus_ponens : ∀ {φ ψ : Formula}, deduction_consequence φ → deduction_consequence (φ →ᶠ ψ) → deduction_consequence ψ

def P1 : Axioms :=
{ ζ : Formula | ∃ φ ψ   : Formula, ζ = φ →ᶠ (ψ →ᶠ φ)}
def P2 : Axioms :=
{ ζ : Formula | ∃ φ ψ ξ : Formula, ζ = (φ →ᶠ (ψ →ᶠ ξ)) →ᶠ ((φ →ᶠ ψ) →ᶠ (φ →ᶠ ξ))}
def P3 : Axioms :=
{ ζ : Formula | ∃ φ ψ   : Formula, ζ = (¬ᶠφ →ᶠ ¬ᶠψ) →ᶠ (ψ →ᶠ φ) }

def classical_axioms : Axioms := 
P1 ∪ P2 ∪ P3

namespace classical_axioms

variables {φ ψ ξ : Formula}

lemma p1_subset_classical_axioms : P1 ⊆ classical_axioms :=
set.subset.trans (set.subset_union_left _ P2) (set.subset_union_left _ P3)

lemma p2_subset_classical_axioms : P2 ⊆ classical_axioms :=
set.subset.trans (set.subset_union_right P1 _) (set.subset_union_left _ P3)

lemma p3_subset_classical_axioms : P3 ⊆ classical_axioms :=
set.subset_union_right _ P3

lemma in_P1 : φ →ᶠ (ψ →ᶠ φ) ∈ P1 := ⟨φ, ψ, rfl⟩

lemma in_P2 : (φ →ᶠ (ψ →ᶠ ξ)) →ᶠ ((φ →ᶠ ψ) →ᶠ (φ →ᶠ ξ)) ∈ P2 := ⟨φ, ψ, ξ, rfl⟩

lemma in_P3 : (¬ᶠφ →ᶠ ¬ᶠψ) →ᶠ (ψ →ᶠ φ) ∈ P3 := ⟨φ, ψ, rfl⟩

end classical_axioms

def consequence : Theory → Formula → Prop :=
deduction_consequence classical_axioms

namespace syntactics

open classical_axioms

variables {T S : Theory} (φ ψ ξ : Formula)

infix ` ⊢ `:50 := consequence

lemma is_theory : φ ∈ T → consequence T φ := 
λ _, deduction_consequence.is_theory ‹_›

lemma is_axiom : φ ∈ classical_axioms → consequence T φ := 
λ _, deduction_consequence.is_axiom ‹_›

lemma is_modes_ponens : consequence T φ → consequence T (φ →ᶠ ψ) → consequence T ψ := 
λ _  _, deduction_consequence.is_modus_ponens ‹_› ‹_›

lemma is_P1 : T ⊢ φ →ᶠ (ψ →ᶠ φ) := is_axiom _ (p1_subset_classical_axioms in_P1)

lemma is_P2 : T ⊢ (φ →ᶠ (ψ →ᶠ ξ)) →ᶠ ((φ →ᶠ ψ) →ᶠ (φ →ᶠ ξ)) :=
is_axiom _ (p2_subset_classical_axioms in_P2)

lemma is_P3 : T ⊢ (¬ᶠφ →ᶠ ¬ᶠψ) →ᶠ (ψ →ᶠ φ) :=
is_axiom _ (p3_subset_classical_axioms in_P3)

variables {φ ψ ξ}

lemma consequence_mem (h : φ ∈ T) : T ⊢ φ := deduction_consequence.is_theory ‹_›

lemma consequence_self : {φ} ⊢ φ := consequence_mem (set.mem_singleton _)

lemma consequence_cut (h : ∀ ψ ∈ S, T ⊢ ψ) (hS : S ⊢ φ) : T ⊢ φ :=
begin
  induction hS with ψ hψS ψ hψax α β hαS hαβS hαT hαβT, 
  { exact h ψ hψS },
  { exact is_axiom _ ‹_› },
  { exact is_modes_ponens _ _ ‹_› ‹_› }
end

lemma consequence_trans (h : S ⊆ T) (hS : S ⊢ φ) : T ⊢ φ :=
consequence_cut (λ ψ _, consequence_mem (h ‹_›)) hS

def is_true (φ : Formula) : Prop := ∅ ⊢ φ

prefix ` ⊢ₜ `:40 := is_true

lemma is_true_def : ⊢ₜ φ ↔ ∅ ⊢ φ := iff.rfl

lemma consequence_of_is_true : ⊢ₜ φ → T ⊢ φ := 
consequence_trans (set.empty_subset _)


section deduction_theorem

lemma is_true_self_to_self : ⊢ₜ φ →ᶠ φ  :=
begin
  apply is_modes_ponens (φ →ᶠ (φ →ᶠ φ)) _ (is_P1 _ _),
  exact is_modes_ponens (φ →ᶠ ((φ →ᶠ φ) →ᶠ φ)) _ (is_P1 _ _) (is_P2 _ _ _),
end

lemma consequence_self_to_self : T ⊢ φ →ᶠ φ := 
consequence_of_is_true is_true_self_to_self

lemma consequence_union_singleton_of_consequence_to (h : T ⊢ φ →ᶠ ψ) : T ∪ {φ} ⊢ ψ :=
begin
  apply is_modes_ponens φ _,
  {
    apply is_theory,
    simp,
  },
  {
    refine consequence_trans _ h,
    simp,
  }
end

lemma consequence_to_of_consequence_union_singleton (h : T ∪ {φ} ⊢ ψ) : (T ⊢ φ →ᶠ ψ) :=
begin
  induction h with ξ hξTφ ξ hξax α β hαTφ hαβTφ hαT hαβT,
  {
    rw set.mem_union at hξTφ,
    cases hξTφ,
    {
      exact is_modes_ponens _ _ (is_theory _ ‹_›) (is_P1 _ _)
    },
    {
      rw set.mem_singleton_iff at hξTφ,
      rw hξTφ,
      exact consequence_self_to_self,
    }
  },
  {
    exact is_modes_ponens _ _ (is_axiom _ ‹_›) (is_P1 _ _)
  },
  {
    apply is_modes_ponens _ _ hαT,
    apply is_modes_ponens _ _ hαβT,
    exact is_P2 _ _ _,
  }
end

theorem deduction : (T ⊢ φ →ᶠ ψ) ↔ T ∪ {φ} ⊢ ψ :=
⟨consequence_union_singleton_of_consequence_to, consequence_to_of_consequence_union_singleton⟩

end deduction_theorem


end syntactics
