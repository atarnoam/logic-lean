import propositional_logic.lanugage
import data.set
import data.finset
import data.finset.order
import order.zorn
open formula

open classical

namespace syntactics

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

section classical_axioms

variables {φ ψ ξ : Formula}

lemma p1_subset_classical_axioms : P1 ⊆ classical_axioms :=
set.subset.trans (set.subset_union_left _ P2) (set.subset_union_left _ P3)

lemma p2_subset_classical_axioms : P2 ⊆ classical_axioms :=
set.subset.trans (set.subset_union_right P1 _) (set.subset_union_left _ P3)

lemma p3_subset_classical_axioms : P3 ⊆ classical_axioms :=
set.subset_union_right _ P3

lemma mem_P1 : φ →ᶠ (ψ →ᶠ φ) ∈ P1 := ⟨φ, ψ, rfl⟩

lemma mem_P2 : (φ →ᶠ (ψ →ᶠ ξ)) →ᶠ ((φ →ᶠ ψ) →ᶠ (φ →ᶠ ξ)) ∈ P2 := ⟨φ, ψ, ξ, rfl⟩

lemma mem_P3 : (¬ᶠφ →ᶠ ¬ᶠψ) →ᶠ (ψ →ᶠ φ) ∈ P3 := ⟨φ, ψ, rfl⟩

end classical_axioms

def consequence : Theory → Formula → Prop :=
deduction_consequence classical_axioms

section basics

variables {T S : Theory} (φ ψ ξ : Formula)

infix ` ⊢ `:50 := consequence

lemma is_theory : φ ∈ T → consequence T φ := 
λ _, deduction_consequence.is_theory ‹_›

lemma is_axiom : φ ∈ classical_axioms → consequence T φ := 
λ _, deduction_consequence.is_axiom ‹_›

lemma is_modus_ponens : consequence T φ → consequence T (φ →ᶠ ψ) → consequence T ψ := 
λ _  _, deduction_consequence.is_modus_ponens ‹_› ‹_›

variables {φ ψ ξ}

lemma is_P1 : T ⊢ φ →ᶠ (ψ →ᶠ φ) := is_axiom _ (p1_subset_classical_axioms mem_P1)

lemma is_P2 : T ⊢ (φ →ᶠ (ψ →ᶠ ξ)) →ᶠ ((φ →ᶠ ψ) →ᶠ (φ →ᶠ ξ)) :=
is_axiom _ (p2_subset_classical_axioms mem_P2)

lemma is_P3 : T ⊢ (¬ᶠφ →ᶠ ¬ᶠψ) →ᶠ (ψ →ᶠ φ) :=
is_axiom _ (p3_subset_classical_axioms mem_P3)

lemma consequence_mem (h : φ ∈ T) : T ⊢ φ := deduction_consequence.is_theory ‹_›

lemma consequence_self : {φ} ⊢ φ := consequence_mem (set.mem_singleton _)

lemma consequence_cut (h : ∀ ψ ∈ S, T ⊢ ψ) (hS : S ⊢ φ) : T ⊢ φ :=
begin
  induction hS with ψ hψS ψ hψax α β hαS hαβS hαT hαβT, 
  { exact h ψ hψS },
  { exact is_axiom _ ‹_› },
  { exact is_modus_ponens _ _ ‹_› ‹_› }
end

lemma consequence_trans (h : S ⊆ T) (hS : S ⊢ φ) : T ⊢ φ :=
consequence_cut (λ ψ _, consequence_mem (h ‹_›)) hS

def is_true (φ : Formula) : Prop := ∅ ⊢ φ

prefix ` ⊢ₜ `:40 := is_true

lemma is_true_def : ⊢ₜ φ ↔ ∅ ⊢ φ := iff.rfl

lemma consequence_of_is_true : ⊢ₜ φ → T ⊢ φ := 
consequence_trans (set.empty_subset _)

end basics

section deduction_theorem

variables {T S : Theory} {φ ψ ξ : Formula}

lemma is_true_self_to_self : ⊢ₜ φ →ᶠ φ  :=
begin
  apply is_modus_ponens (φ →ᶠ (φ →ᶠ φ)) _ is_P1,
  exact is_modus_ponens (φ →ᶠ ((φ →ᶠ φ) →ᶠ φ)) _ is_P1 is_P2,
end

lemma consequence_self_to_self : T ⊢ φ →ᶠ φ := 
consequence_of_is_true is_true_self_to_self

lemma consequence_to_of_consequence (h : T ⊢ φ) : T ⊢ ψ →ᶠ φ :=
is_modus_ponens φ _ ‹_› is_P1

lemma consequence_union_singleton_of_consequence_to (h : T ⊢ φ →ᶠ ψ) : T ∪ {φ} ⊢ ψ :=
begin
  apply is_modus_ponens φ _,
  { apply is_theory, simp },
  { refine consequence_trans _ h,
    simp }
end

lemma consequence_to_of_consequence_union_singleton (h : T ∪ {φ} ⊢ ψ) : (T ⊢ φ →ᶠ ψ) :=
begin
  induction h with ξ hξTφ ξ hξax α β hαTφ hαβTφ hαT hαβT,
  { rw set.mem_union at hξTφ,
    cases hξTφ,
    { exact consequence_to_of_consequence (is_theory _ ‹_›) },
    { rw set.mem_singleton_iff at hξTφ,
      rw hξTφ,
      exact consequence_self_to_self } },
  { exact consequence_to_of_consequence (is_axiom _ ‹_›) },
  { apply is_modus_ponens _ _ hαT,
    apply is_modus_ponens _ _ hαβT,
    exact is_P2 }
end

theorem deduction : (T ⊢ φ →ᶠ ψ) ↔ T ∪ {φ} ⊢ ψ :=
⟨consequence_union_singleton_of_consequence_to, consequence_to_of_consequence_union_singleton⟩

lemma is_true_deduction : ⊢ₜ φ →ᶠ ψ ↔ {φ} ⊢ ψ :=
by rw [is_true_def, deduction, set.empty_union]

end deduction_theorem

section compactness

variables {T : Theory} {φ ψ : Formula}

theorem exists_finset_consequence_of_consequence (h : T ⊢ φ) : 
  ∃ (S : finset Formula), ((S : set Formula) ⊆ T) ∧ (S : set Formula) ⊢ φ :=
begin
  induction h with ψ hψT ψ hψax α β hαT hαβT hαT hαβT,
  { refine ⟨{ψ}, finset.singleton_subset_set_iff.mpr hψT, _⟩,
    simp [consequence_self] },
  { use ∅,
    simp [is_axiom _ ‹_›] },
  { rcases hαT with ⟨A, hAT, hAα⟩,
    rcases hαβT with ⟨B, hBT, hBαβ⟩,
    use A ∪ B,
    split,
    { simp [hAT, hBT] },
    { refine is_modus_ponens α _ (consequence_trans (by simp) hAα) 
    (consequence_trans (by simp) hBαβ) } }
end

end compactness

section negation

variables {T S : Theory} {φ ψ : Formula}

def false : Formula := ¬ᶠ (Formula.Var 0 →ᶠ Formula.Var 0)

lemma consequence_of_consequence_consequence_not (h : T ⊢ φ) (hn : T ⊢ ¬ᶠ φ) : T ⊢ ψ :=
begin
  apply is_modus_ponens φ _ ‹_›,
  exact is_modus_ponens (¬ᶠ ψ →ᶠ ¬ᶠ φ) _ (consequence_to_of_consequence ‹_›) is_P3,
end

lemma consequence_of_consequence_false (h : T ⊢ false) : T ⊢ φ :=
begin
  apply is_modus_ponens (Formula.Var 0 →ᶠ Formula.Var 0) _ consequence_self_to_self,
  refine is_modus_ponens (¬ᶠ φ →ᶠ ¬ᶠ (Formula.Var 0 →ᶠ Formula.Var 0)) _ _ is_P3,
  exact consequence_to_of_consequence h
end

lemma is_true_not_to_self_to_self : ⊢ₜ (¬ᶠ φ →ᶠ φ) →ᶠ φ :=
begin
  rw is_true_deduction,
  apply is_modus_ponens (¬ᶠ φ →ᶠ φ) _ consequence_self,
  refine is_modus_ponens (¬ᶠ φ →ᶠ ¬ᶠ (¬ᶠ φ →ᶠ φ)) _ _ is_P3,
  rw deduction,
  have h : ¬ᶠ φ ∈ {¬ᶠ φ →ᶠ φ} ∪ {¬ᶠ φ} := (set.mem_union_right _ (set.mem_singleton _)),
  refine consequence_of_consequence_consequence_not _ (consequence_mem ‹_›),
  rw ← deduction,
  exact consequence_self
end

lemma consequence_not_to_self_to_self : T ⊢ (¬ᶠ φ →ᶠ φ) →ᶠ φ :=
consequence_of_is_true is_true_not_to_self_to_self

lemma is_true_not_not_to : ⊢ₜ ¬ᶠ ¬ᶠ φ →ᶠ φ :=
begin
  rw is_true_deduction,
  refine is_modus_ponens (¬ᶠ φ →ᶠ φ) _ _ consequence_not_to_self_to_self,
  rw deduction,
  exact consequence_of_consequence_consequence_not 
  (consequence_mem (set.mem_union_right _ (set.mem_singleton _))) 
  (consequence_mem (set.mem_union_left _ (set.mem_singleton _)))
end

lemma consequence_not_not_to : T ⊢ ¬ᶠ ¬ᶠ φ →ᶠ φ  :=
consequence_of_is_true is_true_not_not_to

lemma is_true_to_not_not : ⊢ₜ φ →ᶠ ¬ᶠ ¬ᶠ φ :=
is_modus_ponens _ _ consequence_not_not_to is_P3

lemma consequence_to_not_not : T ⊢ φ →ᶠ ¬ᶠ ¬ᶠ φ  :=
consequence_of_is_true is_true_to_not_not

lemma is_true_modus_tollens : ⊢ₜ (φ →ᶠ ψ) →ᶠ (¬ᶠ ψ →ᶠ ¬ᶠ φ) :=
begin
  rw is_true_deduction,
  apply is_modus_ponens _ _ _ is_P3,
  rw deduction,
  refine is_modus_ponens _ _ _ consequence_to_not_not,
  refine is_modus_ponens _ _ _ (consequence_mem (set.mem_union_left _ (set.mem_singleton _))),
  rw ← deduction,
  exact consequence_not_not_to
end

lemma consequence_modus_tollens : T ⊢ (φ →ᶠ ψ) →ᶠ (¬ᶠ ψ →ᶠ ¬ᶠ φ) :=
consequence_of_is_true is_true_modus_tollens

lemma consequence_of_to_not_to (h : T ⊢ φ →ᶠ ψ) (hn : T ⊢ (¬ᶠ φ) →ᶠ ψ) : T ⊢ ψ :=
begin
  refine is_modus_ponens (¬ᶠ ψ →ᶠ ψ) _ _ (consequence_not_to_self_to_self),
  rw deduction,
  have H := is_modus_ponens _ _ h consequence_modus_tollens,
  refine is_modus_ponens _ _ _ (consequence_trans (set.subset_union_left _ _) hn),
  refine is_modus_ponens _ _ _ (consequence_trans (set.subset_union_left _ _) H),
  exact consequence_mem (set.mem_union_right _ (set.mem_singleton _))
end

lemma consequence_not_to_to_to_not : T ⊢ ¬ᶠ (φ →ᶠ ψ) →ᶠ (φ →ᶠ ¬ᶠ ψ) :=
begin
  rw [deduction, deduction],
  refine consequence_of_to_not_to _ consequence_self_to_self,
  rw deduction,
  refine consequence_of_consequence_consequence_not (_ : _ ⊢ φ →ᶠ ψ) _,
  { exact is_modus_ponens _ _ (consequence_mem (by simp)) is_P1 },
  { exact consequence_mem (by simp) }
end

lemma consequence_not_to_to : T ⊢ ¬ᶠ φ →ᶠ (φ →ᶠ ψ) :=
begin
  rw [deduction, deduction],
  refine consequence_of_consequence_consequence_not (_ : _ ⊢ φ) _;
  exact consequence_mem (by simp)
end

end negation

def consistent (T : Theory) : Prop := 
∀ φ : Formula, ¬ (T ⊢ φ) ∨ ¬ (T ⊢ ¬ᶠ φ)

lemma consistent_iff (T : Theory) : consistent T ↔ ∀ (φ : Formula), ¬ (T ⊢ φ) ∨ ¬ (T ⊢ ¬ᶠ φ) :=
iff.rfl

def complete (T : Theory) : Prop :=
∀ φ : Formula, T ⊢ φ ∨ T ⊢ ¬ᶠ φ  

section consistency

variables {T S : Theory} {φ ψ : Formula}

lemma consistent.trans (hT : consistent T) (h : S ⊆ T) : consistent S :=
begin
  intro φ,
  cases hT φ with hφ hnφ,
  exact or.inl (λ h', hφ $ consequence_trans ‹_› h'),
  exact or.inr (λ h', hnφ $ consequence_trans ‹_› h'),
end

lemma consistent_of_not_consequence : ¬ (T ⊢ φ) → consistent T :=
begin
  rw consistent_iff,
  contrapose!,
  rintros ⟨ψ, h⟩,
  exact consequence_of_consequence_consequence_not h.1 h.2,
end

lemma consistent.exists_not_consequence (h : consistent T) : ∃ φ : Formula, ¬ (T ⊢ φ) :=
begin
  cases (h (Formula.Var 0)) with hφ hnφ,
  { exact ⟨(Formula.Var 0), ‹_›⟩ },
  { exact ⟨¬ᶠ (Formula.Var 0), ‹_›⟩ }
end 

lemma consistent_iff_exists_not_consequence : consistent T ↔ ∃ φ : Formula, ¬ (T ⊢ φ) :=
⟨consistent.exists_not_consequence, 
λ h, begin
  rcases h with ⟨φ, h⟩, 
  exact consistent_of_not_consequence h
end⟩

lemma inconsistent_iff_all_consequence : ¬ consistent T ↔ ∀ φ : Formula, T ⊢ φ :=
by simp only [iff_self, syntactics.consistent_iff_exists_not_consequence, not_exists_not]

lemma inconsistent_of_consequence_false (h : T ⊢ false) : ¬ consistent T :=
begin
  rw inconsistent_iff_all_consequence,
  exact λ _, consequence_of_consequence_false h
end

lemma inconsistent_iff_consequence_false : ¬ consistent T ↔ T ⊢ false :=
⟨λ h, inconsistent_iff_all_consequence.1 h false, inconsistent_of_consequence_false⟩

lemma finset_inconsistent_of_inconsistent (h : ¬ consistent T) : 
  ∃ (S : finset Formula), ((S : set Formula) ⊆ T) ∧ ¬ (consistent (S : set Formula)) :=
begin
  rw inconsistent_iff_consequence_false at h,
  rcases exists_finset_consequence_of_consequence h with ⟨S, hST, hSfalse⟩,
  use [S, hST],
  rwa inconsistent_iff_consequence_false,
end

lemma consistent_of_all_finset_consistent 
  (h : ∀ (S : finset Formula), ((S : set Formula) ⊆ T) → (consistent (S : set Formula))) :
  consistent T :=
by { revert h, contrapose!, exact finset_inconsistent_of_inconsistent }

lemma consistent_iff_all_finset_consistent :
  consistent T ↔ ∀ (S : finset Formula), ((S : set Formula) ⊆ T) → (consistent (S : set Formula)) :=
⟨λ _ _ _, consistent.trans ‹_› ‹_›, consistent_of_all_finset_consistent⟩

lemma consistent_union_of_consistent_not_consequence (hφ : ¬ T ⊢ φ) : consistent (T ∪ {¬ᶠ φ}) :=
begin
    rw consistent_iff_exists_not_consequence,
    use φ,
    revert hφ,
    contrapose!,
    rw ← deduction,
    intro h,
    exact is_modus_ponens _ _ h consequence_not_to_self_to_self,
end

lemma inconsistent_union_not_of_consequence (hφ : T ⊢ φ) : ¬ consistent (T ∪ {¬ᶠ φ}) :=
begin
  rw inconsistent_iff_consequence_false,
  rw ← deduction,
  apply is_modus_ponens _ _ _ is_P3,
  have h : T ⊢ ¬ᶠ ¬ᶠ φ := is_modus_ponens _ _ hφ consequence_to_not_not,
  exact is_modus_ponens _ _ h is_P1,
end

end consistency

section consistent_complete

variables {T : Theory} {φ ψ : Formula}

lemma consistent_complete.consequence_not_iff_not_consequence (hcons : consistent T) (hcom : complete T) : 
  T ⊢ ¬ᶠ φ ↔ ¬ T ⊢ φ :=
⟨by { have := hcons φ, cc }, by { have := hcom φ, cc }⟩

lemma consistent_complete.consequence_to_of_consequence_of (hcons : consistent T) (hcom : complete T) (h : (T ⊢ φ) → (T ⊢ ψ)) : T ⊢ φ →ᶠ ψ  :=
begin
  by_contra hn,
  have Hn := (consistent_complete.consequence_not_iff_not_consequence ‹_› ‹_›).2 hn,
  have hn' := λ H, is_modus_ponens _ _ H (is_modus_ponens _ _ Hn consequence_not_to_to_to_not),
  rw consistent_complete.consequence_not_iff_not_consequence ‹_› ‹_› at hn',
  by_cases hφ : T ⊢ φ,
  { cc },
  { rw ← consistent_complete.consequence_not_iff_not_consequence ‹_› ‹_› at hφ,
    have H : T ⊢ φ →ᶠ ψ := is_modus_ponens _ _ hφ consequence_not_to_to,
    cc }  
end 

lemma consistent_complete.consequence_to_iff_consequence_of (hcons : consistent T) (hcom : complete T) : 
  T ⊢ φ →ᶠ ψ ↔ (T ⊢ φ → T ⊢ ψ) :=
⟨λ x y, is_modus_ponens _ _ y x, consistent_complete.consequence_to_of_consequence_of ‹_› ‹_›⟩

end consistent_complete

section consistent_extension

variables {T : Theory}

open zorn

private lemma chain_union_consistent_consistent (c : set Theory) (hcons : c ⊆ consistent) (hc : chain (⊆) c) (hcne : c.nonempty) : 
  consistent (⋃ (s ∈ c), s) :=
begin
  rw consistent_iff_all_finset_consistent,
  intros S hS,
  cases hcne with a ha,
  rcases finset.exists_mem_subset_of_subset_bUnion_of_directed_on ha (chain.directed_on hc) hS 
    with ⟨R, hRc, hSR⟩,
  refine consistent.trans _ hSR,
  exact set.mem_of_subset_of_mem hcons hRc,
end

lemma consistent.exists_maximal_consistent_extension (h : consistent T): 
  ∃ (T' : Theory) (hT' : consistent T'), T ⊆ T' ∧ ∀ (S : Theory) (hS : consistent S), T' ⊆ S → S = T' :=
zorn_subset_nonempty consistent (λ c hcons hc hcne, 
  ⟨⋃ (s ∈ c), s, chain_union_consistent_consistent c ‹_› ‹_› ‹_›, 
    λ s, set.subset_bUnion_of_mem⟩) _ ‹_›

theorem consistent.exists_consistent_complete_extension (h : consistent T):
  ∃ (T' : Theory), T ⊆ T' ∧ consistent T' ∧ complete T' :=
begin
  rcases h.exists_maximal_consistent_extension with ⟨T', hT', hTT', h⟩,
  refine ⟨T', hTT', hT', λ φ, _⟩,
  rw or_iff_not_imp_left,
  intro hφ,
  rw ← h _ (consistent_union_of_consistent_not_consequence hφ) (set.subset_union_left _ _),
  exact consequence_mem (set.mem_union_right _ (set.mem_singleton _))
end

end consistent_extension

end syntactics
