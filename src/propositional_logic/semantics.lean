import propositional_logic.lanugage

open formula

namespace semantics

def valuation := var → Prop

def eval (v : valuation) : Formula → Prop :=
begin  
  intro φ,
  induction φ with n α β vα vβ α vα,
  exact v n,
  exact vα → vβ,
  exact ¬vα,
end

namespace valuation

variable (v : valuation)
variables (n : var) (φ ψ : Formula)

instance : has_coe_to_fun valuation :=
{ F := λ v, Formula → Prop,
  coe := λ v, eval v 
}

variable {v}

@[simp] lemma eval_var : eval v (Var n) = v n := rfl
@[simp] lemma eval_to : eval v (φ →ᶠ ψ) = ((eval v φ) → (eval v ψ)) := rfl
@[simp] lemma eval_not : eval v (¬ᶠ φ) = ¬ (eval v φ) := rfl

end valuation

def models (T : Theory) (v : valuation) : Prop :=
∀ ⦃φ : Formula⦄, φ ∈ T → eval v φ

infix ` ⊧ `:50 := models

def consequence (T : Theory) (φ : Formula) : Prop :=
∀ ⦃v : valuation⦄, T ⊧ v → eval v φ

infix ` ⊢ `:50 := consequence

def is_true (φ : Formula) : Prop := ∅ ⊢ φ

prefix ` ⊢ₜ `:40 := is_true

section basics

variables {S T : Theory}
variables {v : valuation} {φ ψ ξ : Formula}

lemma subset_models (h : S ⊆ T) (hT : T ⊧ v) : S ⊧ v := λ _ hφ, hT (h hφ)

lemma consequence_trans (h : S ⊆ T) (hS : S ⊢ φ) : T ⊢ φ :=
λ _ _, hS (subset_models h ‹_›)

lemma consequence_mem (h : φ ∈ T) : T ⊢ φ :=
λ _ hv, hv ‹_›

lemma consequence_self : {φ} ⊢ φ := consequence_mem (set.mem_singleton _)

lemma consequence_cut (h : ∀ ψ ∈ S, T ⊢ ψ) (hs : S ⊢ φ) : T ⊢ φ :=
λ _ hv, hs (λ _ hψ, h _ hψ hv)

lemma empty_models : ∅ ⊧ v :=
begin
  intros _ _,
  exfalso,
  exact set.not_mem_empty ‹_› ‹_›,
end

lemma is_true_def : ⊢ₜ φ ↔ ∅ ⊢ φ := iff.rfl

lemma is_true_iff : ⊢ₜ φ ↔ ∀ v : valuation, eval v φ :=
⟨λ h _, h empty_models, λ h v _, h v⟩

lemma consequence_to_of_consequence_union_singleton (h : T ∪ {φ} ⊢ ψ) : (T ⊢ φ →ᶠ ψ) :=
begin
  intros v hv,
  rw valuation.eval_to,
  intro vφ,
  apply h,
  intros α hα,
  rw set.mem_union at hα,
  cases hα,
  { exact hv hα },
  {
    rw set.mem_singleton_iff at hα,
    rwa hα,
  }
end

lemma consequence_union_singleton_of_consequence_to (h : T ⊢ φ →ᶠ ψ) : T ∪ {φ} ⊢ ψ :=
begin
  intros v hv,
  have hvto := h (subset_models (set.subset_union_left _ _) hv),
  rw valuation.eval_to at hvto,
  apply hvto,
  apply hv,
  right,
  exact set.mem_singleton φ,
end

theorem deduction : (T ⊢ φ →ᶠ ψ) ↔ T ∪ {φ} ⊢ ψ :=
⟨consequence_union_singleton_of_consequence_to, consequence_to_of_consequence_union_singleton⟩

lemma is_true_to_iff : ⊢ₜ φ →ᶠ ψ ↔ {φ} ⊢ ψ :=
begin
  rw [is_true_def, deduction, set.empty_union],
end

lemma refl_true : ⊢ₜ φ →ᶠ φ := is_true_to_iff.2 consequence_self

lemma P1_true : ⊢ₜ φ →ᶠ (ψ →ᶠ φ) := 
begin
  rw is_true_to_iff,
  rw deduction,
  apply consequence_mem,
  simp,
end

lemma P2_true : ⊢ₜ (φ →ᶠ (ψ →ᶠ ξ)) →ᶠ ((φ →ᶠ ψ) →ᶠ (φ →ᶠ ξ)) :=
begin
  rw is_true_to_iff,
  repeat {rw deduction},
  intros v h,
  have vφ   : eval v φ := h (by simp),
  have vφψ  : eval v (φ →ᶠ ψ) := h (by simp),
  have vφψξ : eval v (φ →ᶠ (ψ →ᶠ ξ)) := h (by simp),
  simp at *,
  cc
end

lemma P3_true : ⊢ₜ (¬ᶠφ →ᶠ ¬ᶠψ) →ᶠ (ψ →ᶠ φ) :=
begin
  rw is_true_to_iff,
  intros v h,
  have vφψ : eval v (¬ᶠ φ →ᶠ ¬ᶠ ψ) := h (by simp),
  simp at *,
  cc
end

lemma consequence_modus_ponens (hφψ : T ⊢ φ →ᶠ ψ) (hφ : T ⊢ φ) : T ⊢ ψ :=
begin
  intros v h,
  have eφ := hφ h,
  have eφψ := hφψ h,
  rw valuation.eval_to at eφψ,
  cc,
end

end basics

end semantics