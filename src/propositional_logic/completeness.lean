import propositional_logic.semantics
import propositional_logic.syntactics

open formula

section soundness

variables {T : Theory} {φ : Formula}

theorem soundness (h : syntactics.consequence T φ) : semantics.consequence T φ :=
begin
  induction h with ψ hψT ψ hψax α β hαS hαβS hαT hαβT,
  { exact semantics.consequence_mem ‹_› },
  { rcases hψax with ⟨α, β, h⟩,
    { rw h,
      exact semantics.consequence_P1 },
    { rcases hψax with ⟨α, β, γ, h⟩,
      rw h,
      exact semantics.consequence_P2 },
    { rcases hψax with ⟨α, β, h⟩,
      rw h,
      exact semantics.consequence_P3 } },
  { exact semantics.consequence_modus_ponens ‹_› ‹_› }
end

end soundness

section completeness

local infix ` ⊢ `:50 := syntactics.consequence

def model (T : Theory) : valuation :=
λ var, T ⊢ Var var

variables {T : Theory} {φ : Formula}

open syntactics


/- We are going to show that (syntactical) consistent and complete theories have a model. -/
lemma model_models_iff_consequence (hcons : consistent T) (hcom : complete T) : 
  T ⊢ φ ↔ eval (model T) φ :=
begin
  induction φ with v φ ψ hφ hψ φ hφ,
  { refl },
  { rw [semantics.eval_to, ← hφ, ← hψ],
    exact consistent_complete.consequence_to_iff_consequence_of hcons hcom },
  { rw semantics.eval_not,
    rw consistent_complete.consequence_not_iff_not_consequence ‹_› ‹_›,
    cc }
end

theorem model_models (hcons : consistent T) (hcom : complete T) :
  model T ⊧ T :=
begin
  intro φ,
  rw ← model_models_iff_consequence ‹_› ‹_›,
  exact consequence_mem,
end

theorem completeness : semantics.consequence T φ → T ⊢ φ :=
begin
  contrapose!,
  intro h,
  have hTnφ := consistent_union_of_consistent_not_consequence h,
  rcases hTnφ.exists_consistent_complete_extension with ⟨T', hs, hcons, hcom⟩,
  apply (mt (semantics.consequence_trans ((by simp) : T ⊆ T ∪ {¬ᶠ φ}))),
  apply (mt (semantics.consequence_trans hs)),
  apply semantics.not_consequence_of_models_union_not (_ : model T' ⊧ T' ∪ {¬ᶠ φ}),
  refine (semantics.subset_models _ (model_models ‹_› ‹_›)),
  apply set.union_subset (rfl.subset : T' ⊆ T'),
  rw set.union_subset_iff at hs,
  exact hs.2
end

end completeness

theorem semantics_iff_syntactics {T : Theory} {φ : Formula} : 
  semantics.consequence T φ ↔ syntactics.consequence T φ :=
⟨completeness, soundness⟩