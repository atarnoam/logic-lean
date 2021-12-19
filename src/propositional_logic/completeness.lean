import propositional_logic.semantics
import propositional_logic.syntactics

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
