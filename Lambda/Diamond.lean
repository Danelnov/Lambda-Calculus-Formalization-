
import Mathlib.Logic.Relation
import Mathlib.Tactic

open Relation
open ReflTransGen

def Diamond (R : α → α → Prop) := ∀ {A B C}, R A B → R A C → ∃ D, R B D ∧ R C D

section Confluence

variable {R : α → α → Prop}

lemma weak_confluence (diamond : Diamond R) :
    ∀ {A B C}, R A B → ReflTransGen R A C → ∃ D, ReflTransGen R B D ∧ ReflTransGen R C D := by
    intro A B C rab rtac
    induction rtac using head_induction_on generalizing B with
    | refl => exists B; constructor; rfl; exact single rab
    | head hr h ih =>
        obtain ⟨D', h₂, BD'⟩ := diamond hr rab
        obtain ⟨D, D'D, CD⟩ := ih h₂
        exists D; constructor
        exact head BD' D'D
        assumption

theorem confluence (diamond : Diamond R) : Diamond (ReflTransGen R) := by
    unfold Diamond; intro A B C AB AC
    induction AB using head_induction_on generalizing C with
    | refl => exists C
    | head hr h ih =>
        obtain ⟨D, hd₁, hd₂⟩ := weak_confluence diamond hr AC
        obtain ⟨D', BD', DD'⟩ := ih hd₁
        exists D'; constructor
        assumption
        trans; exact hd₂; assumption

theorem equiv_confluence
    (R' : α → α → Prop) (reqv : ∀ {a b}, R a b ↔ R' a b) (diamond : Diamond R) :
    Diamond R' := by unfold Diamond; simp [← reqv]; exact diamond

end Confluence
