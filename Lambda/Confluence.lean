import Lambda.Defs
import Lambda.Properties
import Mathlib.Tactic.Ring

open Lambda

@[simp]
lemma var_reduction {k : Nat} {N : Lambda} : k →βp N ↔ N = k := by
    constructor
    . intro h; induction N <;> cases h; rfl
    . intro h; rw [h]

@[simp]
lemma abs_reduction {N N' : Lambda} : λ N →βp λ N' ↔ N →βp N' := by
    constructor
    . intro h; cases h <;> first | rfl | assumption
    . apply BetaP.abs

@[simp]
lemma app_beta {N₁ N₂ N' : Lambda} : (N₁.app N₂).beta N' = (N₁.beta N').app (N₂.beta N') := by
    conv => lhs; unfold beta; simp; rw [← beta, ← beta]

lemma betap_appl {N₁ N₂ N' : Lambda} : N₁ →βp N₂ → N₁.app N' →βp N₂.app N' := by
    intros; apply BetaP.app; assumption; rfl

lemma betap_appr {N₁ N₂ N' : Lambda} : N₁ →βp N₂ → N'.app N₁ →βp N'.app N₂ := by
    intros; apply BetaP.app; rfl; assumption

lemma para_shift_conservation {i j : Nat} {N N' : Lambda} : N →βp N' → (↑) i j N →βp (↑) i j N' := by
    intro h
    induction h generalizing i j with
    | refl => rfl
    | abs => constructor; aesop
    | app => constructor <;> aesop
    | subst M₁ M₂ N₁ N₂ =>
        simp_all [beta]
        rw [shift_unshift_swap (Nat.zero_le i) (shifted_subst' 0 M₂ N₂)]
        simp_all
        rw [← shift_shift_swap _ (Nat.zero_le i), ← beta]
        apply BetaP.subst <;> aesop
