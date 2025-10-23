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
    . intro h; cases h; first | rfl | assumption
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
    | var => rfl
    | abs => constructor; aesop
    | app => constructor <;> aesop
    | subst M₁ M₂ N₁ N₂ =>
        simp [beta]
        rw [shift_unshift_swap (Nat.zero_le i) (shifted_subst' 0 M₂ N₂)]
        simp
        rw [← shift_shift_swap _ (Nat.zero_le i), ← beta]
        apply BetaP.subst <;> aesop

lemma para_subst' {n} {M N N' : Lambda} : N →βp N' → M[n := N] →βp M[n := N'] := by
    intros
    induction M generalizing n N N' with
    | var => simp; split_ifs; assumption; rfl
    | app => simp; apply BetaP.app <;> aesop
    | abs M ih =>
        simp; apply ih; apply para_shift_conservation; assumption

lemma para_subst {n} {M N M' N' : Lambda} :
    M →βp M' → N →βp N' → M[n := N] →βp M'[n := N'] := by
    intro h₁ h₂
    induction h₁ generalizing n N N' with
    | var => simp; split_ifs <;> aesop
    | app => simp; apply BetaP.app <;> aesop
    | abs _ _ _ ih =>
        simp; apply ih; apply para_shift_conservation; assumption
    | subst M M' P P' hm hp ihm ihp =>
        conv =>
            rhs
            simp [beta, ← unshift_subst_swap' _ _ (shifted_subst' 0 M' P')]

        sorry
