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
lemma app_beta (N₁ N₂ N' : Lambda) : (N₁.app N₂).beta N' = (N₁.beta N').app (N₂.beta N') := by
    conv => lhs; unfold beta; simp; rw [← beta, ← beta]

lemma shift_beta {i j : Nat} {N N' : Lambda} :
    ((↑) (i + 1) j N).beta ((↑) i j N') = (↑) i j (N.beta N') := by
    induction N generalizing i j with
    | var k =>
        sorry
    | app N₁ N₂ ih1 ih2 =>
        simp; constructor <;> first | apply ih1 | apply ih2
    | abs N ih =>
        simp
        sorry

lemma subst_shift (i j : Nat) (N N' : Lambda) : N →βp N' → (↑) i j N →βp (↑) i j N' := by
    intro NreN'
    induction NreN' generalizing i j with
    | refl => rfl
    | abs _ _ _ ih =>
        simp; apply ih
    | app _ _ _ _ _ _ ih1 ih2 =>
        simp; apply BetaP.app <;> (first | apply ih1 | apply ih2)
    | subst M₁ M₂ N₁ N₂ Mre Nre ih1 ih2 =>
        simp
        conv => rhs; apply Eq.symm shift_beta
        apply BetaP.subst <;> first | apply ih1 | apply ih2

lemma subst_reduction (M N N' : Lambda) (n : Nat) : N →βp N' → M[n := N] →βp M[n := N'] := by
    intros
    induction M generalizing n with
    | var k =>
        simp; split_ifs; simp
        apply subst_shift; assumption; rfl
    | app M₁ M₂ ih1 ih2 =>
        simp
        apply BetaP.app <;> repeat first | apply ih1 | apply ih2 | assumption
    | abs M ih =>
        simp; apply ih
