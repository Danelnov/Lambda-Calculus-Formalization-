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

lemma para_shift_shifted {d c} {N₁ N₂ : Lambda} :
    N₁ →βp N₂ → Shifted d c N₁ → Shifted d c N₂ := by
    intro h₁ h₂
    induction h₁ generalizing c d with
    | var n => assumption
    | app => cases h₂; apply Shifted.sapp <;> aesop
    | abs => cases h₂; apply Shifted.sabs; aesop
    | subst M₁ M₂ L₁ L₂ hm hl ihm ihl =>
        simp [beta]; cases h₂; rename_i h1 h2; cases h1
        nth_rw 2 [Eq.symm (Nat.zero_add 1)]
        rw [Eq.symm (Nat.zero_add c)]
        apply shifted_subst <;> (first | apply ihm | apply ihl)
        rw [Nat.zero_add, Nat.add_comm]
        all_goals assumption

lemma para_unshift_conservation {i j : Nat} {N N' : Lambda} :
    Shifted j i N → N →βp N' → (↓) i j N →βp (↓) i j N' := by
    intro h₁ h₂
    induction h₂ generalizing i j with
    | var => rfl
    | abs => simp; cases h₁; aesop
    | app => simp; cases h₁; constructor <;> aesop
    | subst M₁ M₂ N₁ N₂ hm hn ihm ihn =>
        simp [beta]; cases h₁; rename_i h1 h2; cases h1; rename_i h1
        have hsn := para_shift_shifted hn h2
        have hsm := para_shift_shifted hm h1
        rw [unshift_unshift_swap (by omega) (by aesop) ?shifted]
        case shifted =>
            rw [Eq.symm (Nat.zero_add i)]
            nth_rw 2 [Eq.symm (Nat.zero_add 1)]
            apply shifted_subst <;> (try assumption)
            rw [Nat.zero_add, Nat.add_comm]; assumption
        rw [unshift_subst_swap2 (by omega) hsm ?shifted]
        case shifted =>
            rw [Nat.add_comm]; apply shift_shifted' <;> aesop

        rw [← unshift_shift_swap (by omega) hsn, ← beta]
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
        have : 0 + 1 + n = n + 1 := by omega
        rw [beta, ← unshift_subst_swap' _ _ (shifted_subst' 0 M' P'), ← this, substitution']
        simp_all
        rw [← shift_subst_swap', ← beta]
        apply BetaP.subst
        apply ihm; apply para_shift_conservation; assumption
        all_goals aesop

lemma para_beta {M N M' N' : Lambda} :
    M →βp M' → N →βp N' → M.beta N →βp M'.beta N' := by
    intro hm hn; simp [beta]
    apply para_unshift_conservation
    . exact shifted_subst' 0 M N
    . apply (para_subst hm); exact para_shift_conservation hn

lemma abs_para_abs {M N : Lambda} (h : λ M →βp N) : ∃ M', N = λ M' ∧ M →βp M' := by cases h; case abs => aesop

lemma app_para_cases {M N L : Lambda} (h : M.app N →βp L) :
    (∃ M' N', L = M'.app N' ∧ M →βp M' ∧ N →βp N') ∨
    (∃ P P' N', M = λ P ∧ L = P'.beta N' ∧ N →βp N' ∧ P →βp P') := by
    cases h
    case app M' N' _ _ => left; use M', N'
    case subst P M' N' _ _ => right; use P, M', N'

def Diamond (R : α → α → Prop) := ∀ a b c, R a b → R a c → ∃ d, R b d ∧ R c d

theorem para_diamond : Diamond BetaP := by
    unfold Diamond; intro M M₁ M₂ h1 h2
    induction h1 generalizing M₂ with
    | var => simp at h2; simp_all
    | abs N₁ N₂ h ih =>
        obtain ⟨N₃, _, N₁reN₃⟩ := abs_para_abs h2
        obtain ⟨N₄, _, _⟩ := ih N₃ N₁reN₃
        use λ N₄; aesop
    | app N₁ N₂ P₁ P₂ hn₁₂ hp₁₂ ihn ihp =>

        rcases app_para_cases h2 with ⟨N₃, P₃, M₂eq, N₁reN₃, P₁reP₃⟩
            | ⟨L₁, L₂, P₃, N₁eq, M₂eq, P₁reP₂, L₁reL₂⟩
        . obtain ⟨N₄, _, _⟩ := ihn N₃ N₁reN₃
          obtain ⟨P₄, _, _⟩ := ihp P₃ P₁reP₃
          rw [M₂eq]
          use N₄.app P₄; constructor <;> apply BetaP.app <;> aesop
        .
            sorry
    | subst => sorry
