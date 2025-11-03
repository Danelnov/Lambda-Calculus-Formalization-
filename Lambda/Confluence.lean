import Lambda.Defs
import Lambda.Properties
import Lambda.Diamond
import Mathlib.Tactic

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

section ShiftedLemmas

variable {d c : Nat} {N₁ N₂ : Lambda}

lemma para_shift_shifted:
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

lemma para_unshift_conservation:
    Shifted d c N₁ → N₁ →βp N₂ → (↓) c d N₁ →βp (↓) c d N₂ := by
    intro h₁ h₂
    induction h₂ generalizing d c with
    | var => rfl
    | abs => simp; cases h₁; aesop
    | app => simp; cases h₁; constructor <;> aesop
    | subst M₁ M₂ N₁ N₂ hm hn ihm ihn =>
        simp [beta]; cases h₁; rename_i h1 h2; cases h1; rename_i h1
        have hsn := para_shift_shifted hn h2
        have hsm := para_shift_shifted hm h1
        rw [unshift_unshift_swap (by omega) (by aesop) ?shifted]
        case shifted =>
            rw [Eq.symm (Nat.zero_add c)]
            nth_rw 2 [Eq.symm (Nat.zero_add 1)]
            apply shifted_subst <;> (try assumption)
            rw [Nat.zero_add, Nat.add_comm]; assumption
        rw [unshift_subst_swap2 (by omega) hsm ?shifted]
        case shifted =>
            rw [Nat.add_comm]; apply shift_shifted' <;> aesop

        rw [← unshift_shift_swap (by omega) hsn, ← beta]
        apply BetaP.subst <;> aesop

end ShiftedLemmas

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
    . exact (para_subst hm) (para_shift_conservation hn)

lemma abs_para_abs {M N : Lambda} (h : λ M →βp N) : ∃ M', N = λ M' ∧ M →βp M' := by cases h; case abs => aesop

lemma app_para_cases {M N L : Lambda} (h : M.app N →βp L) :
    (∃ M' N', L = M'.app N' ∧ M →βp M' ∧ N →βp N') ∨
    (∃ P P' N', M = λ P ∧ L = P'.beta N' ∧ N →βp N' ∧ P →βp P') := by
    cases h
    case app M' N' _ _ => left; use M', N'
    case subst P M' N' _ _ => right; use P, M', N'

theorem para_diamond : Diamond BetaP := by
    unfold Diamond; intro M M₁ M₂ h1 h2
    induction h1 generalizing M₂ with
    | var => simp at h2; simp_all
    | abs N₁ N₂ h ih =>
        obtain ⟨N₃, _, N₁reN₃⟩ := abs_para_abs h2
        obtain ⟨N₄, _, _⟩ := ih N₁reN₃
        use λ N₄; aesop
    | app N₁ N₂ P₁ P₂ hn₁₂ hp₁₂ ihn ihp =>
        rcases app_para_cases h2 with ⟨N₃, P₃, rfl, N₁reN₃, P₁reP₃⟩
            | ⟨L₁, L₃, P₃, rfl, rfl, P₁reP₃, L₁reL₃⟩
        . obtain ⟨N₄, _, _⟩ := ihn N₁reN₃
          obtain ⟨P₄, _, _⟩ := ihp P₁reP₃
          use N₄.app P₄; constructor <;> apply BetaP.app <;> aesop
        . obtain ⟨P₄, _, _⟩ := ihp P₁reP₃
          obtain ⟨L₂, rfl, _⟩ := abs_para_abs hn₁₂
          obtain ⟨N', N₂re, L₃re⟩ := @ihn (λ L₃) (by aesop)
          obtain ⟨L₄, rfl, _⟩ := abs_para_abs N₂re
          cases L₃re
          use L₄.beta P₄; constructor
          . apply BetaP.subst <;> assumption
          . apply para_beta <;> assumption
    | subst N₁ N₂ P₁ P₂ hn hp ihn ihp=>
        rcases app_para_cases h2 with ⟨M', P₃, rfl, lN₁reL₁, P₁reP₃⟩ |
          ⟨N', N₃, P₃, lN₁eq, rfl, P₁reP₃, N'reN₃⟩
        . obtain ⟨N₃, rfl, N₁reN₃⟩ := abs_para_abs lN₁reL₁
          obtain ⟨N₄, _, _⟩ := ihn N₁reN₃
          obtain ⟨P₄, _, _⟩ := ihp P₁reP₃
          use N₄.beta P₄; constructor
          apply para_beta <;> assumption
          apply BetaP.subst <;> assumption
        . simp at lN₁eq; rw [← lN₁eq] at N'reN₃
          obtain ⟨N₄, _, _⟩ := ihn N'reN₃
          obtain ⟨P₄, _, _⟩ := ihp P₁reP₃
          use N₄.beta P₄; constructor <;> apply para_beta <;> assumption

section BetaTRprops

variable {M₁ M₂ : Lambda}

lemma appr_cong {N : Lambda} (h : M₁ ⇒β M₂) : M₁.app N ⇒β M₂.app N := by
    induction h with
    | refl => rfl
    | tail h₁ h₂ ih=>
        expose_names
        exact Relation.ReflTransGen.tail ih (Beta.appr c b N h₂)

lemma appl_cong {N : Lambda} (h : M₁ ⇒β M₂) : N.app M₁ ⇒β N.app M₂ := by
    induction h with
    | refl => rfl
    | tail h₁ h₂ ih =>
        expose_names
        exact Relation.ReflTransGen.tail ih (Beta.appl c b N h₂)

@[simp]
lemma app_cong {N₁ N₂ : Lambda} (hm : M₁ ⇒β M₂) (hn : N₁ ⇒β N₂) :
    M₁.app N₁ ⇒β M₂.app N₂ := by
    calc
        M₁.app N₁ ⇒β M₂.app N₁ := appr_cong hm
        _         ⇒β M₂.app N₂ := appl_cong hn

lemma abs_cong (h : M₁ ⇒β M₂) : (λ M₁) ⇒β (λ M₂) := by
    induction h with
    | refl => rfl
    | tail h₁ h₂ ih =>
        expose_names
        exact Relation.ReflTransGen.tail ih (Beta.abs b c h₂)

lemma beta_shift_cong {c d : ℕ} (h : M₁ →β M₂) : (↑) c d M₁ →β (↑) c d M₂ := by
    induction h generalizing c with
    | basis N₁ N₂ =>
        simp; unfold beta
        rw [shift_unshift_swap (Nat.zero_le c) (shifted_subst' 0 N₁ N₂)]
        simp
        rw [← shift_shift_swap _ (Nat.zero_le c), ← beta]
        apply Beta.basis
    | _ =>
        simp; constructor; simp_all

lemma shift_cong {c d : ℕ} (h : M₁ ⇒β M₂) : (↑) c d M₁ ⇒β (↑) c d M₂ := by
    induction h with
    | refl => rfl
    | tail h₁ h₂ ih =>
        rename_i N₁ N₂
        exact Relation.ReflTransGen.tail ih (beta_shift_cong h₂)

lemma sub_reduction {i : ℕ} {N : Lambda} (h : M₁ ⇒β M₂) :
    N[i := M₁] ⇒β N[i := M₂] := by
    induction N generalizing i M₁ M₂ with
    | var n =>
        simp_all; split <;> aesop
    | app N₁ N₂ ih1 ih2 =>
        simp_all
    | abs N ih => exact abs_cong (ih <| shift_cong h)

end BetaTRprops

lemma step_para {M₁ M₂ : Lambda} (step : M₁ →β M₂) : M₁ →βp M₂ := by
    induction step <;> (constructor <;> aesop)

lemma para_betatr {M₁ M₂ : Lambda} (para : M₁ →βp M₂) : M₁ ⇒β M₂ := by
    induction M₁ generalizing M₂ with
    | var n => simp_all; rfl
    | abs N₁ ih =>
        obtain ⟨N₂, rfl, h₂⟩  := abs_para_abs para
        exact abs_cong (ih h₂)
    | app N₁ N₂ ih₁ ih₂ =>
        rcases app_para_cases para with ⟨L₁, L₂, rfl, h₁, h₂⟩
            | ⟨P₁, P₂, N₃, rfl, rfl, hn, hp⟩
        simp_all
        calc
            (λ P₁).app N₂ ⇒β (λ P₂).app N₂ := appr_cong (ih₁ <| abs_reduction.mpr hp)
            _             ⇒β (λ P₂).app N₃ := appl_cong (ih₂ hn)
            _             ⇒β P₂.beta N₃ := by
                apply Relation.ReflTransGen.single
                apply Beta.basis

notation:65 M₁ " →β* " M₂ => Relation.ReflTransGen BetaP M₁ M₂

lemma paratr_iff_betatr {M N : Lambda} : (M →β* N) ↔ (M ⇒β N) := by
    constructor <;> intro h <;> induction h <;> try rfl
    all_goals rename_i h₁ h₂
    exact Relation.ReflTransGen.trans h₂ (para_betatr h₁)
    exact Relation.ReflTransGen.tail h₂ (step_para h₁)

theorem church_rosser : Diamond <| Relation.ReflTransGen Beta := by
    apply equiv_confluence
    apply paratr_iff_betatr
    apply confluence
    exact para_diamond
