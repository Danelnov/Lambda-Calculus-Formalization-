inductive Lambda
  | var : Nat → Lambda
  | abs : Lambda → Lambda
  | app : Lambda → Lambda → Lambda
  deriving DecidableEq, Repr

prefix:100 "λ " => Lambda.abs

def Lambda.toString : Lambda → String
  | var n => Nat.toDigits 10 n |> List.asString
  | abs e => s!"λ {e.toString}"
  | app e₁ e₂ =>
    match e₁, e₂ with
    | abs _, _ => s!"(({e₁.toString}) {e₂.toString})"
    | _, _ => s!"({e₁.toString} {e₂.toString})"

instance : ToString Lambda := ⟨Lambda.toString⟩

instance : Repr Lambda where
  reprPrec M _ := M.toString.toFormat

instance : Coe Nat Lambda := ⟨λ n => Lambda.var n⟩

instance : OfNat Lambda n := ⟨Lambda.var n⟩

namespace Lambda

@[simp]
def shift (c i : Nat) : Lambda → Lambda
  | var n =>
    if n < c then var n
    else var (n + i)
  | app e₁ e₂ => app (e₁.shift c i) (e₂.shift c i)
  | abs e => abs $ e.shift (c + 1) i

@[simp]
def unshift (c i : Nat) : Lambda → Lambda
  | var n =>
    if n < c then var n
    else var (n - i)
  | app e₁ e₂ => app (e₁.unshift c i) (e₂.unshift c i)
  | abs e => abs $ e.unshift (c + 1) i

notation:70 "↑" => Lambda.shift
notation:70 "↓" => Lambda.unshift

@[simp]
def subst (v : Lambda) (n : Nat) (e : Lambda) :=
  match v with
  | var m =>
    if m < n then
      var m
    else if n = m then
      (↑) 0 n e
    else
      var (m - 1)
  | app v₁ v₂ => app (v₁.subst n e) (v₂.subst n e)
  | abs v₁ => abs $ v₁.subst (n + 1) e

notation t " [" k " := " s "]" => Lambda.subst t k s

def beta (M N : Lambda) := (↓) 0 1 (M[0 := (↑) 0 1 N])

@[simp]
def range : Lambda → Nat
  | var n => n
  | app e₁ e₂ => max (e₁.range) (e₂.range)
  | abs e => e.range

end Lambda

inductive Beta : Lambda → Lambda → Prop
  | basis (M N : Lambda) : Beta ((λ M).app N) (Lambda.beta M N)
  | appr (M N L : Lambda) : Beta N M → Beta (N.app L) (M.app L)
  | appl (M N L : Lambda): Beta N M → Beta (L.app N) (L.app M)
  | abs (N M) : Beta N M → Beta (λ N) (λ M)

infixl:65 " →β " => Beta

inductive BetaP : Lambda → Lambda → Prop
  | refl (M) : BetaP M M
  | abs (N M) : BetaP N M → BetaP (λ N) (λ M)
  | app (M M' N N') : BetaP M M' → BetaP N N' → BetaP (M.app N) (M'.app N')
  | subst (M M' N N') : BetaP M M' → BetaP N N' → BetaP ((λ M).app N) (Lambda.beta M' N')

infixl:65 " →βp " => BetaP

@[refl]
theorem betap_refl {N : Lambda} :  N →βp N := BetaP.refl N

inductive BetaTR : Lambda → Lambda → Prop
  | refl (M) : BetaTR M M
  | step (M N L) : M →β L → BetaTR L N → BetaTR M N

infixl:65 " ⇒β " => BetaTR

@[refl]
theorem betatr_refl {N : Lambda} : N ⇒β N := BetaTR.refl N
