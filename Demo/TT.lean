/-!
# Simply Typed λ-Calculus

*Type Theory in Type Theory using Quotient Inductive Types* by Thorsten Altenkirch and Ambrus Kaposi.
-/

inductive Ty
  | emp
  | map (dom cod: Ty)

inductive Con
  | emp
  | ext (Γ: Con) (σ: Ty)

inductive Var: Con → Ty → Type
  | zero {Γ σ}: Var (.ext Γ σ) σ
  | succ {Γ σ τ}: Var Γ σ → Var (.ext Γ τ) σ

inductive Tm: Con → Ty → Type
  | var {Γ σ}: Var Γ σ → Tm Γ σ
  | app {Γ σ τ}: Tm Γ (.map σ τ) → Tm Γ σ → Tm Γ τ
  | all {Γ σ τ}: Tm (.ext Γ σ) τ → Tm Γ (.map σ τ)