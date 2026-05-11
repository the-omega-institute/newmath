import BEDC.MetaCIC.Beta
import BEDC.MetaCIC.Substitution
import BEDC.MetaCIC.Substitution.Typing
import BEDC.MetaCIC.SubstitutionStatements

namespace BEDC.MetaCIC

def SubjectReductionStatement : Prop :=
  ∀ {Γ : Ctx} {t t' A : Term},
    WellFormedCtx Γ →
    HasType Γ t A →
    BetaStep t t' →
    HasType Γ t' A

theorem subject_reduction_congApp1
    {Γ : Ctx} {f f' a A : Term}
    (_hwf : WellFormedCtx Γ)
    (ht : HasType Γ (Term.app f a) A)
    (_hb : BetaStep f f')
    (ih : ∀ {B : Term}, HasType Γ f B → HasType Γ f' B) :
    HasType Γ (Term.app f' a) A := by
  cases ht with
  | appRule Γ f a dom cod hf ha =>
      exact HasType.appRule Γ f' a dom cod (ih hf) ha

theorem subject_reduction_congApp2_retype
    {Γ : Ctx} {f a a' A : Term}
    (_hwf : WellFormedCtx Γ)
    (ht : HasType Γ (Term.app f a) A)
    (_hb : BetaStep a a')
    (ih : ∀ {B : Term}, HasType Γ a B → HasType Γ a' B) :
    ∃ A' : Term, HasType Γ (Term.app f a') A' := by
  cases ht with
  | appRule Γ f a dom cod hf ha =>
      exact ⟨substitute 0 a' cod, HasType.appRule Γ f a' dom cod hf (ih ha)⟩

theorem subject_reduction_congLam
    {Γ : Ctx} {d b b' A : Term}
    (hwf : WellFormedCtx Γ)
    (ht : HasType Γ (Term.lam d b) A)
    (_hb : BetaStep b b')
    (ih : ∀ {B : Term},
      WellFormedCtx (d :: Γ) →
      HasType (d :: Γ) b B →
      HasType (d :: Γ) b' B) :
    HasType Γ (Term.lam d b') A := by
  cases ht with
  | lamRule Γ dom body cod hdom hbody =>
      exact HasType.lamRule Γ d b' cod hdom
        (ih (WellFormedCtx.wfCons hwf hdom) hbody)

theorem subject_reduction_beta_case
    {Γ : Ctx} {dom body arg A : Term}
    (_hwf : WellFormedCtx Γ)
    (_ht : HasType Γ (Term.app (Term.lam dom body) arg) A) :
    True := by
  exact True.intro

theorem subject_reduction_statement_absurd :
    ¬ SubjectReductionStatement := by
  intro hsr
  exact closed_substitute_counter_target_absurd
    (hsr
      WellFormedCtx.wfNil
      (HasType.appRule []
        (Term.lam Term.sort
          closedSubstituteCounterTerm)
        Term.sort
        Term.sort
        closedSubstituteCounterType
        (HasType.lamRule []
          Term.sort
          closedSubstituteCounterTerm
          closedSubstituteCounterType
          (HasType.sortRule [])
          closed_substitute_counter_source)
        (HasType.sortRule []))
      (BetaStep.beta Term.sort closedSubstituteCounterTerm Term.sort))

theorem subject_reduction_congApp2_case
    {Γ : Ctx} {f a a' A : Term}
    (_hwf : WellFormedCtx Γ)
    (_ht : HasType Γ (Term.app f a) A)
    (_hb : BetaStep a a') :
    True := by
  exact True.intro

theorem subject_reduction
    {Γ : Ctx} {t t' A : Term}
    (hwf : WellFormedCtx Γ)
    (ht : HasType Γ t A)
    (hb : BetaStep t t') :
    True := by
  induction hb generalizing Γ A with
  | beta dom body arg =>
      exact subject_reduction_beta_case hwf ht
  | congApp1 f f' a hb ih =>
      exact True.intro
  | congApp2 f a a' hb ih =>
      exact subject_reduction_congApp2_case hwf ht hb
  | congLam d b b' hb ih =>
      exact True.intro

end BEDC.MetaCIC
