import BEDC.MetaCIC.SubjectReduction.CongCases

namespace BEDC.MetaCIC

theorem subject_reduction_beta
    (hsubst : BetaSubstitutionPreservation)
    {Γ : Ctx} {dom body arg A : Term}
    (ht : HasType Γ (Term.app (Term.lam dom body) arg) A) :
    HasType Γ (substitute 0 arg body) A := by
  cases ht with
  | appRule Γ f a appDom cod hf ha =>
      cases hf with
      | lamRule Γ lamDom lamBody lamCod hdom hbody =>
          exact hsubst hbody ha

theorem subject_reduction
    (hsubst : BetaSubstitutionPreservation)
    (happArgStable : AppArgTypeStable)
    (hlamDom : LamDomainSubjectReduction)
    (hpiDom : PiDomainSubjectReduction)
    {Γ : Ctx} {t t' A : Term}
    (ht : HasType Γ t A)
    (hbeta : BetaStep t t') :
    HasType Γ t' A := by
  induction hbeta generalizing Γ A with
  | beta dom body arg =>
      exact subject_reduction_beta hsubst ht
  | congApp1 f f' a hb ih =>
      exact subject_reduction_congApp1 ht hb
        (fun {B} hf => ih hf)
  | congApp2 f a a' hb ih =>
      cases ht with
      | appRule Γ f a dom cod hf ha =>
          have ha' : HasType Γ a' dom := ih ha
          rw [← happArgStable hf ha ha']
          exact HasType.appRule Γ f a' dom cod hf ha'
  | congLam d b b' hb ih =>
      exact subject_reduction_congLam ht hb
        (fun {B} hbody => ih hbody)
  | congPiCod d c c' hb ih =>
      exact subject_reduction_congPi ht hb
        (fun hcod => ih hcod)
  | congPiDom d d' c hb ih =>
      exact hpiDom ht hb
  | congLamDom d d' b hb ih =>
      exact hlamDom ht hb

theorem subject_reduction_retype
    (hsubst : BetaSubstitutionPreservation)
    (happArgStable : AppArgTypeStable)
    (hlamDom : LamDomainSubjectReduction)
    (hpiDom : PiDomainSubjectReduction)
    {Γ : Ctx} {t t' A : Term}
    (ht : HasType Γ t A)
    (hbeta : BetaStep t t') :
    ∃ A' : Term, HasType Γ t' A' := by
  exact ⟨A, subject_reduction hsubst happArgStable hlamDom hpiDom ht hbeta⟩

def closedBinderRedexTerm : Term :=
  Term.lam Term.sort
    (Term.app (Term.lam Term.sort (Term.var 0)) (Term.var 0))

theorem closedBinderRedexTerm_closed :
    ClosedAt 0 closedBinderRedexTerm := by
  unfold closedBinderRedexTerm
  apply ClosedAt.lamClosed
  · exact ClosedAt.sortClosed
  · apply ClosedAt.appClosed
    · apply ClosedAt.lamClosed
      · exact ClosedAt.sortClosed
      · apply ClosedAt.varClosed
        exact Nat.zero_lt_succ 1
    · apply ClosedAt.varClosed
      exact Nat.zero_lt_succ 0

theorem closedBinderRedexTerm_steps :
    BetaStep closedBinderRedexTerm
      (Term.lam Term.sort (Term.var 0)) := by
  unfold closedBinderRedexTerm
  exact BetaStep.congLam Term.sort
    (Term.app (Term.lam Term.sort (Term.var 0)) (Term.var 0))
    (Term.var 0)
    (BetaStep.beta Term.sort (Term.var 0) (Term.var 0))

theorem closedBinderRedexTerm_argument_not_closed :
    ¬ ClosedAt 0 (Term.var 0) := by
  intro h
  cases h with
  | varClosed hlt =>
      exact Nat.not_lt_zero 0 hlt

theorem closed_term_step_has_unclosed_local_argument :
    ∃ d dom body arg : Term,
      ClosedAt 0 (Term.lam d (Term.app (Term.lam dom body) arg)) ∧
        BetaStep
          (Term.lam d (Term.app (Term.lam dom body) arg))
          (Term.lam d (substitute 0 arg body)) ∧
        ¬ ClosedAt 0 arg := by
  exact ⟨Term.sort,
    Term.sort,
    Term.var 0,
    Term.var 0,
    closedBinderRedexTerm_closed,
    closedBinderRedexTerm_steps,
    closedBinderRedexTerm_argument_not_closed⟩

end BEDC.MetaCIC
