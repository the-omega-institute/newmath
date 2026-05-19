import BEDC.Derived.RealityConstrainedModelAuditUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.RealityConstrainedModelAuditUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Meta.TasteGate

theorem RealityConstrainedModelAuditSignatureExactness
    {H Pi O M C T L F S observed auditRead : BHist} :
    FieldFaithful.fields (RealityConstrainedModelAuditUp.mk H Pi O M C T L F S) =
        [H, Pi, O, M, C, T, L, F, S] →
      UnaryHistory H →
        UnaryHistory Pi →
          UnaryHistory M →
            Cont H Pi O →
              Cont O M C →
                Cont H Pi observed →
                  Cont observed M auditRead →
                    hsame O observed ∧
                      hsame C auditRead ∧
                        UnaryHistory O ∧
                          UnaryHistory observed ∧
                            UnaryHistory C ∧
                              UnaryHistory auditRead ∧
                                Cont H Pi O ∧
                                  Cont O M C ∧
                                    Cont H Pi observed ∧ Cont observed M auditRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory FieldFaithful
  intro fieldsExact hUnary piUnary mUnary observedRoute modelRoute alternateObservedRoute
    alternateAuditRoute
  have _fieldWitness :
      FieldFaithful.fields (RealityConstrainedModelAuditUp.mk H Pi O M C T L F S) =
        [H, Pi, O, M, C, T, L, F, S] :=
    fieldsExact
  have observedExact : hsame O observed :=
    cont_deterministic observedRoute alternateObservedRoute
  have auditExact : hsame C auditRead :=
    cont_respects_hsame observedExact (hsame_refl M) modelRoute alternateAuditRoute
  have observedUnary : UnaryHistory O :=
    unary_cont_closed hUnary piUnary observedRoute
  have alternateObservedUnary : UnaryHistory observed :=
    unary_cont_closed hUnary piUnary alternateObservedRoute
  have classifierUnary : UnaryHistory C :=
    unary_cont_closed observedUnary mUnary modelRoute
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed alternateObservedUnary mUnary alternateAuditRoute
  exact
    ⟨observedExact, auditExact, observedUnary, alternateObservedUnary, classifierUnary,
      auditUnary, observedRoute, modelRoute, alternateObservedRoute, alternateAuditRoute⟩

end BEDC.Derived.RealityConstrainedModelAuditUp
