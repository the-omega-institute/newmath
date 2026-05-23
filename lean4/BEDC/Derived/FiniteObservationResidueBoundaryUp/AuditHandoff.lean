import BEDC.Derived.FiniteObservationResidueBoundaryUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.FiniteObservationResidueBoundaryUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem FiniteObservationResidueBoundaryAuditHandoff
    {S Sigma K T L F H C P N auditRead failureRead handoffRead : BHist} :
    UnaryHistory S →
      UnaryHistory Sigma →
        UnaryHistory T →
          UnaryHistory L →
            UnaryHistory F →
              UnaryHistory H →
                Cont S Sigma K →
                  Cont K T auditRead →
                    Cont L F failureRead →
                      Cont auditRead failureRead handoffRead →
                        let packet :=
                          FiniteObservationResidueBoundaryUp.mk S Sigma K T L F H C P N
                        finiteObservationResidueBoundaryFields packet =
                            [S, Sigma, K, T, L, F, H, C, P, N] ∧
                          UnaryHistory auditRead ∧
                            UnaryHistory failureRead ∧
                              UnaryHistory handoffRead ∧
                                Cont K T auditRead ∧
                                  Cont L F failureRead ∧
                                    Cont auditRead failureRead handoffRead ∧
                                      List.Mem P
                                        (finiteObservationResidueBoundaryFields packet) ∧
                                        List.Mem N
                                          (finiteObservationResidueBoundaryFields packet) := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro sourceUnary signatureUnary towerUnary ledgerUnary failureUnary _transportUnary
    sourceSignature classifierTower ledgerFailure auditFailureHandoff
  let packet := FiniteObservationResidueBoundaryUp.mk S Sigma K T L F H C P N
  have classifierUnary : UnaryHistory K :=
    unary_cont_closed sourceUnary signatureUnary sourceSignature
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed classifierUnary towerUnary classifierTower
  have failureReadUnary : UnaryHistory failureRead :=
    unary_cont_closed ledgerUnary failureUnary ledgerFailure
  have handoffReadUnary : UnaryHistory handoffRead :=
    unary_cont_closed auditReadUnary failureReadUnary auditFailureHandoff
  exact
    ⟨rfl, auditReadUnary, failureReadUnary, handoffReadUnary, classifierTower,
      ledgerFailure, auditFailureHandoff, by
        exact
          List.Mem.tail S
            (List.Mem.tail Sigma
              (List.Mem.tail K
                (List.Mem.tail T
                  (List.Mem.tail L
                    (List.Mem.tail F
                      (List.Mem.tail H (List.Mem.tail C (List.Mem.head [N])))))))), by
        exact
          List.Mem.tail S
            (List.Mem.tail Sigma
              (List.Mem.tail K
                (List.Mem.tail T
                  (List.Mem.tail L
                    (List.Mem.tail F
                      (List.Mem.tail H
                        (List.Mem.tail C (List.Mem.tail P (List.Mem.head [])))))))))⟩

end BEDC.Derived.FiniteObservationResidueBoundaryUp
