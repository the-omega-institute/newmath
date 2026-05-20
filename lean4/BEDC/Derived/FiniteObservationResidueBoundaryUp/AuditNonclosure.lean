import BEDC.Derived.FiniteObservationResidueBoundaryUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.FiniteObservationResidueBoundaryUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem FiniteObservationResidueBoundaryAuditNonclosure
    {S Sigma K T L F H C P N auditRead : BHist} :
    UnaryHistory S →
      UnaryHistory Sigma →
        UnaryHistory T →
          UnaryHistory L →
            UnaryHistory F →
              Cont S Sigma K →
                Cont K T auditRead →
                  let packet :=
                    FiniteObservationResidueBoundaryUp.mk S Sigma K T L F H C P N
                  finiteObservationResidueBoundaryFields packet =
                      [S, Sigma, K, T, L, F, H, C, P, N] ∧
                    UnaryHistory K ∧
                      UnaryHistory auditRead ∧
                        List.Mem L (finiteObservationResidueBoundaryFields packet) ∧
                          List.Mem F (finiteObservationResidueBoundaryFields packet) ∧
                            Cont S Sigma K ∧ Cont K T auditRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro sourceUnary signatureUnary towerUnary _ledgerUnary _failureUnary sourceSignature
    classifierTower
  let packet := FiniteObservationResidueBoundaryUp.mk S Sigma K T L F H C P N
  have classifierUnary : UnaryHistory K :=
    unary_cont_closed sourceUnary signatureUnary sourceSignature
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed classifierUnary towerUnary classifierTower
  exact
    ⟨rfl, classifierUnary, auditReadUnary, by
      exact
        List.Mem.tail S
          (List.Mem.tail Sigma
            (List.Mem.tail K (List.Mem.tail T (List.Mem.head [F, H, C, P, N])))), by
      exact
        List.Mem.tail S
          (List.Mem.tail Sigma
            (List.Mem.tail K
              (List.Mem.tail T (List.Mem.tail L (List.Mem.head [H, C, P, N]))))),
      sourceSignature, classifierTower⟩

end BEDC.Derived.FiniteObservationResidueBoundaryUp
