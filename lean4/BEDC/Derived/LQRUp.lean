import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LQRUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def LQRFiniteControlPacket [AskSetup] [PackageSetup]
    (state control transition cost horizon estimator successor update predecessor endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory state ∧ UnaryHistory control ∧ UnaryHistory transition ∧
    UnaryHistory cost ∧ UnaryHistory horizon ∧ UnaryHistory estimator ∧
      UnaryHistory successor ∧ UnaryHistory update ∧ UnaryHistory predecessor ∧
        UnaryHistory endpoint ∧ Cont successor transition update ∧
          Cont update control predecessor ∧ Cont predecessor cost endpoint ∧
            Cont estimator horizon endpoint ∧ PkgSig bundle endpoint pkg

theorem LQRFiniteControlPacket_dynamic_programming_row [AskSetup] [PackageSetup]
    {state control transition cost horizon estimator successor update predecessor endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LQRFiniteControlPacket state control transition cost horizon estimator successor update
      predecessor endpoint bundle pkg ->
        Cont successor transition update ∧ Cont update control predecessor ∧
          Cont predecessor cost endpoint ∧ Cont estimator horizon endpoint ∧
            UnaryHistory horizon ∧ PkgSig bundle endpoint pkg := by
  intro packet
  cases packet with
  | intro _stateUnary packet =>
    cases packet with
    | intro _controlUnary packet =>
      cases packet with
      | intro _transitionUnary packet =>
        cases packet with
        | intro _costUnary packet =>
          cases packet with
          | intro horizonUnary packet =>
            cases packet with
            | intro _estimatorUnary packet =>
              cases packet with
              | intro _successorUnary packet =>
                cases packet with
                | intro _updateUnary packet =>
                  cases packet with
                  | intro _predecessorUnary packet =>
                    cases packet with
                    | intro _endpointUnary packet =>
                      cases packet with
                      | intro successorUpdate packet =>
                        cases packet with
                        | intro updatePredecessor packet =>
                          cases packet with
                          | intro predecessorEndpoint packet =>
                            cases packet with
                            | intro estimatorEndpoint endpointPkg =>
                              constructor
                              · exact successorUpdate
                              constructor
                              · exact updatePredecessor
                              constructor
                              · exact predecessorEndpoint
                              constructor
                              · exact estimatorEndpoint
                              constructor
                              · exact horizonUnary
                              · exact endpointPkg

theorem LQR_dynamic_programming_cont_determinacy
    {successor successor' transition transition' control control' cost cost' estimator estimator'
      provenance provenance' st st' stc stc' stcc stcc' stcce stcce' predecessor
      predecessor' : BHist} :
    hsame successor successor' -> hsame transition transition' -> hsame control control' ->
      hsame cost cost' -> hsame estimator estimator' -> hsame provenance provenance' ->
        Cont successor transition st -> Cont successor' transition' st' ->
          Cont st control stc -> Cont st' control' stc' ->
            Cont stc cost stcc -> Cont stc' cost' stcc' ->
              Cont stcc estimator stcce -> Cont stcc' estimator' stcce' ->
                Cont stcce provenance predecessor ->
                  Cont stcce' provenance' predecessor' -> hsame predecessor predecessor' := by
  intro sameSuccessor sameTransition sameControl sameCost sameEstimator sameProvenance rowSt rowSt'
    rowStc rowStc' rowStcc rowStcc' rowStcce rowStcce' rowPredecessor rowPredecessor'
  have sameSt : hsame st st' :=
    cont_respects_hsame sameSuccessor sameTransition rowSt rowSt'
  have sameStc : hsame stc stc' :=
    cont_respects_hsame sameSt sameControl rowStc rowStc'
  have sameStcc : hsame stcc stcc' :=
    cont_respects_hsame sameStc sameCost rowStcc rowStcc'
  have sameStcce : hsame stcce stcce' :=
    cont_respects_hsame sameStcc sameEstimator rowStcce rowStcce'
  exact cont_respects_hsame sameStcce sameProvenance rowPredecessor rowPredecessor'

end BEDC.Derived.LQRUp
