import BEDC.Derived.ReviewAcceptanceGateUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ReviewAcceptanceGateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ReviewAcceptanceGateHumanApprovalBoundary [AskSetup] [PackageSetup]
    {S D R A M K Q H C P N proposalDecision approvalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory S -> UnaryHistory D -> UnaryHistory A -> Cont S D proposalDecision ->
      Cont proposalDecision A approvalRead -> PkgSig bundle approvalRead pkg ->
        UnaryHistory proposalDecision ∧ UnaryHistory approvalRead ∧
          Cont S D proposalDecision ∧ Cont proposalDecision A approvalRead ∧
            PkgSig bundle approvalRead pkg ∧
              List.Mem A
                (reviewAcceptanceGateFields
                  (ReviewAcceptanceGateUp.mk S D R A M K Q H C P N)) := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory
  intro proposalUnary decisionUnary approvalUnary proposalDecisionCont approvalReadCont
    approvalPkg
  have proposalDecisionUnary : UnaryHistory proposalDecision :=
    unary_cont_closed proposalUnary decisionUnary proposalDecisionCont
  have approvalReadUnary : UnaryHistory approvalRead :=
    unary_cont_closed proposalDecisionUnary approvalUnary approvalReadCont
  exact
    ⟨proposalDecisionUnary, approvalReadUnary, proposalDecisionCont, approvalReadCont,
      approvalPkg,
      List.Mem.tail S
        (List.Mem.tail D
          (List.Mem.tail R (List.Mem.head [M, K, Q, H, C, P, N])))⟩

end BEDC.Derived.ReviewAcceptanceGateUp
