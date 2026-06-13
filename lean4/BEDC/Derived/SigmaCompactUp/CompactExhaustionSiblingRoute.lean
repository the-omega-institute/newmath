import BEDC.Derived.SigmaCompactUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SigmaCompactUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SigmaCompactCompactExhaustionSiblingRoute [AskSetup] [PackageSetup]
    {X E K B L H C P N compactEntry closedBall localSupport : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont X E compactEntry →
      Cont compactEntry K closedBall →
        Cont closedBall L localSupport →
          PkgSig bundle localSupport pkg →
            UnaryHistory X →
              UnaryHistory E →
                UnaryHistory K →
                  UnaryHistory L →
                    UnaryHistory compactEntry ∧ UnaryHistory closedBall ∧
                      UnaryHistory localSupport ∧ Cont X E compactEntry ∧
                        Cont compactEntry K closedBall ∧
                          Cont closedBall L localSupport ∧
                            PkgSig bundle localSupport pkg ∧
                              sigmaCompactFromEventFlow
                                  (sigmaCompactToEventFlow
                                    (SigmaCompactUp.mk X E K B L H C P N)) =
                                some (SigmaCompactUp.mk X E K B L H C P N) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro compactRoute closedBallRoute supportRoute supportPkg xUnary eUnary kUnary lUnary
  have compactUnary : UnaryHistory compactEntry :=
    unary_cont_closed xUnary eUnary compactRoute
  have closedBallUnary : UnaryHistory closedBall :=
    unary_cont_closed compactUnary kUnary closedBallRoute
  have supportUnary : UnaryHistory localSupport :=
    unary_cont_closed closedBallUnary lUnary supportRoute
  obtain ⟨_gate, _decode, roundTrip, _emptyEncode⟩ :=
    SigmaCompactTasteGate_single_carrier_alignment
  exact
    ⟨compactUnary, closedBallUnary, supportUnary, compactRoute, closedBallRoute,
      supportRoute, supportPkg, roundTrip (SigmaCompactUp.mk X E K B L H C P N)⟩

end BEDC.Derived.SigmaCompactUp
