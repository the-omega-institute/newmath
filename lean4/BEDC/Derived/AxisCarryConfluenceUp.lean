import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.AxisCarryConfluenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def AxisCarryConfluenceCarrier [AskSetup] [PackageSetup]
    (u v w n routeLeft routeRight valueLedger boundary continuation provenance nameRow :
      BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory n ∧
    UnaryHistory routeLeft ∧
      UnaryHistory routeRight ∧
        UnaryHistory u ∧
          UnaryHistory v ∧
            UnaryHistory w ∧
              UnaryHistory valueLedger ∧
                UnaryHistory boundary ∧
                  UnaryHistory continuation ∧
                    UnaryHistory provenance ∧
                      UnaryHistory nameRow ∧
                        Cont u v routeLeft ∧
                          Cont u w routeRight ∧
                            Cont routeLeft routeRight valueLedger ∧
                              Cont boundary continuation provenance ∧
                                PkgSig bundle nameRow pkg ∧
                                  SemanticNameCert
                                    (fun row : BHist => hsame row nameRow)
                                    (fun row : BHist =>
                                      hsame row routeLeft ∨ hsame row routeRight ∨
                                        hsame row valueLedger ∨ hsame row nameRow)
                                    (fun row : BHist =>
                                      PkgSig bundle nameRow pkg ∧ hsame row nameRow)
                                    hsame

theorem AxisCarryConfluenceCarrier_local_diamond [AskSetup] [PackageSetup]
    {u v w n routeLeft routeRight valueLedger boundary continuation provenance nameRow
      leftHandoff rightHandoff publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxisCarryConfluenceCarrier u v w n routeLeft routeRight valueLedger boundary
      continuation provenance nameRow bundle pkg →
      Cont routeLeft n leftHandoff →
        Cont routeRight n rightHandoff →
          Cont leftHandoff rightHandoff publicRead →
            PkgSig bundle publicRead pkg →
              UnaryHistory n ∧
                UnaryHistory leftHandoff ∧
                  UnaryHistory rightHandoff ∧
                    UnaryHistory publicRead ∧
                      Cont routeLeft n leftHandoff ∧
                        Cont routeRight n rightHandoff ∧
                          Cont leftHandoff rightHandoff publicRead ∧
                            PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert UnaryHistory
  intro carrier leftRoute rightRoute publicRoute publicPkg
  have nUnary : UnaryHistory n := carrier.left
  have routeLeftUnary : UnaryHistory routeLeft := carrier.right.left
  have routeRightUnary : UnaryHistory routeRight := carrier.right.right.left
  have leftHandoffUnary : UnaryHistory leftHandoff :=
    unary_cont_closed routeLeftUnary nUnary leftRoute
  have rightHandoffUnary : UnaryHistory rightHandoff :=
    unary_cont_closed routeRightUnary nUnary rightRoute
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed leftHandoffUnary rightHandoffUnary publicRoute
  exact
    ⟨nUnary, leftHandoffUnary, rightHandoffUnary, publicReadUnary, leftRoute,
      rightRoute, publicRoute, publicPkg⟩

end BEDC.Derived.AxisCarryConfluenceUp
