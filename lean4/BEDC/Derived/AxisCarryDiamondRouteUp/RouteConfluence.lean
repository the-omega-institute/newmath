import BEDC.Derived.AxisCarryDiamondRouteUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.AxisCarryDiamondRouteUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def AxisCarryDiamondRouteCarrier [AskSetup] [PackageSetup]
    (overlap carryLeft carryRight normal routeLeft routeRight valueLeft valueRight
      targetLedger boundary continuation provenance nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory overlap ∧
    UnaryHistory normal ∧
      UnaryHistory routeLeft ∧
        UnaryHistory routeRight ∧
          UnaryHistory carryLeft ∧
            UnaryHistory carryRight ∧
              UnaryHistory valueLeft ∧
                UnaryHistory valueRight ∧
                  UnaryHistory targetLedger ∧
                    UnaryHistory boundary ∧
                      UnaryHistory continuation ∧
                        UnaryHistory provenance ∧
                          UnaryHistory nameRow ∧
                            Cont overlap carryLeft routeLeft ∧
                              Cont overlap carryRight routeRight ∧
                                Cont valueLeft valueRight targetLedger ∧
                                  Cont boundary continuation provenance ∧
                                    PkgSig bundle nameRow pkg ∧
                                      SemanticNameCert
                                        (fun row : BHist => hsame row nameRow)
                                        (fun row : BHist =>
                                          hsame row routeLeft ∨ hsame row routeRight ∨
                                            hsame row targetLedger ∨ hsame row nameRow)
                                        (fun row : BHist =>
                                          PkgSig bundle nameRow pkg ∧ hsame row nameRow)
                                        hsame

theorem AxisCarryDiamondRouteCarrier_names_two_step_confluence [AskSetup] [PackageSetup]
    {overlap carryLeft carryRight normal routeLeft routeRight valueLeft valueRight
      targetLedger boundary continuation provenance nameRow leftHandoff rightHandoff
      sharedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxisCarryDiamondRouteCarrier overlap carryLeft carryRight normal routeLeft routeRight
      valueLeft valueRight targetLedger boundary continuation provenance nameRow bundle pkg →
      Cont routeLeft normal leftHandoff →
        Cont routeRight normal rightHandoff →
          Cont leftHandoff rightHandoff sharedRead →
            PkgSig bundle sharedRead pkg →
              UnaryHistory overlap ∧
                UnaryHistory normal ∧
                  UnaryHistory leftHandoff ∧
                    UnaryHistory rightHandoff ∧
                      UnaryHistory sharedRead ∧
                        Cont routeLeft normal leftHandoff ∧
                          Cont routeRight normal rightHandoff ∧
                            Cont leftHandoff rightHandoff sharedRead ∧
                              PkgSig bundle sharedRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert UnaryHistory
  intro carrier leftRoute rightRoute sharedRoute sharedPkg
  have overlapUnary : UnaryHistory overlap := carrier.left
  have normalUnary : UnaryHistory normal := carrier.right.left
  have routeLeftUnary : UnaryHistory routeLeft := carrier.right.right.left
  have routeRightUnary : UnaryHistory routeRight := carrier.right.right.right.left
  have leftHandoffUnary : UnaryHistory leftHandoff :=
    unary_cont_closed routeLeftUnary normalUnary leftRoute
  have rightHandoffUnary : UnaryHistory rightHandoff :=
    unary_cont_closed routeRightUnary normalUnary rightRoute
  have sharedReadUnary : UnaryHistory sharedRead :=
    unary_cont_closed leftHandoffUnary rightHandoffUnary sharedRoute
  exact
    ⟨overlapUnary, normalUnary, leftHandoffUnary, rightHandoffUnary, sharedReadUnary,
      leftRoute, rightRoute, sharedRoute, sharedPkg⟩

end BEDC.Derived.AxisCarryDiamondRouteUp
