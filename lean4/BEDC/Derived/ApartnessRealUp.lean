import BEDC.Derived.RatUp
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ApartnessRealUp

open BEDC.Derived.RatUp
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ApartnessRealSeparationPacket [AskSetup] [PackageSetup]
    (left right radius window leftEndpoint rightEndpoint forwardLedger reverseLedger pkgrow :
      BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  PositiveUnaryDenominator radius ∧ Cont left window leftEndpoint ∧
    Cont right window rightEndpoint ∧ Cont leftEndpoint rightEndpoint forwardLedger ∧
      Cont rightEndpoint leftEndpoint reverseLedger ∧
        Cont forwardLedger reverseLedger pkgrow ∧
          Cont reverseLedger forwardLedger pkgrow ∧ PkgSig bundle pkgrow pkg

theorem ApartnessRealSeparationPacket_symmetry_stability [AskSetup] [PackageSetup]
    {left right radius window leftEndpoint rightEndpoint forwardLedger reverseLedger pkgrow :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApartnessRealSeparationPacket left right radius window leftEndpoint rightEndpoint
        forwardLedger reverseLedger pkgrow bundle pkg ->
      ApartnessRealSeparationPacket right left radius window rightEndpoint leftEndpoint
          reverseLedger forwardLedger pkgrow bundle pkg ∧
        hsame radius radius ∧ hsame window window := by
  intro packet
  exact
    And.intro
      (And.intro packet.left
        (And.intro packet.right.right.left
          (And.intro packet.right.left
            (And.intro packet.right.right.right.right.left
              (And.intro packet.right.right.right.left
                (And.intro packet.right.right.right.right.right.right.left
                  (And.intro packet.right.right.right.right.right.left
                    packet.right.right.right.right.right.right.right)))))))
      (And.intro (hsame_refl radius) (hsame_refl window))

theorem ApartnessRealSeparationPacket_metric_handoff [AskSetup] [PackageSetup]
    {leftName rightName radius window leftEndpoint rightEndpoint separation metricRow endpoint :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory leftName ->
    UnaryHistory rightName ->
    UnaryHistory radius ->
    UnaryHistory window ->
    UnaryHistory metricRow ->
    Cont leftName rightName leftEndpoint ->
    Cont radius window rightEndpoint ->
    Cont leftEndpoint rightEndpoint separation ->
    Cont separation metricRow endpoint ->
    PkgSig bundle endpoint pkg ->
      UnaryHistory leftEndpoint ∧ UnaryHistory rightEndpoint ∧ UnaryHistory separation ∧
        UnaryHistory endpoint ∧ hsame separation (append leftEndpoint rightEndpoint) ∧
          hsame endpoint (append separation metricRow) ∧ PkgSig bundle endpoint pkg := by
  intro leftUnary rightUnary radiusUnary windowUnary metricUnary leftEndpointRow rightEndpointRow
    separationRow endpointRow pkgSig
  have leftEndpointUnary : UnaryHistory leftEndpoint :=
    unary_cont_closed leftUnary rightUnary leftEndpointRow
  have rightEndpointUnary : UnaryHistory rightEndpoint :=
    unary_cont_closed radiusUnary windowUnary rightEndpointRow
  have separationUnary : UnaryHistory separation :=
    unary_cont_closed leftEndpointUnary rightEndpointUnary separationRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed separationUnary metricUnary endpointRow
  exact And.intro leftEndpointUnary
    (And.intro rightEndpointUnary
      (And.intro separationUnary
        (And.intro endpointUnary
          (And.intro separationRow
            (And.intro endpointRow pkgSig)))))

end BEDC.Derived.ApartnessRealUp
