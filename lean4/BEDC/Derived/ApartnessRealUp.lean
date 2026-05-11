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

def ApartnessRealPositiveSeparationCarrier [AskSetup] [PackageSetup]
    (leftName rightName radius window leftReadback rightReadback separation provenance
      endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory leftName ∧ UnaryHistory rightName ∧ UnaryHistory radius ∧
    UnaryHistory window ∧ UnaryHistory provenance ∧ Cont leftName radius leftReadback ∧
      Cont rightName window rightReadback ∧ Cont leftReadback rightReadback separation ∧
        Cont separation provenance endpoint ∧ PkgSig bundle endpoint pkg

theorem ApartnessRealPositiveSeparationCarrier_metric_handoff [AskSetup] [PackageSetup]
    {leftName rightName radius window leftReadback rightReadback separation provenance
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApartnessRealPositiveSeparationCarrier leftName rightName radius window leftReadback
        rightReadback separation provenance endpoint bundle pkg ->
      UnaryHistory leftReadback ∧ UnaryHistory rightReadback ∧ UnaryHistory separation ∧
        hsame separation (append leftReadback rightReadback) ∧ UnaryHistory endpoint ∧
          hsame endpoint (append separation provenance) ∧ PkgSig bundle endpoint pkg := by
  intro carrier
  have leftNameUnary : UnaryHistory leftName :=
    carrier.left
  have rightNameUnary : UnaryHistory rightName :=
    carrier.right.left
  have radiusUnary : UnaryHistory radius :=
    carrier.right.right.left
  have windowUnary : UnaryHistory window :=
    carrier.right.right.right.left
  have provenanceUnary : UnaryHistory provenance :=
    carrier.right.right.right.right.left
  have leftReadbackRow : Cont leftName radius leftReadback :=
    carrier.right.right.right.right.right.left
  have rightReadbackRow : Cont rightName window rightReadback :=
    carrier.right.right.right.right.right.right.left
  have separationRow : Cont leftReadback rightReadback separation :=
    carrier.right.right.right.right.right.right.right.left
  have endpointRow : Cont separation provenance endpoint :=
    carrier.right.right.right.right.right.right.right.right.left
  have packageBoundary : PkgSig bundle endpoint pkg :=
    carrier.right.right.right.right.right.right.right.right.right
  have leftReadbackUnary : UnaryHistory leftReadback :=
    unary_cont_closed leftNameUnary radiusUnary leftReadbackRow
  have rightReadbackUnary : UnaryHistory rightReadback :=
    unary_cont_closed rightNameUnary windowUnary rightReadbackRow
  have separationUnary : UnaryHistory separation :=
    unary_cont_closed leftReadbackUnary rightReadbackUnary separationRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed separationUnary provenanceUnary endpointRow
  exact And.intro leftReadbackUnary
    (And.intro rightReadbackUnary
      (And.intro separationUnary
        (And.intro separationRow
          (And.intro endpointUnary
            (And.intro endpointRow packageBoundary)))))

end BEDC.Derived.ApartnessRealUp
