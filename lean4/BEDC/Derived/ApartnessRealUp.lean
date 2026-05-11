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

def ApartnessRealMetricHandoffPacket [AskSetup] [PackageSetup]
    (left right radius window leftReadback rightReadback separation provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory left ∧ UnaryHistory right ∧ UnaryHistory radius ∧ UnaryHistory window ∧
    UnaryHistory provenance ∧ Cont left window leftReadback ∧
      Cont right window rightReadback ∧ Cont leftReadback rightReadback separation ∧
        Cont separation provenance endpoint ∧ PkgSig bundle endpoint pkg

theorem ApartnessRealMetricHandoffPacket_transport [AskSetup] [PackageSetup]
    {left right radius window leftReadback rightReadback separation provenance endpoint left'
      right' radius' window' leftReadback' rightReadback' separation' provenance'
      endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApartnessRealMetricHandoffPacket left right radius window leftReadback rightReadback
        separation provenance endpoint bundle pkg ->
      hsame left left' -> hsame right right' -> hsame radius radius' ->
        hsame window window' -> hsame provenance provenance' ->
          Cont left' window' leftReadback' -> Cont right' window' rightReadback' ->
            Cont leftReadback' rightReadback' separation' ->
              Cont separation' provenance' endpoint' -> PkgSig bundle endpoint' pkg ->
                ApartnessRealMetricHandoffPacket left' right' radius' window' leftReadback'
                    rightReadback' separation' provenance' endpoint' bundle pkg ∧
                  hsame leftReadback leftReadback' ∧ hsame rightReadback rightReadback' ∧
                    hsame separation separation' ∧ hsame endpoint endpoint' := by
  intro packet sameLeft sameRight sameRadius sameWindow sameProvenance
  intro leftRow' rightRow' separationRow' endpointRow' pkgSig'
  have sameLeftReadback : hsame leftReadback leftReadback' :=
    cont_respects_hsame sameLeft sameWindow
      packet.right.right.right.right.right.left leftRow'
  have sameRightReadback : hsame rightReadback rightReadback' :=
    cont_respects_hsame sameRight sameWindow
      packet.right.right.right.right.right.right.left rightRow'
  have sameSeparation : hsame separation separation' :=
    cont_respects_hsame sameLeftReadback sameRightReadback
      packet.right.right.right.right.right.right.right.left separationRow'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameSeparation sameProvenance
      packet.right.right.right.right.right.right.right.right.left endpointRow'
  have transported :
      ApartnessRealMetricHandoffPacket left' right' radius' window' leftReadback'
          rightReadback' separation' provenance' endpoint' bundle pkg :=
    ⟨unary_transport packet.left sameLeft,
      unary_transport packet.right.left sameRight,
      unary_transport packet.right.right.left sameRadius,
      unary_transport packet.right.right.right.left sameWindow,
      unary_transport packet.right.right.right.right.left sameProvenance,
      leftRow',
      rightRow',
      separationRow',
      endpointRow',
      pkgSig'⟩
  exact ⟨transported, sameLeftReadback, sameRightReadback, sameSeparation, sameEndpoint⟩

end BEDC.Derived.ApartnessRealUp
