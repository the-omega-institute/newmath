import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Cancellation
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.HolonomyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def HolonomyTransportPacket [AskSetup] [PackageSetup]
    (bundle connection loop endpoint curvatureLedger compositionLedger provenance : BHist)
    (probe : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory bundle ∧ UnaryHistory connection ∧ UnaryHistory loop ∧
    UnaryHistory endpoint ∧ UnaryHistory curvatureLedger ∧
      UnaryHistory compositionLedger ∧ UnaryHistory provenance ∧
        Cont connection loop endpoint ∧ Cont endpoint curvatureLedger compositionLedger ∧
          PkgSig probe provenance pkg

theorem HolonomyTransportPacket_parallel_transport_stability [AskSetup] [PackageSetup]
    {bundle bundle' connection connection' loop loop' endpoint endpoint' curvatureLedger
      curvatureLedger' compositionLedger compositionLedger' provenance provenance' : BHist}
    {probe : ProbeBundle ProbeName} {pkg : Pkg} :
    HolonomyTransportPacket bundle connection loop endpoint curvatureLedger compositionLedger
        provenance probe pkg ->
      hsame bundle bundle' -> hsame connection connection' -> hsame loop loop' ->
        hsame endpoint endpoint' -> hsame curvatureLedger curvatureLedger' ->
          hsame compositionLedger compositionLedger' -> hsame provenance provenance' ->
            PkgSig probe provenance' pkg ->
              HolonomyTransportPacket bundle' connection' loop' endpoint' curvatureLedger'
                  compositionLedger' provenance' probe pkg ∧
                hsame endpoint endpoint' := by
  intro packet sameBundle sameConnection sameLoop sameEndpoint sameCurvatureLedger
    sameCompositionLedger sameProvenance pkgSig'
  have bundleUnary' : UnaryHistory bundle' :=
    unary_transport packet.left sameBundle
  have connectionUnary' : UnaryHistory connection' :=
    unary_transport packet.right.left sameConnection
  have loopUnary' : UnaryHistory loop' :=
    unary_transport packet.right.right.left sameLoop
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_transport packet.right.right.right.left sameEndpoint
  have curvatureLedgerUnary' : UnaryHistory curvatureLedger' :=
    unary_transport packet.right.right.right.right.left sameCurvatureLedger
  have compositionLedgerUnary' : UnaryHistory compositionLedger' :=
    unary_transport packet.right.right.right.right.right.left sameCompositionLedger
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport packet.right.right.right.right.right.right.left sameProvenance
  have endpointRow' : Cont connection' loop' endpoint' :=
    cont_hsame_transport sameConnection sameLoop sameEndpoint
      packet.right.right.right.right.right.right.right.left
  have compositionRow' : Cont endpoint' curvatureLedger' compositionLedger' :=
    cont_hsame_transport sameEndpoint sameCurvatureLedger sameCompositionLedger
      packet.right.right.right.right.right.right.right.right.left
  exact
    And.intro
      (And.intro bundleUnary'
        (And.intro connectionUnary'
          (And.intro loopUnary'
            (And.intro endpointUnary'
              (And.intro curvatureLedgerUnary'
                (And.intro compositionLedgerUnary'
                  (And.intro provenanceUnary'
                    (And.intro endpointRow'
                      (And.intro compositionRow' pkgSig')))))))))
      sameEndpoint

theorem HolonomyTransportPacket_namecert_obligation_surface [AskSetup] [PackageSetup]
    {bundle connection loop endpoint curvatureLedger compositionLedger provenance : BHist}
    {probe : ProbeBundle ProbeName} {pkg : Pkg} :
    HolonomyTransportPacket bundle connection loop endpoint curvatureLedger compositionLedger
        provenance probe pkg ->
      SemanticNameCert
          (fun row : BHist =>
            exists e : BHist,
              HolonomyTransportPacket bundle connection loop e curvatureLedger compositionLedger
                provenance probe pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              HolonomyTransportPacket bundle connection loop e curvatureLedger compositionLedger
                provenance probe pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              HolonomyTransportPacket bundle connection loop e curvatureLedger compositionLedger
                provenance probe pkg ∧ hsame row e)
          hsame ∧
        Cont connection loop endpoint ∧ Cont endpoint curvatureLedger compositionLedger ∧
          PkgSig probe provenance pkg := by
  intro packet
  have endpointSource :
      (fun row : BHist =>
        exists e : BHist,
          HolonomyTransportPacket bundle connection loop e curvatureLedger compositionLedger
            provenance probe pkg ∧ hsame row e) endpoint :=
    Exists.intro endpoint (And.intro packet (hsame_refl endpoint))
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            exists e : BHist,
              HolonomyTransportPacket bundle connection loop e curvatureLedger compositionLedger
                provenance probe pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              HolonomyTransportPacket bundle connection loop e curvatureLedger compositionLedger
                provenance probe pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              HolonomyTransportPacket bundle connection loop e curvatureLedger compositionLedger
                provenance probe pkg ∧ hsame row e)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint endpointSource
      equiv_refl := by
        intro row _carrier
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameRow sameRow'
        exact hsame_trans sameRow sameRow'
      carrier_respects_equiv := by
        intro row row' sameRows carrierRow
        cases carrierRow with
        | intro e endpointWitness =>
            exact Exists.intro e
              (And.intro endpointWitness.left
                (hsame_trans (hsame_symm sameRows) endpointWitness.right))
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }
  exact And.intro cert
    (And.intro packet.right.right.right.right.right.right.right.left
      (And.intro packet.right.right.right.right.right.right.right.right.left
        packet.right.right.right.right.right.right.right.right.right))

end BEDC.Derived.HolonomyUp
