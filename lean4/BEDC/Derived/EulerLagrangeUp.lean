import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.EulerLagrangeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def EulerLagrangePacket [AskSetup] [PackageSetup]
    (action variation firstVariation boundary pde scalar route transport provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory action ∧ UnaryHistory variation ∧ UnaryHistory firstVariation ∧
    UnaryHistory boundary ∧ UnaryHistory pde ∧ UnaryHistory scalar ∧ UnaryHistory route ∧
      UnaryHistory transport ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
        Cont action variation firstVariation ∧ Cont firstVariation boundary pde ∧
          Cont pde scalar route ∧ Cont route transport name ∧ PkgSig bundle name pkg

theorem EulerLagrangePacket_semantic_name_certificate [AskSetup] [PackageSetup]
    {action variation firstVariation boundary pde scalar route transport provenance name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EulerLagrangePacket action variation firstVariation boundary pde scalar route transport
        provenance name bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          EulerLagrangePacket action variation firstVariation boundary pde scalar route transport
              provenance name bundle pkg ∧ hsame row name)
        (fun row : BHist =>
          EulerLagrangePacket action variation firstVariation boundary pde scalar route transport
              provenance name bundle pkg ∧ hsame row name)
        (fun row : BHist =>
          EulerLagrangePacket action variation firstVariation boundary pde scalar route transport
              provenance name bundle pkg ∧ hsame row name)
        hsame := by
  intro packet
  exact {
    core := {
      carrier_inhabited := Exists.intro name ⟨packet, hsame_refl name⟩
      equiv_refl := by
        intro row _carrier
        exact hsame_refl row
      equiv_symm := by
        intro row row' same
        exact hsame_symm same
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' same carrier
        exact ⟨carrier.left, hsame_trans (hsame_symm same) carrier.right⟩
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

theorem EulerLagrangePacket_scoped_dependency_certificate [AskSetup] [PackageSetup]
    {action variation firstVariation boundary pde scalar route transport provenance name action'
      variation' firstVariation' boundary' pde' scalar' route' transport' provenance' name' :
        BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EulerLagrangePacket action variation firstVariation boundary pde scalar route transport
        provenance name bundle pkg ->
      hsame action action' ->
        hsame variation variation' ->
          hsame boundary boundary' ->
            hsame scalar scalar' ->
              hsame transport transport' ->
                hsame provenance provenance' ->
                  Cont action' variation' firstVariation' ->
                    Cont firstVariation' boundary' pde' ->
                      Cont pde' scalar' route' ->
                        Cont route' transport' name' ->
                          PkgSig bundle name' pkg ->
                            EulerLagrangePacket action' variation' firstVariation' boundary'
                                pde' scalar' route' transport' provenance' name' bundle pkg ∧
                              SemanticNameCert
                                (fun row : BHist =>
                                  EulerLagrangePacket action' variation' firstVariation'
                                      boundary' pde' scalar' route' transport' provenance' name'
                                      bundle pkg ∧
                                    hsame row name')
                                (fun row : BHist =>
                                  EulerLagrangePacket action' variation' firstVariation'
                                      boundary' pde' scalar' route' transport' provenance' name'
                                      bundle pkg ∧
                                    hsame row name')
                                (fun row : BHist =>
                                  EulerLagrangePacket action' variation' firstVariation'
                                      boundary' pde' scalar' route' transport' provenance' name'
                                      bundle pkg ∧
                                    hsame row name')
                                hsame ∧
                                hsame firstVariation firstVariation' ∧ hsame pde pde' ∧
                                  hsame route route' ∧ hsame name name' := by
  intro packet sameAction sameVariation sameBoundary sameScalar sameTransport sameProvenance
    actionVariationFirstVariation' firstVariationBoundaryPde' pdeScalarRoute'
    routeTransportName' packageName'
  have actionUnary' : UnaryHistory action' :=
    unary_transport packet.left sameAction
  have variationUnary' : UnaryHistory variation' :=
    unary_transport packet.right.left sameVariation
  have boundaryUnary' : UnaryHistory boundary' :=
    unary_transport packet.right.right.right.left sameBoundary
  have scalarUnary' : UnaryHistory scalar' :=
    unary_transport packet.right.right.right.right.right.left sameScalar
  have transportUnary' : UnaryHistory transport' :=
    unary_transport packet.right.right.right.right.right.right.right.left sameTransport
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport packet.right.right.right.right.right.right.right.right.left sameProvenance
  have actionVariationFirstVariation : Cont action variation firstVariation :=
    packet.right.right.right.right.right.right.right.right.right.right.left
  have firstVariationBoundaryPde : Cont firstVariation boundary pde :=
    packet.right.right.right.right.right.right.right.right.right.right.right.left
  have pdeScalarRoute : Cont pde scalar route :=
    packet.right.right.right.right.right.right.right.right.right.right.right.right.left
  have routeTransportName : Cont route transport name :=
    packet.right.right.right.right.right.right.right.right.right.right.right.right.right.left
  have sameFirstVariation : hsame firstVariation firstVariation' :=
    cont_respects_hsame sameAction sameVariation actionVariationFirstVariation
      actionVariationFirstVariation'
  have samePde : hsame pde pde' :=
    cont_respects_hsame sameFirstVariation sameBoundary firstVariationBoundaryPde
      firstVariationBoundaryPde'
  have sameRoute : hsame route route' :=
    cont_respects_hsame samePde sameScalar pdeScalarRoute pdeScalarRoute'
  have sameName : hsame name name' :=
    cont_respects_hsame sameRoute sameTransport routeTransportName routeTransportName'
  have firstVariationUnary' : UnaryHistory firstVariation' :=
    unary_cont_closed actionUnary' variationUnary' actionVariationFirstVariation'
  have pdeUnary' : UnaryHistory pde' :=
    unary_cont_closed firstVariationUnary' boundaryUnary' firstVariationBoundaryPde'
  have routeUnary' : UnaryHistory route' :=
    unary_cont_closed pdeUnary' scalarUnary' pdeScalarRoute'
  have nameUnary' : UnaryHistory name' :=
    unary_cont_closed routeUnary' transportUnary' routeTransportName'
  have transported :
      EulerLagrangePacket action' variation' firstVariation' boundary' pde' scalar' route'
        transport' provenance' name' bundle pkg :=
    ⟨actionUnary', variationUnary', firstVariationUnary', boundaryUnary', pdeUnary',
      scalarUnary', routeUnary', transportUnary', provenanceUnary', nameUnary',
      actionVariationFirstVariation', firstVariationBoundaryPde', pdeScalarRoute',
      routeTransportName', packageName'⟩
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          EulerLagrangePacket action' variation' firstVariation' boundary' pde' scalar' route'
              transport' provenance' name' bundle pkg ∧
            hsame row name')
        (fun row : BHist =>
          EulerLagrangePacket action' variation' firstVariation' boundary' pde' scalar' route'
              transport' provenance' name' bundle pkg ∧
            hsame row name')
        (fun row : BHist =>
          EulerLagrangePacket action' variation' firstVariation' boundary' pde' scalar' route'
              transport' provenance' name' bundle pkg ∧
            hsame row name')
        hsame :=
    EulerLagrangePacket_semantic_name_certificate transported
  exact ⟨transported, cert, sameFirstVariation, samePde, sameRoute, sameName⟩

end BEDC.Derived.EulerLagrangeUp
