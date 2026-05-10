import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RamseyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RamseyColouringCarrier [AskSetup] [PackageSetup]
    (vertex subset colour lookup provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory vertex ∧ UnaryHistory subset ∧ UnaryHistory colour ∧
    UnaryHistory provenance ∧ Cont vertex subset lookup ∧ Cont lookup colour endpoint ∧
      PkgSig bundle endpoint pkg

theorem RamseyColouringCarrier_monochrome_classifier_stability [AskSetup] [PackageSetup]
    {vertex subset colour lookup provenance endpoint vertex' subset' colour' lookup'
      provenance' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RamseyColouringCarrier vertex subset colour lookup provenance endpoint bundle pkg ->
      hsame vertex vertex' ->
        hsame subset subset' ->
          hsame colour colour' ->
            hsame provenance provenance' ->
              Cont vertex' subset' lookup' ->
                Cont lookup' colour' endpoint' ->
                  PkgSig bundle endpoint' pkg ->
                    RamseyColouringCarrier vertex' subset' colour' lookup' provenance'
                        endpoint' bundle pkg ∧ hsame lookup lookup' ∧
                      hsame endpoint endpoint' := by
  intro carrier sameVertex sameSubset sameColour sameProvenance lookupRoute'
    endpointRoute' endpointPkg'
  have vertexUnary : UnaryHistory vertex := carrier.left
  have subsetUnary : UnaryHistory subset := carrier.right.left
  have colourUnary : UnaryHistory colour := carrier.right.right.left
  have provenanceUnary : UnaryHistory provenance := carrier.right.right.right.left
  have lookupRoute : Cont vertex subset lookup := carrier.right.right.right.right.left
  have endpointRoute : Cont lookup colour endpoint := carrier.right.right.right.right.right.left
  have lookupSame : hsame lookup lookup' :=
    cont_respects_hsame sameVertex sameSubset lookupRoute lookupRoute'
  have endpointSame : hsame endpoint endpoint' :=
    cont_respects_hsame lookupSame sameColour endpointRoute endpointRoute'
  have transportedCarrier :
      RamseyColouringCarrier vertex' subset' colour' lookup' provenance' endpoint' bundle pkg :=
    And.intro (unary_transport vertexUnary sameVertex)
      (And.intro (unary_transport subsetUnary sameSubset)
        (And.intro (unary_transport colourUnary sameColour)
          (And.intro (unary_transport provenanceUnary sameProvenance)
            (And.intro lookupRoute' (And.intro endpointRoute' endpointPkg')))))
  exact And.intro transportedCarrier (And.intro lookupSame endpointSame)

theorem RamseyColouringCarrier_obligation_surface [AskSetup] [PackageSetup]
    {vertexSpine subsetSpine colorEndpoint lookupLedger provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory vertexSpine ->
      UnaryHistory subsetSpine ->
        UnaryHistory colorEndpoint ->
          Cont vertexSpine subsetSpine lookupLedger ->
            Cont lookupLedger colorEndpoint provenance ->
              Cont provenance colorEndpoint endpoint ->
                PkgSig bundle endpoint pkg ->
                  UnaryHistory lookupLedger ∧ UnaryHistory provenance ∧
                    UnaryHistory endpoint ∧ hsame lookupLedger (append vertexSpine subsetSpine) ∧
                      hsame provenance (append lookupLedger colorEndpoint) ∧
                        hsame endpoint (append provenance colorEndpoint) ∧
                          PkgSig bundle endpoint pkg := by
  intro vertexUnary subsetUnary colorUnary lookupRow provenanceRow endpointRow pkgSig
  have lookupUnary : UnaryHistory lookupLedger :=
    unary_cont_closed vertexUnary subsetUnary lookupRow
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed lookupUnary colorUnary provenanceRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed provenanceUnary colorUnary endpointRow
  exact
    ⟨lookupUnary,
      provenanceUnary,
      endpointUnary,
      lookupRow,
      provenanceRow,
      endpointRow,
      pkgSig⟩

end BEDC.Derived.RamseyUp
