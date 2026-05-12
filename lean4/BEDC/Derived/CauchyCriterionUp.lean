import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Sig
import BEDC.FKernel.Unary

/-!
# CauchyCriterionUp finite carrier surface.
-/

namespace BEDC.Derived.CauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

def CauchyCriterionCarrier [AskSetup] [PackageSetup]
    (window modulus tolerance ledger regseq realSeal transport route provenance localCert
      endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory window ∧ UnaryHistory modulus ∧ UnaryHistory tolerance ∧
    UnaryHistory ledger ∧ UnaryHistory regseq ∧ UnaryHistory realSeal ∧
      UnaryHistory transport ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
        UnaryHistory localCert ∧ UnaryHistory endpoint ∧
          Cont window modulus tolerance ∧ Cont tolerance ledger regseq ∧
            Cont regseq realSeal transport ∧ Cont transport localCert route ∧
              Cont route provenance endpoint ∧ PkgSig bundle endpoint pkg

theorem CauchyCriterionCarrier_modulus_threshold_stability [AskSetup] [PackageSetup]
    {window modulus tolerance ledger regseq realSeal transport route provenance localCert endpoint
      window' modulus' tolerance' ledger' regseq' realSeal' transport' route' provenance'
      localCert' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCriterionCarrier window modulus tolerance ledger regseq realSeal transport route
        provenance localCert endpoint bundle pkg ->
      hsame window window' ->
        hsame modulus modulus' ->
          hsame ledger ledger' ->
            hsame realSeal realSeal' ->
              hsame provenance provenance' ->
                hsame localCert localCert' ->
                  Cont window' modulus' tolerance' ->
                    Cont tolerance' ledger' regseq' ->
                      Cont regseq' realSeal' transport' ->
                        Cont transport' localCert' route' ->
                          Cont route' provenance' endpoint' ->
                            PkgSig bundle endpoint' pkg ->
                              CauchyCriterionCarrier window' modulus' tolerance' ledger' regseq'
                                  realSeal' transport' route' provenance' localCert' endpoint'
                                  bundle pkg ∧
                                hsame tolerance tolerance' ∧
                                  hsame regseq regseq' ∧
                                    hsame transport transport' ∧
                                      hsame route route' ∧ hsame endpoint endpoint' := by
  intro carrier sameWindow sameModulus sameLedger sameRealSeal sameProvenance sameLocalCert
    toleranceRow' regseqRow' transportRow' routeRow' endpointRow' pkgSig'
  rcases carrier with
    ⟨windowUnary, modulusUnary, _toleranceUnary, ledgerUnary, _regseqUnary, realSealUnary,
      _transportUnary, _routeUnary, provenanceUnary, localCertUnary, _endpointUnary,
      toleranceRow, regseqRow, transportRow, routeRow, endpointRow, _pkgSig⟩
  have windowUnary' : UnaryHistory window' :=
    unary_transport windowUnary sameWindow
  have modulusUnary' : UnaryHistory modulus' :=
    unary_transport modulusUnary sameModulus
  have ledgerUnary' : UnaryHistory ledger' :=
    unary_transport ledgerUnary sameLedger
  have realSealUnary' : UnaryHistory realSeal' :=
    unary_transport realSealUnary sameRealSeal
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary sameProvenance
  have localCertUnary' : UnaryHistory localCert' :=
    unary_transport localCertUnary sameLocalCert
  have toleranceUnary' : UnaryHistory tolerance' :=
    unary_cont_closed windowUnary' modulusUnary' toleranceRow'
  have regseqUnary' : UnaryHistory regseq' :=
    unary_cont_closed toleranceUnary' ledgerUnary' regseqRow'
  have transportUnary' : UnaryHistory transport' :=
    unary_cont_closed regseqUnary' realSealUnary' transportRow'
  have routeUnary' : UnaryHistory route' :=
    unary_cont_closed transportUnary' localCertUnary' routeRow'
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed routeUnary' provenanceUnary' endpointRow'
  have sameTolerance : hsame tolerance tolerance' :=
    cont_respects_hsame sameWindow sameModulus toleranceRow toleranceRow'
  have sameRegseq : hsame regseq regseq' :=
    cont_respects_hsame sameTolerance sameLedger regseqRow regseqRow'
  have sameTransport : hsame transport transport' :=
    cont_respects_hsame sameRegseq sameRealSeal transportRow transportRow'
  have sameRoute : hsame route route' :=
    cont_respects_hsame sameTransport sameLocalCert routeRow routeRow'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameRoute sameProvenance endpointRow endpointRow'
  have targetCarrier :
      CauchyCriterionCarrier window' modulus' tolerance' ledger' regseq' realSeal'
        transport' route' provenance' localCert' endpoint' bundle pkg :=
    ⟨windowUnary', modulusUnary', toleranceUnary', ledgerUnary', regseqUnary', realSealUnary',
      transportUnary', routeUnary', provenanceUnary', localCertUnary', endpointUnary',
      toleranceRow', regseqRow', transportRow', routeRow', endpointRow', pkgSig'⟩
  exact And.intro targetCarrier
    (And.intro sameTolerance
      (And.intro sameRegseq
        (And.intro sameTransport (And.intro sameRoute sameEndpoint))))

end BEDC.Derived.CauchyCriterionUp
