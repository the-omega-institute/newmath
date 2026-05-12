import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Sig
import BEDC.FKernel.Unary

/-!
# SqueezeRealUp finite carrier surface.
-/

namespace BEDC.Derived.SqueezeRealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

def SqueezeRealCarrier [AskSetup] [PackageSetup]
    (lower middle upper tolerance lowerLedger upperLedger realSeal transport provenance localCert
      endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory lower ∧ UnaryHistory middle ∧ UnaryHistory upper ∧
    UnaryHistory tolerance ∧ UnaryHistory lowerLedger ∧ UnaryHistory upperLedger ∧
      UnaryHistory realSeal ∧ UnaryHistory transport ∧ UnaryHistory provenance ∧
        UnaryHistory localCert ∧ UnaryHistory endpoint ∧
          Cont lower middle lowerLedger ∧ Cont middle upper upperLedger ∧
            Cont tolerance lowerLedger realSeal ∧ Cont upperLedger realSeal transport ∧
              Cont transport localCert endpoint ∧ PkgSig bundle endpoint pkg

theorem SqueezeRealCarrier_transport_stability [AskSetup] [PackageSetup]
    {lower middle upper tolerance lowerLedger upperLedger realSeal transport provenance localCert
      endpoint lower' middle' upper' tolerance' lowerLedger' upperLedger' realSeal' transport'
      localCert' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SqueezeRealCarrier lower middle upper tolerance lowerLedger upperLedger realSeal transport
        provenance localCert endpoint bundle pkg ->
      hsame lower lower' ->
        hsame middle middle' ->
          hsame upper upper' ->
            hsame tolerance tolerance' ->
              hsame realSeal realSeal' ->
                hsame localCert localCert' ->
                  Cont lower' middle' lowerLedger' ->
                    Cont middle' upper' upperLedger' ->
                      Cont tolerance' lowerLedger' realSeal' ->
                        Cont upperLedger' realSeal' transport' ->
                          Cont transport' localCert' endpoint' ->
                            PkgSig bundle endpoint' pkg ->
                              SqueezeRealCarrier lower' middle' upper' tolerance' lowerLedger'
                                  upperLedger' realSeal' transport' provenance localCert'
                                  endpoint' bundle pkg ∧
                                hsame lowerLedger lowerLedger' ∧
                                  hsame upperLedger upperLedger' ∧
                                    hsame transport transport' ∧ hsame endpoint endpoint' := by
  intro carrier sameLower sameMiddle sameUpper sameTolerance sameRealSeal sameLocalCert
    lowerLedgerRow' upperLedgerRow' realSealRow' transportRow' endpointRow' pkgSig'
  rcases carrier with
    ⟨lowerUnary, middleUnary, upperUnary, toleranceUnary, _lowerLedgerUnary,
      _upperLedgerUnary, _realSealUnary, _transportUnary, provenanceUnary, localCertUnary,
      _endpointUnary, lowerLedgerRow, upperLedgerRow, realSealRow, transportRow, endpointRow,
      _pkgSig⟩
  have lowerUnary' : UnaryHistory lower' :=
    unary_transport lowerUnary sameLower
  have middleUnary' : UnaryHistory middle' :=
    unary_transport middleUnary sameMiddle
  have upperUnary' : UnaryHistory upper' :=
    unary_transport upperUnary sameUpper
  have toleranceUnary' : UnaryHistory tolerance' :=
    unary_transport toleranceUnary sameTolerance
  have realSealUnary' : UnaryHistory realSeal' :=
    unary_transport _realSealUnary sameRealSeal
  have localCertUnary' : UnaryHistory localCert' :=
    unary_transport localCertUnary sameLocalCert
  have lowerLedgerUnary' : UnaryHistory lowerLedger' :=
    unary_cont_closed lowerUnary' middleUnary' lowerLedgerRow'
  have upperLedgerUnary' : UnaryHistory upperLedger' :=
    unary_cont_closed middleUnary' upperUnary' upperLedgerRow'
  have transportUnary' : UnaryHistory transport' :=
    unary_cont_closed upperLedgerUnary' realSealUnary' transportRow'
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed transportUnary' localCertUnary' endpointRow'
  have sameLowerLedger : hsame lowerLedger lowerLedger' :=
    cont_respects_hsame sameLower sameMiddle lowerLedgerRow lowerLedgerRow'
  have sameUpperLedger : hsame upperLedger upperLedger' :=
    cont_respects_hsame sameMiddle sameUpper upperLedgerRow upperLedgerRow'
  have sameTransport : hsame transport transport' :=
    cont_respects_hsame sameUpperLedger sameRealSeal transportRow transportRow'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameTransport sameLocalCert endpointRow endpointRow'
  have targetCarrier :
      SqueezeRealCarrier lower' middle' upper' tolerance' lowerLedger' upperLedger' realSeal'
        transport' provenance localCert' endpoint' bundle pkg :=
    ⟨lowerUnary', middleUnary', upperUnary', toleranceUnary', lowerLedgerUnary',
      upperLedgerUnary', realSealUnary', transportUnary', provenanceUnary, localCertUnary',
      endpointUnary', lowerLedgerRow', upperLedgerRow', realSealRow', transportRow',
      endpointRow', pkgSig'⟩
  exact And.intro targetCarrier
    (And.intro sameLowerLedger
      (And.intro sameUpperLedger (And.intro sameTransport sameEndpoint)))

end BEDC.Derived.SqueezeRealUp
