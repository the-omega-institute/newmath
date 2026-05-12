import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
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
open BEDC.FKernel.NameCert
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

def CauchyCriterionNameCertCarrier [AskSetup] [PackageSetup]
    (window modulus tail tolerance sealRow transportRow route provenance localCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  Cont window modulus tail ∧
    Cont tail tolerance transportRow ∧
      Cont transportRow route provenance ∧
        Cont provenance localCert sealRow ∧
          PkgSig bundle provenance pkg ∧ hsame sealRow tail ∧ hsame sealRow provenance

theorem CauchyCriterionCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {window modulus tail tolerance sealRow transportRow route provenance localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCriterionNameCertCarrier window modulus tail tolerance sealRow transportRow route
        provenance localCert bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          CauchyCriterionNameCertCarrier window modulus tail tolerance sealRow transportRow route
            provenance localCert bundle pkg ∧ hsame row sealRow)
        (fun row : BHist =>
          CauchyCriterionNameCertCarrier window modulus tail tolerance sealRow transportRow route
            provenance localCert bundle pkg ∧ hsame row tail)
        (fun row : BHist =>
          CauchyCriterionNameCertCarrier window modulus tail tolerance sealRow transportRow route
            provenance localCert bundle pkg ∧ hsame row provenance)
        hsame := by
  intro carrier
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro sealRow (And.intro carrier (hsame_refl sealRow))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact And.intro source.left
        (hsame_trans source.right source.left.right.right.right.right.right.left)
    ledger_sound := by
      intro _row source
      exact And.intro source.left
        (hsame_trans source.right source.left.right.right.right.right.right.right)
  }

end BEDC.Derived.CauchyCriterionUp
