import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Sig
import BEDC.FKernel.Unary

namespace BEDC.Derived.ObserverHistoryIdentityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

def ObserverHistoryIdentityPacket [AskSetup] [PackageSetup]
    (leftHistory rightHistory signatures samenessRows ledger routes provenance nameCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory leftHistory ∧ UnaryHistory rightHistory ∧ UnaryHistory signatures ∧
    UnaryHistory samenessRows ∧ UnaryHistory ledger ∧ UnaryHistory routes ∧
      UnaryHistory provenance ∧ UnaryHistory nameCert ∧
        SameSig bundle leftHistory rightHistory ∧ Cont ledger routes samenessRows ∧
          PkgSig bundle provenance pkg ∧ PkgSig bundle signatures pkg

theorem ObserverHistoryIdentityPacket_namecert_obligations [AskSetup] [PackageSetup]
    {leftHistory rightHistory signatures samenessRows ledger routes provenance nameCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObserverHistoryIdentityPacket leftHistory rightHistory signatures samenessRows ledger routes
        provenance nameCert bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            ObserverHistoryIdentityPacket leftHistory rightHistory signatures samenessRows ledger
              routes provenance row bundle pkg)
          (fun row : BHist =>
            UnaryHistory row ∧ SameSig bundle leftHistory rightHistory ∧
              PkgSig bundle signatures pkg)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont ledger routes samenessRows ∧
              PkgSig bundle provenance pkg)
          hsame ∧
        SameSig bundle leftHistory rightHistory ∧ Cont ledger routes samenessRows ∧
          PkgSig bundle provenance pkg := by
  intro packet
  have packetWitness := packet
  obtain ⟨leftUnary, rightUnary, signaturesUnary, samenessRowsUnary, ledgerUnary, routesUnary,
    provenanceUnary, nameCertUnary, sameRows, ledgerRoutes, provenancePkg, signaturesPkg⟩ :=
      packet
  have sourceWitness :
      (fun row : BHist =>
        ObserverHistoryIdentityPacket leftHistory rightHistory signatures samenessRows ledger routes
          provenance row bundle pkg) nameCert := by
    exact packetWitness
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ObserverHistoryIdentityPacket leftHistory rightHistory signatures samenessRows ledger
              routes provenance row bundle pkg)
          (fun row : BHist =>
            UnaryHistory row ∧ SameSig bundle leftHistory rightHistory ∧
              PkgSig bundle signatures pkg)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont ledger routes samenessRows ∧
              PkgSig bundle provenance pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro nameCert sourceWitness
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _row' same
          exact hsame_symm same
        equiv_trans := by
          intro _row _row' _row'' sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro row row' same sourceRow
          obtain ⟨sourceLeftUnary, sourceRightUnary, sourceSignaturesUnary,
            sourceSamenessRowsUnary, sourceLedgerUnary, sourceRoutesUnary,
            sourceProvenanceUnary, sourceNameCertUnary, sourceSameRows, sourceLedgerRoutes,
            sourceProvenancePkg, sourceSignaturesPkg⟩ := sourceRow
          exact
            ⟨sourceLeftUnary, sourceRightUnary, sourceSignaturesUnary,
              sourceSamenessRowsUnary, sourceLedgerUnary, sourceRoutesUnary,
              sourceProvenanceUnary, unary_transport sourceNameCertUnary same, sourceSameRows,
              sourceLedgerRoutes, sourceProvenancePkg, sourceSignaturesPkg⟩
      }
      pattern_sound := by
        intro row sourceRow
        obtain ⟨_sourceLeftUnary, _sourceRightUnary, _sourceSignaturesUnary,
          _sourceSamenessRowsUnary, _sourceLedgerUnary, _sourceRoutesUnary,
          _sourceProvenanceUnary, sourceNameCertUnary, sourceSameRows, _sourceLedgerRoutes,
          _sourceProvenancePkg, sourceSignaturesPkg⟩ := sourceRow
        exact ⟨sourceNameCertUnary, sourceSameRows, sourceSignaturesPkg⟩
      ledger_sound := by
        intro row sourceRow
        obtain ⟨_sourceLeftUnary, _sourceRightUnary, _sourceSignaturesUnary,
          _sourceSamenessRowsUnary, _sourceLedgerUnary, _sourceRoutesUnary,
          _sourceProvenanceUnary, sourceNameCertUnary, _sourceSameRows, sourceLedgerRoutes,
          sourceProvenancePkg, _sourceSignaturesPkg⟩ := sourceRow
        exact ⟨sourceNameCertUnary, sourceLedgerRoutes, sourceProvenancePkg⟩
    }
  exact ⟨cert, sameRows, ledgerRoutes, provenancePkg⟩

theorem ObserverHistoryIdentityPacket_non_escape_boundary [AskSetup] [PackageSetup]
    {leftHistory rightHistory signatures samenessRows ledger routes provenance nameCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObserverHistoryIdentityPacket leftHistory rightHistory signatures samenessRows ledger routes
        provenance nameCert bundle pkg ->
      UnaryHistory leftHistory ∧ UnaryHistory rightHistory ∧ UnaryHistory signatures ∧
        UnaryHistory samenessRows ∧ UnaryHistory ledger ∧ UnaryHistory routes ∧
          UnaryHistory provenance ∧ UnaryHistory nameCert ∧
            SameSig bundle leftHistory rightHistory ∧ Cont ledger routes samenessRows ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle signatures pkg ∧
                SemanticNameCert
                    (fun row : BHist =>
                      ObserverHistoryIdentityPacket leftHistory rightHistory signatures
                        samenessRows ledger routes provenance row bundle pkg)
                    (fun row : BHist =>
                      UnaryHistory row ∧ SameSig bundle leftHistory rightHistory ∧
                        PkgSig bundle signatures pkg)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont ledger routes samenessRows ∧
                        PkgSig bundle provenance pkg)
                    hsame := by
  intro packet
  have packetWitness := packet
  obtain ⟨leftUnary, rightUnary, signaturesUnary, samenessRowsUnary, ledgerUnary, routesUnary,
    provenanceUnary, nameCertUnary, sameRows, ledgerRoutes, provenancePkg, signaturesPkg⟩ :=
      packet
  have obligations :=
    ObserverHistoryIdentityPacket_namecert_obligations
      (leftHistory := leftHistory) (rightHistory := rightHistory) (signatures := signatures)
      (samenessRows := samenessRows) (ledger := ledger) (routes := routes)
      (provenance := provenance) (nameCert := nameCert) (bundle := bundle) (pkg := pkg)
      packetWitness
  obtain ⟨cert, _sameRows, _ledgerRoutes, _provenancePkg⟩ := obligations
  exact
    ⟨leftUnary, rightUnary, signaturesUnary, samenessRowsUnary, ledgerUnary, routesUnary,
      provenanceUnary, nameCertUnary, sameRows, ledgerRoutes, provenancePkg, signaturesPkg, cert⟩

theorem ObserverHistoryIdentityPacket_classifier_stability [AskSetup] [PackageSetup]
    {leftHistory rightHistory signatures samenessRows ledger routes provenance nameCert
      signatures' samenessRows' ledger' routes' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObserverHistoryIdentityPacket leftHistory rightHistory signatures samenessRows ledger routes
        provenance nameCert bundle pkg ->
      hsame signatures signatures' ->
        hsame samenessRows samenessRows' ->
          hsame ledger ledger' ->
            hsame routes routes' ->
              SameSig bundle leftHistory rightHistory ->
                Cont ledger' routes' samenessRows' ->
                  PkgSig bundle signatures' pkg ->
                    ObserverHistoryIdentityPacket leftHistory rightHistory signatures'
                        samenessRows' ledger' routes' provenance nameCert bundle pkg /\
                      hsame signatures signatures' /\ hsame samenessRows samenessRows' := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro packet sameSignatures sameSamenessRows sameLedger sameRoutes sameRows'
    ledgerRoutes' signaturesPkg'
  obtain ⟨leftUnary, rightUnary, signaturesUnary, samenessRowsUnary, ledgerUnary, routesUnary,
    provenanceUnary, nameCertUnary, _sameRows, _ledgerRoutes, provenancePkg,
    _signaturesPkg⟩ := packet
  have signaturesUnary' : UnaryHistory signatures' :=
    unary_transport signaturesUnary sameSignatures
  have samenessRowsUnary' : UnaryHistory samenessRows' :=
    unary_transport samenessRowsUnary sameSamenessRows
  have ledgerUnary' : UnaryHistory ledger' :=
    unary_transport ledgerUnary sameLedger
  have routesUnary' : UnaryHistory routes' :=
    unary_transport routesUnary sameRoutes
  have transported :
      ObserverHistoryIdentityPacket leftHistory rightHistory signatures' samenessRows' ledger'
        routes' provenance nameCert bundle pkg :=
    ⟨leftUnary, rightUnary, signaturesUnary', samenessRowsUnary', ledgerUnary', routesUnary',
      provenanceUnary, nameCertUnary, sameRows', ledgerRoutes', provenancePkg,
      signaturesPkg'⟩
  exact ⟨transported, sameSignatures, sameSamenessRows⟩

end BEDC.Derived.ObserverHistoryIdentityUp
