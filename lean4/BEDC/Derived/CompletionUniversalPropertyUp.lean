import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CompletionUniversalPropertyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CompletionUniversalPropertyPacket [AskSetup] [PackageSetup]
    (completion diagonal regular realSeal denseMap extensionLedger uniquenessLedger provenance
      nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory completion ∧ UnaryHistory diagonal ∧ UnaryHistory regular ∧
    UnaryHistory realSeal ∧ UnaryHistory nameRow ∧
      Cont completion diagonal extensionLedger ∧ Cont regular realSeal denseMap ∧
        Cont extensionLedger uniquenessLedger provenance ∧ PkgSig bundle provenance pkg

theorem CompletionUniversalPropertyPacket_namecert_obligations [AskSetup] [PackageSetup]
    {completion diagonal regular realSeal denseMap extensionLedger uniquenessLedger provenance
      nameRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompletionUniversalPropertyPacket completion diagonal regular realSeal denseMap
        extensionLedger uniquenessLedger provenance nameRow bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            hsame row nameRow ∧
              CompletionUniversalPropertyPacket completion diagonal regular realSeal denseMap
                extensionLedger uniquenessLedger provenance nameRow bundle pkg)
          (fun row : BHist => hsame row nameRow)
          (fun row : BHist => hsame row nameRow ∧ PkgSig bundle provenance pkg)
          hsame ∧
        UnaryHistory completion ∧ UnaryHistory diagonal ∧ UnaryHistory regular ∧
          UnaryHistory realSeal ∧ UnaryHistory nameRow ∧ PkgSig bundle provenance pkg := by
  intro packet
  have packetWitness := packet
  obtain ⟨completionUnary, diagonalUnary, regularUnary, realSealUnary, nameRowUnary,
    _extensionRoute, _denseRoute, _provenanceRoute, provenancePkg⟩ := packet
  have sourceNameRow :
      (fun row : BHist =>
        hsame row nameRow ∧
          CompletionUniversalPropertyPacket completion diagonal regular realSeal denseMap
            extensionLedger uniquenessLedger provenance nameRow bundle pkg) nameRow := by
    exact ⟨hsame_refl nameRow, packetWitness⟩
  have core :
      NameCert
        (fun row : BHist =>
          hsame row nameRow ∧
            CompletionUniversalPropertyPacket completion diagonal regular realSeal denseMap
              extensionLedger uniquenessLedger provenance nameRow bundle pkg)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro nameRow sourceNameRow
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _other _third sameRO sameOT
        exact hsame_trans sameRO sameOT
      carrier_respects_equiv := by
        intro _row _other same source
        exact ⟨hsame_trans (hsame_symm same) source.left, source.right⟩
    }
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row nameRow ∧
              CompletionUniversalPropertyPacket completion diagonal regular realSeal denseMap
                extensionLedger uniquenessLedger provenance nameRow bundle pkg)
          (fun row : BHist => hsame row nameRow)
          (fun row : BHist => hsame row nameRow ∧ PkgSig bundle provenance pkg)
          hsame := by
    exact {
      core := core
      pattern_sound := by
        intro _row source
        exact source.left
      ledger_sound := by
        intro _row source
        exact ⟨source.left, provenancePkg⟩
    }
  exact
    ⟨cert, completionUnary, diagonalUnary, regularUnary, realSealUnary, nameRowUnary,
      provenancePkg⟩

theorem CompletionUniversalPropertyPacket_extension_obligations [AskSetup] [PackageSetup]
    {completion diagonal regular realSeal denseMap extensionLedger uniquenessLedger provenance
      nameRow exportRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompletionUniversalPropertyPacket completion diagonal regular realSeal denseMap
        extensionLedger uniquenessLedger provenance nameRow bundle pkg ->
      Cont extensionLedger nameRow exportRow ->
        PkgSig bundle exportRow pkg ->
          UnaryHistory completion ∧ UnaryHistory diagonal ∧ UnaryHistory regular ∧
            UnaryHistory realSeal ∧ UnaryHistory denseMap ∧ UnaryHistory extensionLedger ∧
              UnaryHistory exportRow ∧ Cont completion diagonal extensionLedger ∧
                Cont regular realSeal denseMap ∧ Cont extensionLedger nameRow exportRow ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle exportRow pkg := by
  intro packet exportRoute exportPkg
  obtain ⟨completionUnary, diagonalUnary, regularUnary, realSealUnary, nameRowUnary,
    extensionRoute, denseRoute, _provenanceRoute, provenancePkg⟩ := packet
  have extensionUnary : UnaryHistory extensionLedger :=
    unary_cont_closed completionUnary diagonalUnary extensionRoute
  have denseUnary : UnaryHistory denseMap :=
    unary_cont_closed regularUnary realSealUnary denseRoute
  have exportUnary : UnaryHistory exportRow :=
    unary_cont_closed extensionUnary nameRowUnary exportRoute
  exact
    ⟨completionUnary, diagonalUnary, regularUnary, realSealUnary, denseUnary,
      extensionUnary, exportUnary, extensionRoute, denseRoute, exportRoute, provenancePkg,
      exportPkg⟩

theorem CompletionUniversalPropertyPacket_uniqueness_ledger [AskSetup] [PackageSetup]
    {completion diagonal regular realSeal denseMap extensionLedger uniquenessLedger provenance
      nameRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompletionUniversalPropertyPacket completion diagonal regular realSeal denseMap
        extensionLedger uniquenessLedger provenance nameRow bundle pkg ->
      Cont extensionLedger nameRow uniquenessLedger ->
        UnaryHistory extensionLedger ∧ UnaryHistory uniquenessLedger ∧ UnaryHistory provenance ∧
          Cont extensionLedger nameRow uniquenessLedger ∧
            Cont extensionLedger uniquenessLedger provenance ∧ PkgSig bundle provenance pkg := by
  intro packet uniquenessRoute
  obtain ⟨completionUnary, diagonalUnary, _regularUnary, _realSealUnary, nameRowUnary,
    extensionRoute, _denseRoute, provenanceRoute, provenancePkg⟩ := packet
  have extensionUnary : UnaryHistory extensionLedger :=
    unary_cont_closed completionUnary diagonalUnary extensionRoute
  have uniquenessUnary : UnaryHistory uniquenessLedger :=
    unary_cont_closed extensionUnary nameRowUnary uniquenessRoute
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed extensionUnary uniquenessUnary provenanceRoute
  exact
    ⟨extensionUnary, uniquenessUnary, provenanceUnary, uniquenessRoute, provenanceRoute,
      provenancePkg⟩

theorem CompletionUniversalPropertyPacket_classifier_transport [AskSetup] [PackageSetup]
    {completion diagonal regular realSeal denseMap extensionLedger uniquenessLedger provenance
      nameRow completion' diagonal' regular' realSeal' denseMap' extensionLedger'
      uniquenessLedger' provenance' nameRow' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompletionUniversalPropertyPacket completion diagonal regular realSeal denseMap
        extensionLedger uniquenessLedger provenance nameRow bundle pkg ->
      hsame completion completion' ->
        hsame diagonal diagonal' ->
          hsame regular regular' ->
            hsame realSeal realSeal' ->
              hsame nameRow nameRow' ->
                hsame uniquenessLedger uniquenessLedger' ->
                  Cont completion' diagonal' extensionLedger' ->
                    Cont regular' realSeal' denseMap' ->
                      Cont extensionLedger' uniquenessLedger' provenance' ->
                        PkgSig bundle provenance' pkg ->
                          CompletionUniversalPropertyPacket completion' diagonal' regular'
                              realSeal' denseMap' extensionLedger' uniquenessLedger'
                              provenance' nameRow' bundle pkg ∧
                            hsame extensionLedger extensionLedger' ∧
                              hsame denseMap denseMap' ∧ hsame provenance provenance' := by
  intro packet sameCompletion sameDiagonal sameRegular sameRealSeal sameName sameUniqueness
    extensionRoute' denseRoute' provenanceRoute' provenancePkg'
  obtain ⟨completionUnary, diagonalUnary, regularUnary, realSealUnary, nameRowUnary,
    extensionRoute, denseRoute, provenanceRoute, _provenancePkg⟩ := packet
  have sameExtension : hsame extensionLedger extensionLedger' :=
    cont_respects_hsame sameCompletion sameDiagonal extensionRoute extensionRoute'
  have sameDense : hsame denseMap denseMap' :=
    cont_respects_hsame sameRegular sameRealSeal denseRoute denseRoute'
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameExtension sameUniqueness provenanceRoute provenanceRoute'
  have completionUnary' : UnaryHistory completion' :=
    unary_transport completionUnary sameCompletion
  have diagonalUnary' : UnaryHistory diagonal' :=
    unary_transport diagonalUnary sameDiagonal
  have regularUnary' : UnaryHistory regular' :=
    unary_transport regularUnary sameRegular
  have realSealUnary' : UnaryHistory realSeal' :=
    unary_transport realSealUnary sameRealSeal
  have nameRowUnary' : UnaryHistory nameRow' :=
    unary_transport nameRowUnary sameName
  exact
    ⟨⟨completionUnary', diagonalUnary', regularUnary', realSealUnary', nameRowUnary',
        extensionRoute', denseRoute', provenanceRoute', provenancePkg'⟩,
      sameExtension, sameDense, sameProvenance⟩

end BEDC.Derived.CompletionUniversalPropertyUp
