import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RealCauchyCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RealCauchyCompletionCarrier [AskSetup] [PackageSetup]
    (family modulus diagonal window readback dyadic «seal» provenance localCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory family ∧ UnaryHistory modulus ∧ UnaryHistory window ∧ UnaryHistory dyadic ∧
    UnaryHistory provenance ∧ Cont family modulus diagonal ∧ Cont diagonal window readback ∧
      Cont readback dyadic «seal» ∧ Cont «seal» localCert provenance ∧
        PkgSig bundle provenance pkg

theorem RealCauchyCompletionCarrier_transport_stability [AskSetup] [PackageSetup]
    {family modulus diagonal window readback dyadic «seal» provenance localCert
      family' modulus' diagonal' window' readback' dyadic' seal' provenance' localCert' :
        BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealCauchyCompletionCarrier family modulus diagonal window readback dyadic «seal»
        provenance localCert bundle pkg ->
      hsame family family' ->
        hsame modulus modulus' ->
          hsame window window' ->
            hsame dyadic dyadic' ->
              hsame localCert localCert' ->
                Cont family' modulus' diagonal' ->
                  Cont diagonal' window' readback' ->
                    Cont readback' dyadic' seal' ->
                      Cont seal' localCert' provenance' ->
                        PkgSig bundle provenance' pkg ->
                          RealCauchyCompletionCarrier family' modulus' diagonal' window'
                              readback' dyadic' seal' provenance' localCert' bundle pkg ∧
                            hsame diagonal diagonal' ∧ hsame readback readback' ∧
                              hsame «seal» seal' ∧ hsame provenance provenance' := by
  intro carrier sameFamily sameModulus sameWindow sameDyadic sameLocalCert
  intro familyModulusRow' diagonalWindowRow' readbackDyadicRow' sealLocalCertRow'
    provenancePkg'
  obtain ⟨familyUnary, modulusUnary, windowUnary, dyadicUnary, provenanceUnary,
    familyModulusRow, diagonalWindowRow, readbackDyadicRow, sealLocalCertRow, _provenancePkg⟩ :=
    carrier
  have sameDiagonal : hsame diagonal diagonal' :=
    cont_respects_hsame sameFamily sameModulus familyModulusRow familyModulusRow'
  have sameReadback : hsame readback readback' :=
    cont_respects_hsame sameDiagonal sameWindow diagonalWindowRow diagonalWindowRow'
  have sameSeal : hsame «seal» seal' :=
    cont_respects_hsame sameReadback sameDyadic readbackDyadicRow readbackDyadicRow'
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameSeal sameLocalCert sealLocalCertRow sealLocalCertRow'
  have familyUnary' : UnaryHistory family' :=
    unary_transport familyUnary sameFamily
  have modulusUnary' : UnaryHistory modulus' :=
    unary_transport modulusUnary sameModulus
  have windowUnary' : UnaryHistory window' :=
    unary_transport windowUnary sameWindow
  have dyadicUnary' : UnaryHistory dyadic' :=
    unary_transport dyadicUnary sameDyadic
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary sameProvenance
  exact
    ⟨⟨familyUnary', modulusUnary', windowUnary', dyadicUnary', provenanceUnary',
        familyModulusRow', diagonalWindowRow', readbackDyadicRow', sealLocalCertRow',
        provenancePkg'⟩,
      sameDiagonal, sameReadback, sameSeal, sameProvenance⟩

theorem RealCauchyCompletionCarrier_diagonal_handoff [AskSetup] [PackageSetup]
    {family modulus diagonal window readback dyadic «seal» provenance localCert
      consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealCauchyCompletionCarrier family modulus diagonal window readback dyadic «seal»
        provenance localCert bundle pkg ->
      UnaryHistory localCert ->
        Cont «seal» localCert consumerRead ->
          UnaryHistory diagonal ∧ UnaryHistory window ∧ UnaryHistory readback ∧
            UnaryHistory dyadic ∧ UnaryHistory «seal» ∧ UnaryHistory consumerRead ∧
              Cont family modulus diagonal ∧ Cont diagonal window readback ∧
                Cont readback dyadic «seal» ∧ PkgSig bundle provenance pkg := by
  intro carrier localCertUnary consumerRow
  obtain ⟨familyUnary, modulusUnary, windowUnary, dyadicUnary, _provenanceUnary,
    familyModulusRow, diagonalWindowRow, readbackDyadicRow, _provenanceRow, pkgSig⟩ :=
    carrier
  have diagonalUnary : UnaryHistory diagonal :=
    unary_cont_closed familyUnary modulusUnary familyModulusRow
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed diagonalUnary windowUnary diagonalWindowRow
  have sealUnary : UnaryHistory «seal» :=
    unary_cont_closed readbackUnary dyadicUnary readbackDyadicRow
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed sealUnary localCertUnary consumerRow
  exact ⟨diagonalUnary, windowUnary, readbackUnary, dyadicUnary, sealUnary, consumerUnary,
    familyModulusRow, diagonalWindowRow, readbackDyadicRow, pkgSig⟩

theorem RealCauchyCompletionCarrier_public_real_name_export [AskSetup] [PackageSetup]
    {regularFamily modulus diagonalPacket streamWindow regseqRead dyadicLedger realSeal
      provenance localCert publicExport : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory regularFamily ->
      UnaryHistory modulus ->
        UnaryHistory diagonalPacket ->
          UnaryHistory streamWindow ->
            UnaryHistory regseqRead ->
              UnaryHistory dyadicLedger ->
                UnaryHistory realSeal ->
                  Cont modulus diagonalPacket streamWindow ->
                    Cont streamWindow regseqRead dyadicLedger ->
                      Cont dyadicLedger realSeal publicExport ->
                        PkgSig bundle provenance pkg ->
                          PkgSig bundle localCert pkg ->
                            PkgSig bundle publicExport pkg ->
                              SemanticNameCert
                                (fun row : BHist =>
                                  hsame row publicExport ∧ UnaryHistory row ∧
                                    PkgSig bundle row pkg)
                                (fun row : BHist =>
                                  Cont dyadicLedger realSeal row ∧ PkgSig bundle row pkg)
                                (fun _row : BHist =>
                                  UnaryHistory regularFamily ∧ UnaryHistory modulus ∧
                                    UnaryHistory diagonalPacket ∧ UnaryHistory streamWindow ∧
                                      UnaryHistory regseqRead ∧ UnaryHistory dyadicLedger ∧
                                        UnaryHistory realSeal ∧
                                          PkgSig bundle provenance pkg ∧
                                            PkgSig bundle localCert pkg)
                                hsame := by
  intro regularFamilyUnary modulusUnary diagonalPacketUnary streamWindowUnary
  intro regseqReadUnary dyadicLedgerUnary realSealUnary
  intro _modulusDiagonalWindow _windowReadLedger ledgerSealExport
  intro provenancePkg localCertPkg publicExportPkg
  have publicExportUnary : UnaryHistory publicExport :=
    unary_cont_closed dyadicLedgerUnary realSealUnary ledgerSealExport
  have sourceExport :
      hsame publicExport publicExport ∧ UnaryHistory publicExport ∧
        PkgSig bundle publicExport pkg :=
    ⟨hsame_refl publicExport, publicExportUnary, publicExportPkg⟩
  exact {
    core := {
      carrier_inhabited := Exists.intro publicExport sourceExport
      equiv_refl := by
        intro row _sourceRow
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' classified
        exact hsame_symm classified
      equiv_trans := by
        intro _row _row' _row'' leftClassified rightClassified
        exact hsame_trans leftClassified rightClassified
      carrier_respects_equiv := by
        intro row row' classified sourceRow
        exact
          ⟨hsame_trans (hsame_symm classified) sourceRow.left,
            unary_transport sourceRow.right.left classified,
            by
              cases classified
              exact sourceRow.right.right⟩
    }
    pattern_sound := by
      intro row sourceRow
      cases sourceRow.left
      exact ⟨ledgerSealExport, sourceRow.right.right⟩
    ledger_sound := by
      intro _row _sourceRow
      exact
        ⟨regularFamilyUnary, modulusUnary, diagonalPacketUnary, streamWindowUnary,
          regseqReadUnary, dyadicLedgerUnary, realSealUnary, provenancePkg, localCertPkg⟩
  }

theorem RealCauchyCompletionCarrier_namecert_obligation_surface [AskSetup] [PackageSetup]
    {family modulus diagonal window readback dyadic sealRow provenance localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealCauchyCompletionCarrier family modulus diagonal window readback dyadic sealRow
        provenance localCert bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          hsame row provenance ∧
            RealCauchyCompletionCarrier family modulus diagonal window readback dyadic sealRow
              provenance localCert bundle pkg)
        (fun _row : BHist =>
          UnaryHistory family ∧ UnaryHistory modulus ∧ Cont family modulus diagonal ∧
            Cont diagonal window readback ∧ Cont readback dyadic sealRow)
        (fun row : BHist => PkgSig bundle provenance pkg ∧ UnaryHistory row)
        hsame := by
  intro carrier
  have carrierData :
      RealCauchyCompletionCarrier family modulus diagonal window readback dyadic sealRow
        provenance localCert bundle pkg :=
    carrier
  obtain ⟨familyUnary, modulusUnary, _windowUnary, _dyadicUnary, provenanceUnary,
    familyModulusRow, diagonalWindowRow, readbackDyadicRow, _sealLocalCertRow,
    provenancePkg⟩ := carrier
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro provenance ⟨hsame_refl provenance, carrierData⟩
      equiv_refl := by
        intro row _sourceRow
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameRow sameRow'
        exact hsame_trans sameRow sameRow'
      carrier_respects_equiv := by
        intro _row _row' sameRows sourceRow
        exact ⟨hsame_trans (hsame_symm sameRows) sourceRow.left, sourceRow.right⟩
    }
    pattern_sound := by
      intro _row _sourceRow
      exact
        ⟨familyUnary, modulusUnary, familyModulusRow, diagonalWindowRow,
          readbackDyadicRow⟩
    ledger_sound := by
      intro _row sourceRow
      exact ⟨provenancePkg, unary_transport provenanceUnary (hsame_symm sourceRow.left)⟩
  }

theorem RealCauchyCompletionCarrier_non_escape_boundary [AskSetup] [PackageSetup]
    {family modulus diagonal window readback dyadic «seal» provenance localCert consumer :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealCauchyCompletionCarrier family modulus diagonal window readback dyadic «seal»
        provenance localCert bundle pkg ->
      UnaryHistory localCert ->
        Cont «seal» localCert consumer ->
          UnaryHistory family ∧ UnaryHistory modulus ∧ UnaryHistory diagonal ∧
            UnaryHistory window ∧ UnaryHistory readback ∧ UnaryHistory dyadic ∧
              UnaryHistory «seal» ∧ UnaryHistory provenance ∧ UnaryHistory consumer ∧
                Cont family modulus diagonal ∧ Cont diagonal window readback ∧
                  Cont readback dyadic «seal» ∧ Cont «seal» localCert provenance ∧
                    Cont «seal» localCert consumer ∧ PkgSig bundle provenance pkg := by
  intro carrier localCertUnary sealLocalCertConsumer
  obtain ⟨familyUnary, modulusUnary, windowUnary, dyadicUnary, provenanceUnary,
    familyModulusRow, diagonalWindowRow, readbackDyadicRow, sealLocalCertProvenance,
    pkgSig⟩ := carrier
  have diagonalUnary : UnaryHistory diagonal :=
    unary_cont_closed familyUnary modulusUnary familyModulusRow
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed diagonalUnary windowUnary diagonalWindowRow
  have sealUnary : UnaryHistory «seal» :=
    unary_cont_closed readbackUnary dyadicUnary readbackDyadicRow
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed sealUnary localCertUnary sealLocalCertConsumer
  exact
    ⟨familyUnary, modulusUnary, diagonalUnary, windowUnary, readbackUnary, dyadicUnary,
      sealUnary, provenanceUnary, consumerUnary, familyModulusRow, diagonalWindowRow,
      readbackDyadicRow, sealLocalCertProvenance, sealLocalCertConsumer, pkgSig⟩

theorem RealCauchyCompletionCarrier_real_seal_readback_scope [AskSetup] [PackageSetup]
    {family modulus diagonal window readback dyadic «seal» provenance localCert consumerRead
      scopedSurface : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealCauchyCompletionCarrier family modulus diagonal window readback dyadic «seal»
        provenance localCert bundle pkg ->
      UnaryHistory localCert ->
        Cont «seal» localCert consumerRead ->
          Cont consumerRead provenance scopedSurface ->
            PkgSig bundle scopedSurface pkg ->
              UnaryHistory «seal» ∧ UnaryHistory consumerRead ∧
                UnaryHistory scopedSurface ∧ Cont readback dyadic «seal» ∧
                  Cont «seal» localCert consumerRead ∧
                    Cont consumerRead provenance scopedSurface ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle scopedSurface pkg := by
  intro carrier localCertUnary consumerRow scopedRow scopedPkg
  have handoff :=
    RealCauchyCompletionCarrier_diagonal_handoff carrier localCertUnary consumerRow
  obtain ⟨_familyUnary, _modulusUnary, _windowUnary, _dyadicUnary, provenanceUnary,
    _familyModulusRow, _diagonalWindowRow, _carrierReadbackRow, _carrierProvenanceRow,
    provenancePkg⟩ := carrier
  obtain ⟨_diagonalUnary, _handoffWindowUnary, _readbackUnary, _handoffDyadicUnary,
    sealUnary, consumerUnary, _handoffFamilyRow, _handoffDiagonalRow, readbackRow,
    _handoffPkg⟩ := handoff
  have scopedUnary : UnaryHistory scopedSurface :=
    unary_cont_closed consumerUnary provenanceUnary scopedRow
  exact ⟨sealUnary, consumerUnary, scopedUnary, readbackRow, consumerRow, scopedRow,
    provenancePkg, scopedPkg⟩

theorem RealCauchyCompletionCarrier_probe_bundle_window_coverage [AskSetup] [PackageSetup]
    {familyRow modulusRow diagonalPacket streamWindow regseqRead dyadicLedger realSeal
      consumerRead bundleSurface localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory familyRow ->
      UnaryHistory modulusRow ->
        UnaryHistory localCert ->
          Cont modulusRow familyRow diagonalPacket ->
            Cont diagonalPacket modulusRow streamWindow ->
              Cont streamWindow familyRow regseqRead ->
                Cont regseqRead streamWindow dyadicLedger ->
                  Cont dyadicLedger diagonalPacket realSeal ->
                    Cont realSeal dyadicLedger consumerRead ->
                      Cont consumerRead localCert bundleSurface ->
                        PkgSig bundle consumerRead pkg ->
                          PkgSig bundle bundleSurface pkg ->
                            UnaryHistory diagonalPacket ∧ UnaryHistory streamWindow ∧
                              UnaryHistory regseqRead ∧ UnaryHistory dyadicLedger ∧
                                UnaryHistory realSeal ∧ UnaryHistory consumerRead ∧
                                  UnaryHistory bundleSurface ∧
                                    SemanticNameCert
                                      (fun row : BHist =>
                                        hsame row bundleSurface ∧ UnaryHistory row ∧
                                          PkgSig bundle row pkg)
                                      (fun row : BHist =>
                                        hsame row bundleSurface ∧ UnaryHistory row)
                                      (fun row : BHist =>
                                        PkgSig bundle row pkg ∧ hsame row bundleSurface)
                                      (fun row row' : BHist => hsame row row') := by
  intro familyUnary modulusUnary localCertUnary modulusFamilyDiagonal
  intro diagonalModulusWindow streamFamilyRegseq regseqStreamDyadic
  intro dyadicDiagonalSeal sealDyadicConsumer consumerLocalSurface _consumerPkg surfacePkg
  have diagonalUnary : UnaryHistory diagonalPacket :=
    unary_cont_closed modulusUnary familyUnary modulusFamilyDiagonal
  have streamUnary : UnaryHistory streamWindow :=
    unary_cont_closed diagonalUnary modulusUnary diagonalModulusWindow
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed streamUnary familyUnary streamFamilyRegseq
  have dyadicUnary : UnaryHistory dyadicLedger :=
    unary_cont_closed regseqUnary streamUnary regseqStreamDyadic
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed dyadicUnary diagonalUnary dyadicDiagonalSeal
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed realSealUnary dyadicUnary sealDyadicConsumer
  have surfaceUnary : UnaryHistory bundleSurface :=
    unary_cont_closed consumerUnary localCertUnary consumerLocalSurface
  have semantic :
      SemanticNameCert
        (fun row : BHist => hsame row bundleSurface ∧ UnaryHistory row ∧
          PkgSig bundle row pkg)
        (fun row : BHist => hsame row bundleSurface ∧ UnaryHistory row)
        (fun row : BHist => PkgSig bundle row pkg ∧ hsame row bundleSurface)
        (fun row row' : BHist => hsame row row') := {
    core := {
      carrier_inhabited :=
        Exists.intro bundleSurface ⟨hsame_refl bundleSurface, surfaceUnary, surfacePkg⟩
      equiv_refl := by
        intro row _sourceRow
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' classified
        exact hsame_symm classified
      equiv_trans := by
        intro _row _row' _row'' leftClassified rightClassified
        exact hsame_trans leftClassified rightClassified
      carrier_respects_equiv := by
        intro _row _row' classified sourceRow
        cases classified
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, sourceRow.right.left⟩
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right.right, sourceRow.left⟩
  }
  exact
    ⟨diagonalUnary, streamUnary, regseqUnary, dyadicUnary, realSealUnary, consumerUnary,
      surfaceUnary, semantic⟩

theorem RealCauchyCompletionCarrier_regular_family_input_interface [AskSetup] [PackageSetup]
    {family modulus diagonal window readback dyadic sealRow provenance localCert
      selectedMember completionSurface : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealCauchyCompletionCarrier family modulus diagonal window readback dyadic sealRow
        provenance localCert bundle pkg ->
      UnaryHistory localCert ->
        Cont family modulus selectedMember ->
          Cont selectedMember window readback ->
            Cont sealRow localCert completionSurface ->
              PkgSig bundle completionSurface pkg ->
                UnaryHistory family ∧ UnaryHistory modulus ∧ UnaryHistory selectedMember ∧
                  UnaryHistory window ∧ UnaryHistory readback ∧ UnaryHistory sealRow ∧
                    UnaryHistory completionSurface ∧ Cont family modulus diagonal ∧
                      Cont family modulus selectedMember ∧
                        Cont selectedMember window readback ∧
                          Cont sealRow localCert completionSurface ∧
                            PkgSig bundle provenance pkg ∧
                              PkgSig bundle completionSurface pkg := by
  intro carrier localCertUnary selectedMemberRoute selectedReadbackRoute
    completionSurfaceRoute completionSurfacePkg
  obtain ⟨familyUnary, modulusUnary, windowUnary, dyadicUnary, _provenanceUnary,
    familyModulusDiagonal, _diagonalWindowReadback, readbackDyadicSeal,
    _sealLocalCertProvenance, provenancePkg⟩ := carrier
  have selectedMemberUnary : UnaryHistory selectedMember :=
    unary_cont_closed familyUnary modulusUnary selectedMemberRoute
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed selectedMemberUnary windowUnary selectedReadbackRoute
  have sealRowUnary : UnaryHistory sealRow :=
    unary_cont_closed readbackUnary dyadicUnary readbackDyadicSeal
  have completionSurfaceUnary : UnaryHistory completionSurface :=
    unary_cont_closed sealRowUnary localCertUnary completionSurfaceRoute
  exact
    ⟨familyUnary, modulusUnary, selectedMemberUnary, windowUnary, readbackUnary,
      sealRowUnary, completionSurfaceUnary, familyModulusDiagonal, selectedMemberRoute,
      selectedReadbackRoute, completionSurfaceRoute, provenancePkg, completionSurfacePkg⟩

end BEDC.Derived.RealCauchyCompletionUp
