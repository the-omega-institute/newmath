import BEDC.Derived.RealCauchyCompletionUp

namespace BEDC.Derived.RealCauchyCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealCauchyCompletionCarrier_bridge_handoff [AskSetup] [PackageSetup]
    {family modulus diagonal window readback dyadic sealRow provenance localCert consumerRead
      bridgeSurface publicSurface : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealCauchyCompletionCarrier family modulus diagonal window readback dyadic sealRow
        provenance localCert bundle pkg ->
      UnaryHistory localCert ->
        Cont sealRow localCert consumerRead ->
          Cont consumerRead provenance bridgeSurface ->
            Cont bridgeSurface provenance publicSurface ->
              PkgSig bundle bridgeSurface pkg ->
                PkgSig bundle publicSurface pkg ->
                  SemanticNameCert
                    (fun row : BHist =>
                      hsame row publicSurface ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
                    (fun row : BHist => hsame row publicSurface ∧ UnaryHistory row)
                    (fun row : BHist =>
                      PkgSig bundle provenance pkg ∧ PkgSig bundle row pkg ∧
                        Cont consumerRead provenance bridgeSurface ∧
                          Cont bridgeSurface provenance publicSurface)
                    hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier localCertUnary sealLocalCertConsumer consumerProvenanceBridge
    bridgeProvenancePublic _bridgePkg publicPkg
  have handoff :=
    RealCauchyCompletionCarrier_diagonal_handoff carrier localCertUnary
      sealLocalCertConsumer
  obtain ⟨_diagonalUnary, _windowUnary, _readbackUnary, _dyadicUnary, _sealUnary,
    consumerUnary, _familyModulusRow, _diagonalWindowRow, _readbackDyadicRow,
    provenancePkg⟩ := handoff
  obtain ⟨_familyUnary, _modulusUnary, _carrierWindowUnary, _carrierDyadicUnary,
    provenanceUnary, _carrierFamilyModulusRow, _carrierDiagonalWindowRow,
    _carrierReadbackDyadicRow, _sealLocalCertProvenance, _carrierPkg⟩ := carrier
  have bridgeUnary : UnaryHistory bridgeSurface :=
    unary_cont_closed consumerUnary provenanceUnary consumerProvenanceBridge
  have publicUnary : UnaryHistory publicSurface :=
    unary_cont_closed bridgeUnary provenanceUnary bridgeProvenancePublic
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro publicSurface ⟨hsame_refl publicSurface, publicUnary, publicPkg⟩
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
      exact
        ⟨provenancePkg, sourceRow.right.right, consumerProvenanceBridge,
          bridgeProvenancePublic⟩
  }

end BEDC.Derived.RealCauchyCompletionUp
