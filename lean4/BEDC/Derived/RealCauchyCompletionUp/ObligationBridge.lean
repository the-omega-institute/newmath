import BEDC.Derived.RealCauchyCompletionUp

namespace BEDC.Derived.RealCauchyCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealCauchyCompletionCarrier_obligation_closure_package [AskSetup] [PackageSetup]
    {family modulus diagonal window readback dyadic sealRow provenance localCert consumerRead
      scopedSurface : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealCauchyCompletionCarrier family modulus diagonal window readback dyadic sealRow
        provenance localCert bundle pkg ->
      UnaryHistory localCert ->
        Cont sealRow localCert consumerRead ->
          Cont consumerRead provenance scopedSurface ->
            PkgSig bundle scopedSurface pkg ->
              SemanticNameCert
                (fun row : BHist =>
                  hsame row scopedSurface ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
                (fun row : BHist =>
                  Cont readback dyadic sealRow ∧ Cont sealRow localCert consumerRead ∧
                    Cont consumerRead provenance row)
                (fun row : BHist =>
                  PkgSig bundle provenance pkg ∧ PkgSig bundle row pkg ∧
                    UnaryHistory family ∧ UnaryHistory modulus)
                hsame := by
  intro carrier localCertUnary consumerRow scopedRow scopedPkg
  obtain ⟨familyUnary, modulusUnary, windowUnary, dyadicUnary, provenanceUnary,
    familyModulusRow, diagonalWindowRow, readbackDyadicRow, _sealProvenanceRow,
    provenancePkg⟩ := carrier
  have diagonalUnary : UnaryHistory diagonal :=
    unary_cont_closed familyUnary modulusUnary familyModulusRow
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed diagonalUnary windowUnary diagonalWindowRow
  have sealUnary : UnaryHistory sealRow :=
    unary_cont_closed readbackUnary dyadicUnary readbackDyadicRow
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed sealUnary localCertUnary consumerRow
  have scopedUnary : UnaryHistory scopedSurface :=
    unary_cont_closed consumerUnary provenanceUnary scopedRow
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro scopedSurface ⟨hsame_refl scopedSurface, scopedUnary, scopedPkg⟩
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
        exact
          ⟨hsame_trans (hsame_symm classified) sourceRow.left,
            unary_transport sourceRow.right.left classified,
            by
              cases classified
              exact sourceRow.right.right⟩
    }
    pattern_sound := by
      intro _row sourceRow
      cases sourceRow.left
      exact ⟨readbackDyadicRow, consumerRow, scopedRow⟩
    ledger_sound := by
      intro _row sourceRow
      exact ⟨provenancePkg, sourceRow.right.right, familyUnary, modulusUnary⟩
  }

theorem RealCauchyCompletionCarrier_standard_bridge_boundary [AskSetup] [PackageSetup]
    {family modulus diagonal window readback dyadic sealRow provenance localCert consumerRead
      bridgeSurface : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealCauchyCompletionCarrier family modulus diagonal window readback dyadic sealRow
        provenance localCert bundle pkg ->
      UnaryHistory localCert ->
        Cont sealRow localCert consumerRead ->
          Cont consumerRead provenance bridgeSurface ->
            PkgSig bundle bridgeSurface pkg ->
              UnaryHistory family ∧ UnaryHistory modulus ∧ UnaryHistory diagonal ∧
                UnaryHistory window ∧ UnaryHistory readback ∧ UnaryHistory dyadic ∧
                  UnaryHistory sealRow ∧ UnaryHistory consumerRead ∧
                    UnaryHistory bridgeSurface ∧ Cont family modulus diagonal ∧
                      Cont diagonal window readback ∧ Cont readback dyadic sealRow ∧
                        Cont sealRow localCert consumerRead ∧
                          Cont consumerRead provenance bridgeSurface ∧
                            PkgSig bundle provenance pkg ∧
                              SemanticNameCert
                                (fun row : BHist =>
                                  hsame row bridgeSurface ∧ UnaryHistory row ∧
                                    PkgSig bundle row pkg)
                                (fun row : BHist => hsame row bridgeSurface ∧ UnaryHistory row)
                                (fun row : BHist => PkgSig bundle row pkg ∧
                                  hsame row bridgeSurface)
                                hsame := by
  intro carrier localCertUnary consumerRow bridgeRow bridgePkg
  obtain ⟨familyUnary, modulusUnary, windowUnary, dyadicUnary, provenanceUnary,
    familyModulusRow, diagonalWindowRow, readbackDyadicRow, _sealProvenanceRow,
    provenancePkg⟩ := carrier
  have diagonalUnary : UnaryHistory diagonal :=
    unary_cont_closed familyUnary modulusUnary familyModulusRow
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed diagonalUnary windowUnary diagonalWindowRow
  have sealUnary : UnaryHistory sealRow :=
    unary_cont_closed readbackUnary dyadicUnary readbackDyadicRow
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed sealUnary localCertUnary consumerRow
  have bridgeUnary : UnaryHistory bridgeSurface :=
    unary_cont_closed consumerUnary provenanceUnary bridgeRow
  have semantic :
      SemanticNameCert
        (fun row : BHist => hsame row bridgeSurface ∧ UnaryHistory row ∧
          PkgSig bundle row pkg)
        (fun row : BHist => hsame row bridgeSurface ∧ UnaryHistory row)
        (fun row : BHist => PkgSig bundle row pkg ∧ hsame row bridgeSurface)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro bridgeSurface ⟨hsame_refl bridgeSurface, bridgeUnary, bridgePkg⟩
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
        exact
          ⟨hsame_trans (hsame_symm classified) sourceRow.left,
            unary_transport sourceRow.right.left classified,
            by
              cases classified
              exact sourceRow.right.right⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, sourceRow.right.left⟩
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right.right, sourceRow.left⟩
  }
  exact
    ⟨familyUnary, modulusUnary, diagonalUnary, windowUnary, readbackUnary, dyadicUnary,
      sealUnary, consumerUnary, bridgeUnary, familyModulusRow, diagonalWindowRow,
      readbackDyadicRow, consumerRow, bridgeRow, provenancePkg, semantic⟩

end BEDC.Derived.RealCauchyCompletionUp
