import BEDC.Derived.RealCauchyCompletionUp

namespace BEDC.Derived.RealCauchyCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealCauchyCompletionCarrier_standard_bishop_reading [AskSetup] [PackageSetup]
    {family modulus diagonal window readback dyadic sealRow provenance localCert
      bishopSurface : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealCauchyCompletionCarrier family modulus diagonal window readback dyadic sealRow
        provenance localCert bundle pkg ->
      UnaryHistory localCert ->
        Cont sealRow localCert bishopSurface ->
          PkgSig bundle bishopSurface pkg ->
            SemanticNameCert
              (fun row : BHist =>
                hsame row bishopSurface ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
              (fun row : BHist =>
                Cont family modulus diagonal ∧ Cont diagonal window readback ∧
                  Cont readback dyadic sealRow ∧ Cont sealRow localCert row)
              (fun row : BHist =>
                UnaryHistory family ∧ UnaryHistory modulus ∧ UnaryHistory window ∧
                  UnaryHistory dyadic ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle row pkg)
              hsame := by
  intro carrier localCertUnary sealLocalCertBishop bishopPkg
  obtain ⟨familyUnary, modulusUnary, windowUnary, dyadicUnary, _provenanceUnary,
    familyModulusDiagonal, diagonalWindowReadback, readbackDyadicSeal,
    _sealLocalCertProvenance, provenancePkg⟩ := carrier
  have diagonalUnary : UnaryHistory diagonal :=
    unary_cont_closed familyUnary modulusUnary familyModulusDiagonal
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed diagonalUnary windowUnary diagonalWindowReadback
  have sealUnary : UnaryHistory sealRow :=
    unary_cont_closed readbackUnary dyadicUnary readbackDyadicSeal
  have bishopUnary : UnaryHistory bishopSurface :=
    unary_cont_closed sealUnary localCertUnary sealLocalCertBishop
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro bishopSurface ⟨hsame_refl bishopSurface, bishopUnary, bishopPkg⟩
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
      exact
        ⟨familyModulusDiagonal, diagonalWindowReadback, readbackDyadicSeal,
          sealLocalCertBishop⟩
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨familyUnary, modulusUnary, windowUnary, dyadicUnary, provenancePkg,
          sourceRow.right.right⟩
  }

end BEDC.Derived.RealCauchyCompletionUp
