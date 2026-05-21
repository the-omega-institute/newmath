import BEDC.Derived.RealCauchyCompletionUp

namespace BEDC.Derived.RealCauchyCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealCauchyCompletionUp_StdBridge [AskSetup] [PackageSetup]
    {family modulus diagonal window readback dyadic sealRow provenance localCert consumerRead
      bundleSurface forbidden : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealCauchyCompletionCarrier family modulus diagonal window readback dyadic sealRow
        provenance localCert bundle pkg →
      UnaryHistory localCert →
        Cont sealRow localCert consumerRead →
          Cont consumerRead localCert bundleSurface →
            PkgSig bundle bundleSurface pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    hsame row bundleSurface ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
                  (fun row : BHist => hsame row bundleSurface ∧ UnaryHistory row)
                  (fun row : BHist => PkgSig bundle row pkg ∧ hsame row bundleSurface)
                  hsame ∧
                (Cont bundleSurface (BHist.e1 forbidden) bundleSurface → False) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier localCertUnary sealLocalCertConsumer consumerLocalBundle bundlePkg
  obtain ⟨familyUnary, modulusUnary, windowUnary, dyadicUnary, _provenanceUnary,
    familyModulusDiagonal, diagonalWindowReadback, readbackDyadicSeal,
    _sealLocalProvenance, _provenancePkg⟩ := carrier
  have diagonalUnary : UnaryHistory diagonal :=
    unary_cont_closed familyUnary modulusUnary familyModulusDiagonal
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed diagonalUnary windowUnary diagonalWindowReadback
  have sealUnary : UnaryHistory sealRow :=
    unary_cont_closed readbackUnary dyadicUnary readbackDyadicSeal
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed sealUnary localCertUnary sealLocalCertConsumer
  have bundleUnary : UnaryHistory bundleSurface :=
    unary_cont_closed consumerUnary localCertUnary consumerLocalBundle
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          hsame row bundleSurface ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
        (fun row : BHist => hsame row bundleSurface ∧ UnaryHistory row)
        (fun row : BHist => PkgSig bundle row pkg ∧ hsame row bundleSurface)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro bundleSurface ⟨hsame_refl bundleSurface, bundleUnary, bundlePkg⟩
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
  have refusal : Cont bundleSurface (BHist.e1 forbidden) bundleSurface → False := by
    intro selectedHostRoute
    have suffixEmpty : hsame (BHist.e1 forbidden) BHist.Empty :=
      cont_right_unit_unique selectedHostRoute
    exact not_hsame_e1_empty suffixEmpty
  exact ⟨cert, refusal⟩

end BEDC.Derived.RealCauchyCompletionUp
