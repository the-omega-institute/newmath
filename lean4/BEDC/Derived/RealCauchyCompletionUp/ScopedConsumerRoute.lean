import BEDC.Derived.RealCauchyCompletionUp

namespace BEDC.Derived.RealCauchyCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealCauchyCompletionCarrier_scoped_consumer_route [AskSetup] [PackageSetup]
    {family modulus diagonal window readback dyadic sealRow provenance localCert consumerRead
      scopedSurface downstream : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealCauchyCompletionCarrier family modulus diagonal window readback dyadic sealRow
        provenance localCert bundle pkg ->
      UnaryHistory localCert ->
        Cont sealRow localCert consumerRead ->
          Cont consumerRead provenance scopedSurface ->
            Cont scopedSurface readback downstream ->
              PkgSig bundle scopedSurface pkg ->
                PkgSig bundle downstream pkg ->
                  SemanticNameCert
                    (fun row : BHist => hsame row scopedSurface ∧ UnaryHistory row ∧
                      PkgSig bundle row pkg)
                    (fun row : BHist => hsame row scopedSurface ∧
                      Cont consumerRead provenance row)
                    (fun _row : BHist =>
                      RealCauchyCompletionCarrier family modulus diagonal window readback dyadic
                        sealRow provenance localCert bundle pkg ∧ PkgSig bundle provenance pkg)
                    hsame ∧ UnaryHistory downstream ∧
                      Cont scopedSurface readback downstream := by
  intro carrier localCertUnary consumerReadRow scopedSurfaceRow downstreamRow scopedPkg
    _downstreamPkg
  have carrierData := carrier
  obtain ⟨familyUnary, modulusUnary, windowUnary, dyadicUnary, provenanceUnary,
    familyModulusRow, diagonalWindowRow, readbackDyadicRow, _sealLocalCertRow,
    provenancePkg⟩ := carrier
  have diagonalUnary : UnaryHistory diagonal :=
    unary_cont_closed familyUnary modulusUnary familyModulusRow
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed diagonalUnary windowUnary diagonalWindowRow
  have sealUnary : UnaryHistory sealRow :=
    unary_cont_closed readbackUnary dyadicUnary readbackDyadicRow
  have consumerReadUnary : UnaryHistory consumerRead :=
    unary_cont_closed sealUnary localCertUnary consumerReadRow
  have scopedSurfaceUnary : UnaryHistory scopedSurface :=
    unary_cont_closed consumerReadUnary provenanceUnary scopedSurfaceRow
  have downstreamUnary : UnaryHistory downstream :=
    unary_cont_closed scopedSurfaceUnary readbackUnary downstreamRow
  have sourceScoped :
      hsame scopedSurface scopedSurface ∧ UnaryHistory scopedSurface ∧
        PkgSig bundle scopedSurface pkg :=
    ⟨hsame_refl scopedSurface, scopedSurfaceUnary, scopedPkg⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row scopedSurface ∧ UnaryHistory row ∧
          PkgSig bundle row pkg)
        (fun row : BHist => hsame row scopedSurface ∧ Cont consumerRead provenance row)
        (fun _row : BHist =>
          RealCauchyCompletionCarrier family modulus diagonal window readback dyadic sealRow
            provenance localCert bundle pkg ∧ PkgSig bundle provenance pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro scopedSurface sourceScoped
      equiv_refl := by
        intro row _sourceRow
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows sourceRow
        cases sameRows
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      cases sourceRow.left
      exact ⟨hsame_refl scopedSurface, scopedSurfaceRow⟩
    ledger_sound := by
      intro _row _sourceRow
      exact ⟨carrierData, provenancePkg⟩
  }
  exact ⟨cert, downstreamUnary, downstreamRow⟩

end BEDC.Derived.RealCauchyCompletionUp
