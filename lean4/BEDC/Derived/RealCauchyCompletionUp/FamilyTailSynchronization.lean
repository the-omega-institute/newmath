import BEDC.Derived.RealCauchyCompletionUp

namespace BEDC.Derived.RealCauchyCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealCauchyCompletionCarrier_family_tail_synchronization [AskSetup] [PackageSetup]
    {family modulus diagonal window readback dyadic sealRow provenance localCert family'
      modulus' diagonal' window' readback' dyadic' sealRow' provenance' localCert' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealCauchyCompletionCarrier family modulus diagonal window readback dyadic sealRow
        provenance localCert bundle pkg ->
      RealCauchyCompletionCarrier family' modulus' diagonal' window' readback' dyadic'
          sealRow' provenance' localCert' bundle pkg ->
        hsame family family' ->
          hsame modulus modulus' ->
            hsame window window' ->
              hsame dyadic dyadic' ->
                hsame readback readback' ∧ hsame sealRow sealRow' ∧
                  UnaryHistory sealRow ∧ UnaryHistory sealRow' ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle provenance' pkg := by
  intro carrier carrier' sameFamily sameModulus sameWindow sameDyadic
  obtain ⟨familyUnary, modulusUnary, windowUnary, dyadicUnary, _provenanceUnary,
    familyModulusRow, diagonalWindowRow, readbackDyadicRow, _sealLocalProvenance,
    provenancePkg⟩ := carrier
  obtain ⟨_familyUnary', _modulusUnary', _windowUnary', dyadicUnary',
    _provenanceUnary', familyModulusRow', diagonalWindowRow', readbackDyadicRow',
    _sealLocalProvenance', provenancePkg'⟩ := carrier'
  have sameDiagonal : hsame diagonal diagonal' :=
    cont_respects_hsame sameFamily sameModulus familyModulusRow familyModulusRow'
  have sameReadback : hsame readback readback' :=
    cont_respects_hsame sameDiagonal sameWindow diagonalWindowRow diagonalWindowRow'
  have sameSeal : hsame sealRow sealRow' :=
    cont_respects_hsame sameReadback sameDyadic readbackDyadicRow readbackDyadicRow'
  have diagonalUnary : UnaryHistory diagonal :=
    unary_cont_closed familyUnary modulusUnary familyModulusRow
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed diagonalUnary windowUnary diagonalWindowRow
  have sealUnary : UnaryHistory sealRow :=
    unary_cont_closed readbackUnary dyadicUnary readbackDyadicRow
  have sealUnary' : UnaryHistory sealRow' :=
    unary_transport sealUnary sameSeal
  exact ⟨sameReadback, sameSeal, sealUnary, sealUnary', provenancePkg, provenancePkg'⟩

end BEDC.Derived.RealCauchyCompletionUp
