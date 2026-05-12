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
      intro _row sourceRow
      exact
        ⟨familyUnary, modulusUnary, familyModulusRow, diagonalWindowRow,
          readbackDyadicRow⟩
    ledger_sound := by
      intro row sourceRow
      exact ⟨provenancePkg, unary_transport provenanceUnary (hsame_symm sourceRow.left)⟩
  }

end BEDC.Derived.RealCauchyCompletionUp
