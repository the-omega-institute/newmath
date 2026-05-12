import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RealCauchyCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
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

theorem RealCauchyCompletionCarrier_modulus_diagonal_exactness [AskSetup] [PackageSetup]
    {family modulus diagonal window readback dyadic «seal» provenance localCert selectedRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealCauchyCompletionCarrier family modulus diagonal window readback dyadic «seal»
        provenance localCert bundle pkg ->
      Cont modulus diagonal selectedRead ->
        PkgSig bundle selectedRead pkg ->
          UnaryHistory family ∧ UnaryHistory modulus ∧ UnaryHistory diagonal ∧
            UnaryHistory window ∧ UnaryHistory readback ∧ UnaryHistory dyadic ∧
              UnaryHistory «seal» ∧ UnaryHistory selectedRead ∧
                Cont family modulus diagonal ∧ Cont diagonal window readback ∧
                  Cont readback dyadic «seal» ∧ Cont modulus diagonal selectedRead ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle selectedRead pkg := by
  intro carrier modulusDiagonalRead selectedPkg
  cases carrier with
  | intro familyUnary rest =>
      cases rest with
      | intro modulusUnary rest =>
          cases rest with
          | intro windowUnary rest =>
              cases rest with
              | intro dyadicUnary rest =>
                  cases rest with
                  | intro _provenanceUnary rest =>
                      cases rest with
                      | intro familyModulusDiagonal rest =>
                          cases rest with
                          | intro diagonalWindowReadback rest =>
                              cases rest with
                              | intro readbackDyadicSeal rest =>
                                  cases rest with
                                  | intro _sealLocalCertProvenance provenancePkg =>
                                      have diagonalUnary : UnaryHistory diagonal :=
                                        unary_cont_closed familyUnary modulusUnary
                                          familyModulusDiagonal
                                      have readbackUnary : UnaryHistory readback :=
                                        unary_cont_closed diagonalUnary windowUnary
                                          diagonalWindowReadback
                                      have sealUnary : UnaryHistory «seal» :=
                                        unary_cont_closed readbackUnary dyadicUnary
                                          readbackDyadicSeal
                                      have selectedUnary : UnaryHistory selectedRead :=
                                        unary_cont_closed modulusUnary diagonalUnary
                                          modulusDiagonalRead
                                      exact
                                        ⟨familyUnary, modulusUnary, diagonalUnary, windowUnary,
                                          readbackUnary, dyadicUnary, sealUnary, selectedUnary,
                                          familyModulusDiagonal, diagonalWindowReadback,
                                          readbackDyadicSeal, modulusDiagonalRead, provenancePkg,
                                          selectedPkg⟩

end BEDC.Derived.RealCauchyCompletionUp
