import BEDC.Derived.RealCauchyCompletionUp

namespace BEDC.Derived.RealCauchyCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealCauchyCompletionCarrier_stream_regseq_tail_seal_factorization [AskSetup]
    [PackageSetup]
    {family modulus diagonal window readback dyadic sealRow provenance localCert consumerSurface
      completionRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealCauchyCompletionCarrier family modulus diagonal window readback dyadic sealRow
        provenance localCert bundle pkg ->
      UnaryHistory localCert ->
        Cont sealRow localCert consumerSurface ->
          Cont consumerSurface provenance completionRoute ->
            PkgSig bundle completionRoute pkg ->
              UnaryHistory diagonal ∧ UnaryHistory window ∧ UnaryHistory readback ∧
                UnaryHistory dyadic ∧ UnaryHistory sealRow ∧ UnaryHistory consumerSurface ∧
                  UnaryHistory completionRoute ∧ Cont family modulus diagonal ∧
                    Cont diagonal window readback ∧ Cont readback dyadic sealRow ∧
                      Cont sealRow localCert consumerSurface ∧
                        Cont consumerSurface provenance completionRoute ∧
                          PkgSig bundle provenance pkg ∧
                            PkgSig bundle completionRoute pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig
  intro carrier localCertUnary sealConsumer completionRouteRow completionRoutePkg
  obtain ⟨familyUnary, modulusUnary, windowUnary, dyadicUnary, provenanceUnary,
    familyModulusDiagonal, diagonalWindowReadback, readbackDyadicSeal,
    _sealLocalCertProvenance, provenancePkg⟩ := carrier
  have diagonalUnary : UnaryHistory diagonal :=
    unary_cont_closed familyUnary modulusUnary familyModulusDiagonal
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed diagonalUnary windowUnary diagonalWindowReadback
  have sealUnary : UnaryHistory sealRow :=
    unary_cont_closed readbackUnary dyadicUnary readbackDyadicSeal
  have consumerUnary : UnaryHistory consumerSurface :=
    unary_cont_closed sealUnary localCertUnary sealConsumer
  have completionUnary : UnaryHistory completionRoute :=
    unary_cont_closed consumerUnary provenanceUnary completionRouteRow
  exact
    ⟨diagonalUnary, windowUnary, readbackUnary, dyadicUnary, sealUnary, consumerUnary,
      completionUnary, familyModulusDiagonal, diagonalWindowReadback, readbackDyadicSeal,
      sealConsumer, completionRouteRow, provenancePkg, completionRoutePkg⟩

end BEDC.Derived.RealCauchyCompletionUp
