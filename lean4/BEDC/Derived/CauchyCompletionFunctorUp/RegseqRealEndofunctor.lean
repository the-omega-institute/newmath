import BEDC.Derived.CauchyCompletionFunctorUp

namespace BEDC.Derived.CauchyCompletionFunctorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyCompletionFunctorPacket_regseq_real_endofunctor
    [AskSetup] [PackageSetup]
    {metric regular sealRow monadRow universal classifier transport nameCert endpoint
      regseqRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionFunctorPacket metric regular sealRow monadRow universal classifier transport
        nameCert endpoint bundle pkg ->
      Cont regular sealRow regseqRead ->
        Cont regseqRead monadRow completionRead ->
          PkgSig bundle completionRead pkg ->
            UnaryHistory regseqRead ∧ UnaryHistory completionRead ∧
              Cont regular sealRow regseqRead ∧
                Cont regseqRead monadRow completionRead ∧
                  Cont metric regular sealRow ∧ Cont monadRow universal endpoint ∧
                    PkgSig bundle endpoint pkg ∧ PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro packet regularSealRegseq regseqMonadCompletion completionPkg
  obtain ⟨_metricUnary, regularUnary, sealUnary, monadUnary, _universalUnary,
    _classifierUnary, _transportUnary, _nameCertUnary, _endpointUnary, metricRegularSeal,
    monadUniversalEndpoint, _classifierTransportNameCert, endpointPkg⟩ := packet
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed regularUnary sealUnary regularSealRegseq
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed regseqUnary monadUnary regseqMonadCompletion
  exact
    ⟨regseqUnary, completionUnary, regularSealRegseq, regseqMonadCompletion,
      metricRegularSeal, monadUniversalEndpoint, endpointPkg, completionPkg⟩

end BEDC.Derived.CauchyCompletionFunctorUp
