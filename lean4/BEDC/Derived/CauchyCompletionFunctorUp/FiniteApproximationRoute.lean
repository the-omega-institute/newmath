import BEDC.Derived.CauchyCompletionFunctorUp

namespace BEDC.Derived.CauchyCompletionFunctorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyCompletionFunctorPacket_finite_approximation_route
    [AskSetup] [PackageSetup]
    {metric regular sealRow monadRow universal classifier transport nameCert endpoint
      approximationStart approximationWindow approximationDyadic approximationRead
      completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionFunctorPacket metric regular sealRow monadRow universal classifier transport
        nameCert endpoint bundle pkg ->
      UnaryHistory approximationStart ->
        UnaryHistory approximationWindow ->
          Cont approximationStart approximationWindow approximationDyadic ->
            Cont approximationDyadic regular approximationRead ->
              Cont approximationRead sealRow completionRead ->
                PkgSig bundle completionRead pkg ->
                  UnaryHistory approximationDyadic ∧ UnaryHistory approximationRead ∧
                    UnaryHistory completionRead ∧
                      Cont approximationStart approximationWindow approximationDyadic ∧
                        Cont approximationDyadic regular approximationRead ∧
                          Cont approximationRead sealRow completionRead ∧
                            Cont metric regular sealRow ∧ Cont monadRow universal endpoint ∧
                              PkgSig bundle endpoint pkg ∧
                                PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet approximationStartUnary approximationWindowUnary startWindowDyadic
    dyadicRegularRead readSealCompletion completionPkg
  obtain ⟨_metricUnary, regularUnary, sealUnary, _monadUnary, _universalUnary,
    _classifierUnary, _transportUnary, _nameCertUnary, _endpointUnary, metricRegularSeal,
    monadUniversalEndpoint, _classifierTransportNameCert, endpointPkg⟩ := packet
  have approximationDyadicUnary : UnaryHistory approximationDyadic :=
    unary_cont_closed approximationStartUnary approximationWindowUnary startWindowDyadic
  have approximationReadUnary : UnaryHistory approximationRead :=
    unary_cont_closed approximationDyadicUnary regularUnary dyadicRegularRead
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed approximationReadUnary sealUnary readSealCompletion
  exact
    ⟨approximationDyadicUnary, approximationReadUnary, completionReadUnary,
      startWindowDyadic, dyadicRegularRead, readSealCompletion, metricRegularSeal,
      monadUniversalEndpoint, endpointPkg, completionPkg⟩

end BEDC.Derived.CauchyCompletionFunctorUp
