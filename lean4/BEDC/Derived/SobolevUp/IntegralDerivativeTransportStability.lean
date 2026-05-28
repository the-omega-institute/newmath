import BEDC.Derived.SobolevUp

namespace BEDC.Derived.SobolevUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SobolevCarrier_integral_derivative_transport_stability [AskSetup] [PackageSetup]
    {D M V L G H C P N D' M' V' L' G' H' C' P' N' integralRead derivativeRead
      transportedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SobolevCarrier D M V L G H C P N bundle pkg ->
      SobolevCarrier D' M' V' L' G' H' C' P' N' bundle pkg ->
        hsame D D' ->
          hsame M M' ->
            hsame V V' ->
              hsame L L' ->
                hsame G G' ->
                  Cont L G integralRead ->
                    Cont integralRead C derivativeRead ->
                      Cont L' G' transportedRead ->
                        PkgSig bundle transportedRead pkg ->
                          UnaryHistory D ∧ UnaryHistory M ∧ UnaryHistory V ∧
                            UnaryHistory L ∧ UnaryHistory G ∧ UnaryHistory D' ∧
                              UnaryHistory M' ∧ UnaryHistory V' ∧ UnaryHistory L' ∧
                                UnaryHistory G' ∧ UnaryHistory integralRead ∧
                                  UnaryHistory derivativeRead ∧ UnaryHistory transportedRead ∧
                                    hsame D D' ∧ hsame M M' ∧ hsame V V' ∧
                                      hsame L L' ∧ hsame G G' ∧
                                        Cont L G integralRead ∧
                                          Cont integralRead C derivativeRead ∧
                                            Cont L' G' transportedRead ∧
                                              PkgSig bundle P pkg ∧
                                                PkgSig bundle P' pkg ∧
                                                  PkgSig bundle transportedRead pkg := by
  -- BEDC touchpoint anchor: SobolevCarrier BHist ProbeBundle Pkg Cont hsame
  intro sourceCarrier targetCarrier sameD sameM sameV sameL sameG integralRoute
    derivativeRoute transportedRoute transportedPkg
  obtain ⟨domainUnary, baseUnary, codomainUnary, magnitudeUnary, gradientUnary,
    _transportUnary, replayUnary, _provenanceUnary, _localCertUnary, _domainBaseCodomain,
    _codomainMagnitudeGradient, _gradientTransportReplay, _replayProvenanceLocalCert,
    provenancePkg⟩ := sourceCarrier
  obtain ⟨domainUnary', baseUnary', codomainUnary', magnitudeUnary', gradientUnary',
    _transportUnary', _replayUnary', _provenanceUnary', _localCertUnary',
    _domainBaseCodomain', _codomainMagnitudeGradient', _gradientTransportReplay',
    _replayProvenanceLocalCert', provenancePkg'⟩ := targetCarrier
  have integralUnary : UnaryHistory integralRead :=
    unary_cont_closed magnitudeUnary gradientUnary integralRoute
  have derivativeUnary : UnaryHistory derivativeRead :=
    unary_cont_closed integralUnary replayUnary derivativeRoute
  have transportedUnary : UnaryHistory transportedRead :=
    unary_cont_closed magnitudeUnary' gradientUnary' transportedRoute
  exact
    ⟨domainUnary, baseUnary, codomainUnary, magnitudeUnary, gradientUnary, domainUnary',
      baseUnary', codomainUnary', magnitudeUnary', gradientUnary', integralUnary,
      derivativeUnary, transportedUnary, sameD, sameM, sameV, sameL, sameG,
      integralRoute, derivativeRoute, transportedRoute, provenancePkg, provenancePkg',
      transportedPkg⟩

end BEDC.Derived.SobolevUp
