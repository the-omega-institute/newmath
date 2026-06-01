import BEDC.Derived.BishopRegularCauchyCompletionUp

namespace BEDC.Derived.BishopRegularCauchyCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BishopRegularCauchyCompletionCarrier_diagonal_window_stability [AskSetup]
    [PackageSetup]
    {endpoint observations regularity tailModulus commonWindow transport replay provenance
      localName observationsPrime regularityPrime endpointRead endpointReadPrime sealRead
      sealReadPrime : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BishopRegularCauchyCompletionCarrier endpoint observations regularity tailModulus
        commonWindow transport replay provenance localName bundle pkg ->
      hsame regularity regularityPrime ->
        Cont tailModulus commonWindow observations ->
          Cont observations regularity endpointRead ->
            Cont endpointRead endpoint sealRead ->
              Cont tailModulus commonWindow observationsPrime ->
                Cont observationsPrime regularityPrime endpointReadPrime ->
                  Cont endpointReadPrime endpoint sealReadPrime ->
                    PkgSig bundle sealRead pkg ->
                      PkgSig bundle sealReadPrime pkg ->
                        UnaryHistory tailModulus ∧ UnaryHistory commonWindow ∧
                          UnaryHistory observations ∧ UnaryHistory observationsPrime ∧
                            UnaryHistory regularityPrime ∧ UnaryHistory endpointRead ∧
                              UnaryHistory endpointReadPrime ∧ UnaryHistory sealRead ∧
                                UnaryHistory sealReadPrime ∧
                                  Cont tailModulus commonWindow observations ∧
                                    Cont tailModulus commonWindow observationsPrime ∧
                                      PkgSig bundle provenance pkg ∧
                                        PkgSig bundle sealRead pkg ∧
                                          PkgSig bundle sealReadPrime pkg := by
  -- BEDC touchpoint anchor: BHist hsame ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier sameRegularity tailCommon observationsRegularity endpointSeal
    tailCommonPrime observationsRegularityPrime endpointSealPrime sealPkg sealPrimePkg
  obtain ⟨endpointUnary, observationsUnary, regularityUnary, tailModulusUnary,
    commonWindowUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
      provenancePkg, _localNamePkg⟩ := carrier
  have regularityPrimeUnary : UnaryHistory regularityPrime :=
    unary_transport regularityUnary sameRegularity
  have observationsPrimeUnary : UnaryHistory observationsPrime :=
    unary_cont_closed tailModulusUnary commonWindowUnary tailCommonPrime
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed observationsUnary regularityUnary observationsRegularity
  have endpointReadPrimeUnary : UnaryHistory endpointReadPrime :=
    unary_cont_closed observationsPrimeUnary regularityPrimeUnary observationsRegularityPrime
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed endpointReadUnary endpointUnary endpointSeal
  have sealReadPrimeUnary : UnaryHistory sealReadPrime :=
    unary_cont_closed endpointReadPrimeUnary endpointUnary endpointSealPrime
  exact
    ⟨tailModulusUnary, commonWindowUnary, observationsUnary, observationsPrimeUnary,
      regularityPrimeUnary, endpointReadUnary, endpointReadPrimeUnary, sealReadUnary,
      sealReadPrimeUnary, tailCommon, tailCommonPrime, provenancePkg, sealPkg, sealPrimePkg⟩

end BEDC.Derived.BishopRegularCauchyCompletionUp
