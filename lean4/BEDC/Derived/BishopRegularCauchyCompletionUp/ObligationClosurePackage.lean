import BEDC.Derived.BishopRegularCauchyCompletionUp

namespace BEDC.Derived.BishopRegularCauchyCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BishopRegularCauchyCompletionObligationClosurePackage [AskSetup] [PackageSetup]
    {endpoint observations regularity tailModulus commonTail transport replay provenance
      localName toleranceRead windowRead regularRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BishopRegularCauchyCompletionCarrier endpoint observations regularity tailModulus
        commonTail transport replay provenance localName bundle pkg →
      Cont tailModulus commonTail toleranceRead →
        Cont toleranceRead observations windowRead →
          Cont windowRead regularity regularRead →
            Cont regularRead endpoint sealRead →
              PkgSig bundle sealRead pkg →
                UnaryHistory endpoint ∧ UnaryHistory observations ∧ UnaryHistory regularity ∧
                  UnaryHistory tailModulus ∧ UnaryHistory commonTail ∧ UnaryHistory transport ∧
                    UnaryHistory replay ∧ UnaryHistory provenance ∧ UnaryHistory localName ∧
                      UnaryHistory toleranceRead ∧ UnaryHistory windowRead ∧
                        UnaryHistory regularRead ∧ UnaryHistory sealRead ∧
                          Cont tailModulus commonTail toleranceRead ∧
                            Cont toleranceRead observations windowRead ∧
                              Cont windowRead regularity regularRead ∧
                                Cont regularRead endpoint sealRead ∧
                                  PkgSig bundle provenance pkg ∧
                                    PkgSig bundle localName pkg ∧
                                      PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier tailCommon commonObservations observationsRegularity regularitySeal sealPkg
  obtain ⟨endpointUnary, observationsUnary, regularityUnary, tailModulusUnary,
    commonTailUnary, transportUnary, replayUnary, provenanceUnary, localNameUnary,
    provenancePkg, localNamePkg⟩ := carrier
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed tailModulusUnary commonTailUnary tailCommon
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed toleranceReadUnary observationsUnary commonObservations
  have regularReadUnary : UnaryHistory regularRead :=
    unary_cont_closed windowReadUnary regularityUnary observationsRegularity
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed regularReadUnary endpointUnary regularitySeal
  exact
    ⟨endpointUnary, observationsUnary, regularityUnary, tailModulusUnary, commonTailUnary,
      transportUnary, replayUnary, provenanceUnary, localNameUnary, toleranceReadUnary,
      windowReadUnary, regularReadUnary, sealReadUnary, tailCommon, commonObservations,
      observationsRegularity, regularitySeal, provenancePkg, localNamePkg, sealPkg⟩

end BEDC.Derived.BishopRegularCauchyCompletionUp
