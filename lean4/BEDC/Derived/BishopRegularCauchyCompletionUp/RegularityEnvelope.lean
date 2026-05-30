import BEDC.Derived.BishopRegularCauchyCompletionUp

namespace BEDC.Derived.BishopRegularCauchyCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BishopRegularCauchyCompletionRegularityEnvelope [AskSetup] [PackageSetup]
    {endpoint observations regularity tailModulus commonTail transport replay provenance
      localName observationRead regularRead endpointRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BishopRegularCauchyCompletionCarrier endpoint observations regularity tailModulus
        commonTail transport replay provenance localName bundle pkg →
      Cont observations regularity observationRead →
        Cont observationRead tailModulus regularRead →
          Cont regularRead commonTail endpointRead →
            Cont endpointRead endpoint sealRead →
              PkgSig bundle sealRead pkg →
                UnaryHistory observations ∧ UnaryHistory regularity ∧
                  UnaryHistory tailModulus ∧ UnaryHistory commonTail ∧
                    UnaryHistory endpoint ∧ UnaryHistory observationRead ∧
                      UnaryHistory regularRead ∧ UnaryHistory endpointRead ∧
                        UnaryHistory sealRead ∧
                          Cont observations regularity observationRead ∧
                            Cont observationRead tailModulus regularRead ∧
                              Cont regularRead commonTail endpointRead ∧
                                Cont endpointRead endpoint sealRead ∧
                                  PkgSig bundle provenance pkg ∧
                                    PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier observationsRegularity observationTail regularCommon endpointSeal sealPkg
  obtain ⟨endpointUnary, observationsUnary, regularityUnary, tailModulusUnary,
    commonTailUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    provenancePkg, _localNamePkg⟩ := carrier
  have observationReadUnary : UnaryHistory observationRead :=
    unary_cont_closed observationsUnary regularityUnary observationsRegularity
  have regularReadUnary : UnaryHistory regularRead :=
    unary_cont_closed observationReadUnary tailModulusUnary observationTail
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed regularReadUnary commonTailUnary regularCommon
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed endpointReadUnary endpointUnary endpointSeal
  exact
    ⟨observationsUnary, regularityUnary, tailModulusUnary, commonTailUnary, endpointUnary,
      observationReadUnary, regularReadUnary, endpointReadUnary, sealReadUnary,
      observationsRegularity, observationTail, regularCommon, endpointSeal, provenancePkg,
      sealPkg⟩

end BEDC.Derived.BishopRegularCauchyCompletionUp
