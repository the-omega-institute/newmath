import BEDC.Derived.BishopRegularCauchyCompletionUp

namespace BEDC.Derived.BishopRegularCauchyCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BishopRegularCauchyCompletionTailDeterminacy [AskSetup] [PackageSetup]
    {endpoint observations regularity tailModulus commonTail transport replay provenance localName
      toleranceRead windowRead regularRead sealRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BishopRegularCauchyCompletionCarrier endpoint observations regularity tailModulus commonTail
        transport replay provenance localName bundle pkg ->
      Cont tailModulus commonTail toleranceRead ->
        Cont toleranceRead observations windowRead ->
          Cont windowRead regularity regularRead ->
            Cont regularRead endpoint sealRead ->
              Cont sealRead replay consumerRead ->
                PkgSig bundle consumerRead pkg ->
                  UnaryHistory toleranceRead ∧ UnaryHistory windowRead ∧
                    UnaryHistory regularRead ∧ UnaryHistory sealRead ∧
                      UnaryHistory consumerRead ∧ Cont tailModulus commonTail toleranceRead ∧
                        Cont toleranceRead observations windowRead ∧
                          Cont windowRead regularity regularRead ∧
                            Cont regularRead endpoint sealRead ∧
                              Cont sealRead replay consumerRead ∧
                                PkgSig bundle provenance pkg ∧
                                  PkgSig bundle localName pkg ∧
                                    PkgSig bundle consumerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier tailCommon toleranceWindow windowRegular regularSeal sealConsumer consumerPkg
  obtain ⟨endpointUnary, observationsUnary, regularityUnary, tailModulusUnary,
    commonTailUnary, _transportUnary, replayUnary, _provenanceUnary, _localNameUnary,
    provenancePkg, localNamePkg⟩ := carrier
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed tailModulusUnary commonTailUnary tailCommon
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed toleranceUnary observationsUnary toleranceWindow
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed windowUnary regularityUnary windowRegular
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed regularUnary endpointUnary regularSeal
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed sealUnary replayUnary sealConsumer
  exact
    ⟨toleranceUnary, windowUnary, regularUnary, sealUnary, consumerUnary, tailCommon,
      toleranceWindow, windowRegular, regularSeal, sealConsumer, provenancePkg, localNamePkg,
      consumerPkg⟩

end BEDC.Derived.BishopRegularCauchyCompletionUp
