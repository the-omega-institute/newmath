import BEDC.Derived.MetaCICCriticalPathUp

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathBoundedConversionSocketBudget
    [AskSetup] [PackageSetup] {candidate snEndpoint socket checkerBudget conversionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory candidate ->
      UnaryHistory snEndpoint ->
        UnaryHistory socket ->
          UnaryHistory checkerBudget ->
            Cont candidate snEndpoint socket ->
              Cont socket checkerBudget conversionRead ->
                PkgSig bundle conversionRead pkg ->
                  UnaryHistory conversionRead /\ Cont candidate snEndpoint socket /\
                    Cont socket checkerBudget conversionRead /\
                      PkgSig bundle conversionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro _candidateUnary _snEndpointUnary socketUnary checkerBudgetUnary candidateEndpointSocket
    socketCheckerConversion conversionPkg
  have conversionUnary : UnaryHistory conversionRead :=
    unary_cont_closed socketUnary checkerBudgetUnary socketCheckerConversion
  exact
    ⟨conversionUnary, candidateEndpointSocket, socketCheckerConversion, conversionPkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
