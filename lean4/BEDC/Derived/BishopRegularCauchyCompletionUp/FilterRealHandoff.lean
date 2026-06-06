import BEDC.Derived.BishopRegularCauchyCompletionUp

namespace BEDC.Derived.BishopRegularCauchyCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BishopRegularCauchyCompletionFilterRealHandoff [AskSetup] [PackageSetup]
    {endpoint observations regularity tailModulus commonTail transport replay provenance
      localName filterBase filterWindow regularRead sealRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BishopRegularCauchyCompletionCarrier endpoint observations regularity tailModulus
        commonTail transport replay provenance localName bundle pkg ->
      UnaryHistory filterBase ->
        Cont filterBase observations filterWindow ->
          Cont filterWindow regularity regularRead ->
            Cont regularRead endpoint sealRead ->
              Cont sealRead replay realRead ->
                PkgSig bundle realRead pkg ->
                  UnaryHistory observations ∧ UnaryHistory regularity ∧ UnaryHistory endpoint ∧
                    UnaryHistory filterWindow ∧ UnaryHistory regularRead ∧
                      UnaryHistory sealRead ∧ UnaryHistory realRead ∧
                        Cont filterBase observations filterWindow ∧
                          Cont filterWindow regularity regularRead ∧
                            Cont regularRead endpoint sealRead ∧
                              Cont sealRead replay realRead ∧
                                PkgSig bundle provenance pkg ∧
                                  PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BishopRegularCauchyCompletionCarrier BHist ProbeBundle Pkg Cont
  intro carrier filterBaseUnary filterRoute regularRoute sealRoute realRoute realPkg
  obtain ⟨endpointUnary, observationsUnary, regularityUnary, _tailModulusUnary,
    _commonTailUnary, _transportUnary, replayUnary, _provenanceUnary, _localNameUnary,
    provenancePkg, _localNamePkg⟩ := carrier
  have filterWindowUnary : UnaryHistory filterWindow :=
    unary_cont_closed filterBaseUnary observationsUnary filterRoute
  have regularReadUnary : UnaryHistory regularRead :=
    unary_cont_closed filterWindowUnary regularityUnary regularRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed regularReadUnary endpointUnary sealRoute
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed sealReadUnary replayUnary realRoute
  exact
    ⟨observationsUnary, regularityUnary, endpointUnary, filterWindowUnary,
      regularReadUnary, sealReadUnary, realReadUnary, filterRoute, regularRoute, sealRoute,
      realRoute, provenancePkg, realPkg⟩

end BEDC.Derived.BishopRegularCauchyCompletionUp
