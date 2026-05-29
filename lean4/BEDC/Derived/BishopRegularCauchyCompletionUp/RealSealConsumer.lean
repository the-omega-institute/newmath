import BEDC.Derived.BishopRegularCauchyCompletionUp

namespace BEDC.Derived.BishopRegularCauchyCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BishopRegularCauchyCompletionCarrier_real_seal_consumer [AskSetup] [PackageSetup]
    {endpoint observations regularity tailModulus commonTail transport replay provenance
      localName streamRead regularRead tailRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BishopRegularCauchyCompletionCarrier endpoint observations regularity tailModulus
        commonTail transport replay provenance localName bundle pkg ->
      Cont observations regularity streamRead ->
        Cont streamRead tailModulus regularRead ->
          Cont regularRead commonTail tailRead ->
            Cont tailRead endpoint sealRead ->
              PkgSig bundle sealRead pkg ->
                UnaryHistory observations ∧ UnaryHistory regularity ∧
                  UnaryHistory tailModulus ∧ UnaryHistory commonTail ∧
                    UnaryHistory streamRead ∧ UnaryHistory regularRead ∧
                      UnaryHistory tailRead ∧ UnaryHistory sealRead ∧
                        Cont observations regularity streamRead ∧
                          Cont streamRead tailModulus regularRead ∧
                            Cont regularRead commonTail tailRead ∧
                              Cont tailRead endpoint sealRead ∧
                                PkgSig bundle provenance pkg ∧
                                  PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BishopRegularCauchyCompletionCarrier BHist ProbeBundle Pkg Cont
  intro carrier observationsRegularity streamTail regularCommon tailEndpoint sealPkg
  obtain ⟨endpointUnary, observationsUnary, regularityUnary, tailModulusUnary,
    commonTailUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    provenancePkg, _localNamePkg⟩ := carrier
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed observationsUnary regularityUnary observationsRegularity
  have regularReadUnary : UnaryHistory regularRead :=
    unary_cont_closed streamUnary tailModulusUnary streamTail
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed regularReadUnary commonTailUnary regularCommon
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed tailReadUnary endpointUnary tailEndpoint
  exact
    ⟨observationsUnary, regularityUnary, tailModulusUnary, commonTailUnary, streamUnary,
      regularReadUnary, tailReadUnary, sealReadUnary, observationsRegularity, streamTail,
      regularCommon, tailEndpoint, provenancePkg, sealPkg⟩

end BEDC.Derived.BishopRegularCauchyCompletionUp
