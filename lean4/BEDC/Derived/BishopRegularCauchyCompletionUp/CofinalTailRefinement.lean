import BEDC.Derived.BishopRegularCauchyCompletionUp

namespace BEDC.Derived.BishopRegularCauchyCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BishopRegularCauchyCompletionCofinalTailRefinement [AskSetup] [PackageSetup]
    {endpoint observations regularity tailModulus commonTail transport replay provenance
      localName filterBase tailRead _regularRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BishopRegularCauchyCompletionCarrier endpoint observations regularity tailModulus
        commonTail transport replay provenance localName bundle pkg →
      Cont commonTail observations filterBase →
        Cont filterBase regularity tailRead →
          Cont tailRead endpoint sealRead →
            PkgSig bundle sealRead pkg →
              UnaryHistory commonTail ∧ UnaryHistory observations ∧
                UnaryHistory regularity ∧ UnaryHistory filterBase ∧ UnaryHistory tailRead ∧
                  UnaryHistory sealRead ∧ Cont commonTail observations filterBase ∧
                    Cont filterBase regularity tailRead ∧ Cont tailRead endpoint sealRead ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier commonObservations filterRegular tailSeal sealPkg
  obtain ⟨endpointUnary, observationsUnary, regularityUnary, _tailModulusUnary,
    commonTailUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    provenancePkg, _localNamePkg⟩ := carrier
  have filterUnary : UnaryHistory filterBase :=
    unary_cont_closed commonTailUnary observationsUnary commonObservations
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed filterUnary regularityUnary filterRegular
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed tailUnary endpointUnary tailSeal
  exact
    ⟨commonTailUnary, observationsUnary, regularityUnary, filterUnary, tailUnary, sealUnary,
      commonObservations, filterRegular, tailSeal, provenancePkg, sealPkg⟩

end BEDC.Derived.BishopRegularCauchyCompletionUp
