import BEDC.Derived.CauchyCompletionFunctorUp

namespace BEDC.Derived.CauchyCompletionFunctorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyCompletionFunctorPacket_selector_budget_determinacy
    [AskSetup] [PackageSetup]
    {metric regular sealRow monadRow universal classifier transport nameCert endpoint selectorA
      selectorB completionA completionB : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionFunctorPacket metric regular sealRow monadRow universal classifier transport
        nameCert endpoint bundle pkg →
      Cont metric regular selectorA →
        Cont metric regular selectorB →
          Cont selectorA sealRow completionA →
            Cont selectorB sealRow completionB →
              PkgSig bundle completionA pkg →
                PkgSig bundle completionB pkg →
                  hsame selectorA selectorB ∧ hsame completionA completionB ∧
                    UnaryHistory selectorA ∧ UnaryHistory selectorB ∧
                      UnaryHistory completionA ∧ UnaryHistory completionB ∧
                        PkgSig bundle completionA pkg ∧ PkgSig bundle completionB pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory PkgSig
  intro packet metricRegularSelectorA metricRegularSelectorB selectorASealCompletionA
    selectorBSealCompletionB completionAPkg completionBPkg
  obtain ⟨metricUnary, regularUnary, sealUnary, _monadUnary, _universalUnary,
    _classifierUnary, _transportUnary, _nameCertUnary, _endpointUnary, _metricRegularSeal,
    _monadUniversalEndpoint, _classifierTransportNameCert, _endpointPkg⟩ :=
    packet
  have selectorSame : hsame selectorA selectorB :=
    cont_respects_hsame (hsame_refl metric) (hsame_refl regular)
      metricRegularSelectorA metricRegularSelectorB
  have completionSame : hsame completionA completionB :=
    cont_respects_hsame selectorSame (hsame_refl sealRow)
      selectorASealCompletionA selectorBSealCompletionB
  have selectorAUnary : UnaryHistory selectorA :=
    unary_cont_closed metricUnary regularUnary metricRegularSelectorA
  have selectorBUnary : UnaryHistory selectorB :=
    unary_cont_closed metricUnary regularUnary metricRegularSelectorB
  have completionAUnary : UnaryHistory completionA :=
    unary_cont_closed selectorAUnary sealUnary selectorASealCompletionA
  have completionBUnary : UnaryHistory completionB :=
    unary_cont_closed selectorBUnary sealUnary selectorBSealCompletionB
  exact
    ⟨selectorSame, completionSame, selectorAUnary, selectorBUnary, completionAUnary,
      completionBUnary, completionAPkg, completionBPkg⟩

end BEDC.Derived.CauchyCompletionFunctorUp
