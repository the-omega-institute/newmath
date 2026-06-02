import BEDC.Derived.HyperspaceUp.TasteGate

namespace BEDC.Derived.HyperspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HyperspaceCarrierObligations [AskSetup] [PackageSetup]
    {X K0 K1 N0 N1 D0 D1 R Hs C P M replayRead localRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HyperspaceCarrier X K0 K1 N0 N1 D0 D1 R Hs C P M bundle pkg ->
      Cont Hs C replayRead ->
        Cont replayRead M localRead ->
          PkgSig bundle M pkg ->
            PkgSig bundle localRead pkg ->
              UnaryHistory X ∧ UnaryHistory K0 ∧ UnaryHistory K1 ∧
                UnaryHistory N0 ∧ UnaryHistory N1 ∧ UnaryHistory D0 ∧
                  UnaryHistory D1 ∧ UnaryHistory R ∧ UnaryHistory Hs ∧
                    UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory M ∧
                      UnaryHistory replayRead ∧ UnaryHistory localRead ∧
                        PkgSig bundle P pkg ∧ PkgSig bundle M pkg ∧
                          PkgSig bundle localRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier replayRoute localRoute localPkg localReadPkg
  obtain ⟨xUnary, k0Unary, k1Unary, n0Unary, n1Unary, d0Unary, d1Unary, rUnary,
    hsUnary, cUnary, pUnary, mUnary, provenancePkg⟩ := carrier
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed hsUnary cUnary replayRoute
  have localUnary : UnaryHistory localRead :=
    unary_cont_closed replayUnary mUnary localRoute
  exact
    ⟨xUnary, k0Unary, k1Unary, n0Unary, n1Unary, d0Unary, d1Unary, rUnary,
      hsUnary, cUnary, pUnary, mUnary, replayUnary, localUnary, provenancePkg,
      localPkg, localReadPkg⟩

end BEDC.Derived.HyperspaceUp
