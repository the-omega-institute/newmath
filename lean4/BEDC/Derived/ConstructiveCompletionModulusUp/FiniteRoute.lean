import BEDC.Derived.ConstructiveCompletionModulusUp

namespace BEDC.Derived.ConstructiveCompletionModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ConstructiveCompletionModulusCarrier_finite_route [AskSetup] [PackageSetup]
    {source modulus window readback dyadic realSeal transport replay provenance name
      completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ConstructiveCompletionModulusCarrier source modulus window readback dyadic realSeal
        transport replay provenance name bundle pkg ->
      Cont source modulus window ->
        Cont window readback dyadic ->
          Cont dyadic realSeal completionRead ->
            PkgSig bundle completionRead pkg ->
              UnaryHistory source ∧ UnaryHistory modulus ∧ UnaryHistory window ∧
                UnaryHistory readback ∧ UnaryHistory dyadic ∧ UnaryHistory realSeal ∧
                  UnaryHistory completionRead ∧ Cont source modulus window ∧
                    Cont window readback dyadic ∧ Cont dyadic realSeal completionRead ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sourceModulusWindow windowReadbackDyadic dyadicRealSealRead completionPkg
  obtain ⟨sourceUnary, modulusUnary, _windowCarrierUnary, readbackUnary, _dyadicCarrierUnary,
    realSealUnary, _transportUnary, _replayUnary, provenancePkg, _namePkg⟩ := carrier
  have windowUnary : UnaryHistory window :=
    unary_cont_closed sourceUnary modulusUnary sourceModulusWindow
  have dyadicUnary : UnaryHistory dyadic :=
    unary_cont_closed windowUnary readbackUnary windowReadbackDyadic
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed dyadicUnary realSealUnary dyadicRealSealRead
  exact
    ⟨sourceUnary, modulusUnary, windowUnary, readbackUnary, dyadicUnary, realSealUnary,
      completionUnary, sourceModulusWindow, windowReadbackDyadic, dyadicRealSealRead,
      provenancePkg, completionPkg⟩

end BEDC.Derived.ConstructiveCompletionModulusUp
