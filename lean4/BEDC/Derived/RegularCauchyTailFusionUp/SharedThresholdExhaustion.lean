import BEDC.Derived.RegularCauchyTailFusionUp

namespace BEDC.Derived.RegularCauchyTailFusionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyTailFusionCarrier_shared_threshold_exhaustion [AskSetup] [PackageSetup]
    {Q X W D T M R L H C P N thresholdRead diagonalRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyTailFusionCarrier Q X W D T M R L H C P N bundle pkg ->
      Cont T M thresholdRead ->
        Cont thresholdRead R diagonalRead ->
          Cont diagonalRead N sealRead ->
            UnaryHistory M ∧ UnaryHistory thresholdRead ∧ UnaryHistory diagonalRead ∧
              UnaryHistory sealRead ∧ Cont T M thresholdRead ∧
                Cont thresholdRead R diagonalRead ∧ Cont diagonalRead N sealRead ∧
                  hsame L (append R N) ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier thresholdRoute diagonalRoute sealRoute
  obtain ⟨_qUnary, _xUnary, _wUnary, _dUnary, tailUnary, meetUnary, diagonalUnary,
    _sealUnary, _transportUnary, _routeUnary, _provenanceUnary, nameUnary,
    _precisionWindow, _windowTail, _tailMeet, _transportRoute, sealSame, namePkg⟩ :=
    carrier
  have thresholdReadUnary : UnaryHistory thresholdRead :=
    unary_cont_closed tailUnary meetUnary thresholdRoute
  have diagonalReadUnary : UnaryHistory diagonalRead :=
    unary_cont_closed thresholdReadUnary diagonalUnary diagonalRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed diagonalReadUnary nameUnary sealRoute
  exact
    ⟨meetUnary, thresholdReadUnary, diagonalReadUnary, sealReadUnary, thresholdRoute,
      diagonalRoute, sealRoute, sealSame, namePkg⟩

end BEDC.Derived.RegularCauchyTailFusionUp
