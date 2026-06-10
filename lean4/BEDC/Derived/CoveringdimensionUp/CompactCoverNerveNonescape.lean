import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionCompactCoverNerveNonescape [AskSetup] [PackageSetup]
    {K E C R O L H T P N nerveRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier K E C R O L H T P N bundle pkg ->
      Cont C O nerveRead ->
        PkgSig bundle nerveRead pkg ->
          UnaryHistory K ∧ UnaryHistory E ∧ UnaryHistory C ∧ UnaryHistory O ∧
            UnaryHistory nerveRead ∧ Cont C O nerveRead ∧ PkgSig bundle P pkg ∧
              PkgSig bundle nerveRead pkg := by
  -- BEDC touchpoint anchor: CoveringDimensionCarrier BHist ProbeBundle Pkg Cont PkgSig
  intro carrier coverOrderNerve nervePkg
  obtain ⟨KUnary, EUnary, CUnary, _RUnary, OUnary, _LUnary, _HUnary, _TUnary,
    _PUnary, _NUnary, _compactEpsilonCover, _coverRefinementOrder,
    _orderLebesgueReplay, _transportReplayProvenance, provenancePkg, _localNamePkg⟩ :=
    carrier
  have nerveUnary : UnaryHistory nerveRead :=
    unary_cont_closed CUnary OUnary coverOrderNerve
  exact ⟨KUnary, EUnary, CUnary, OUnary, nerveUnary, coverOrderNerve, provenancePkg,
    nervePkg⟩

end BEDC.Derived.CoveringdimensionUp
