import BEDC.Derived.RealPowerSeriesUp

namespace BEDC.Derived.RealPowerSeriesUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealPowerSeriesCarrier_root_coefficient_window_coverage [AskSetup] [PackageSetup]
    {A Z X R W S M E H C P N coeffRead partialRead majorantRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealPowerSeriesCarrier A Z X R W S M E H C P N bundle pkg ->
      Cont A W coeffRead ->
        Cont coeffRead S partialRead ->
          Cont partialRead M majorantRead ->
            PkgSig bundle majorantRead pkg ->
              UnaryHistory A ∧ UnaryHistory W ∧ UnaryHistory S ∧ UnaryHistory M ∧
                UnaryHistory coeffRead ∧ UnaryHistory partialRead ∧
                  UnaryHistory majorantRead ∧ Cont A W coeffRead ∧
                    Cont coeffRead S partialRead ∧ Cont partialRead M majorantRead ∧
                      PkgSig bundle P pkg ∧ PkgSig bundle majorantRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier coeffRoute partialRoute majorantRoute majorantPkg
  obtain ⟨AUnary, _ZUnary, _XUnary, _RUnary, WUnary, SUnary, MUnary, _EUnary,
    _HUnary, _CUnary, _PUnary, _NUnary, _coefficientWindow, _radiusMajorant,
    _majorantEndpoint, carrierPkg⟩ := carrier
  have coeffUnary : UnaryHistory coeffRead :=
    unary_cont_closed AUnary WUnary coeffRoute
  have partialUnary : UnaryHistory partialRead :=
    unary_cont_closed coeffUnary SUnary partialRoute
  have majorantUnary : UnaryHistory majorantRead :=
    unary_cont_closed partialUnary MUnary majorantRoute
  exact
    ⟨AUnary, WUnary, SUnary, MUnary, coeffUnary, partialUnary, majorantUnary,
      coeffRoute, partialRoute, majorantRoute, carrierPkg, majorantPkg⟩

end BEDC.Derived.RealPowerSeriesUp
