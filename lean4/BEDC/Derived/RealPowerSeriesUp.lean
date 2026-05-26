import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RealPowerSeriesUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RealPowerSeriesCarrier [AskSetup] [PackageSetup]
    (A Z X R W S M E H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory A ∧ UnaryHistory Z ∧ UnaryHistory X ∧ UnaryHistory R ∧
    UnaryHistory W ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory E ∧
      UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
        Cont A W S ∧ Cont R S M ∧ Cont M E C ∧ PkgSig bundle P pkg

theorem RealPowerSeriesCarrier_coefficient_window_obligation [AskSetup] [PackageSetup]
    {A Z X R W S M E H C P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealPowerSeriesCarrier A Z X R W S M E H C P N bundle pkg ->
      UnaryHistory A ∧ UnaryHistory W ∧ UnaryHistory S ∧ Cont A W S ∧
        PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier
  obtain ⟨AUnary, _ZUnary, _XUnary, _RUnary, WUnary, SUnary, _MUnary, _EUnary,
    _HUnary, _CUnary, _PUnary, _NUnary, coefficientWindow, _radiusMajorant,
    _majorantEndpoint, pkgSig⟩ := carrier
  exact ⟨AUnary, WUnary, SUnary, coefficientWindow, pkgSig⟩

theorem RealPowerSeriesCarrier_radius_window_handoff [AskSetup] [PackageSetup]
    {A Z X R W S M E H C P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealPowerSeriesCarrier A Z X R W S M E H C P N bundle pkg ->
      UnaryHistory A ∧ UnaryHistory W ∧ UnaryHistory S ∧ UnaryHistory R ∧
        UnaryHistory M ∧ UnaryHistory E ∧ UnaryHistory C ∧ Cont A W S ∧
          Cont R S M ∧ Cont M E C ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier
  obtain ⟨AUnary, _ZUnary, _XUnary, RUnary, WUnary, SUnary, MUnary, EUnary,
    _HUnary, CUnary, _PUnary, _NUnary, coefficientWindow, radiusMajorant,
    majorantEndpoint, pkgSig⟩ := carrier
  exact
    ⟨AUnary, WUnary, SUnary, RUnary, MUnary, EUnary, CUnary, coefficientWindow,
      radiusMajorant, majorantEndpoint, pkgSig⟩

theorem RealPowerSeriesCarrier_coefficient_window_transport [AskSetup] [PackageSetup]
    {A Z X R W S M E H C P N coeffRead partialRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealPowerSeriesCarrier A Z X R W S M E H C P N bundle pkg ->
      Cont A W coeffRead ->
        Cont coeffRead S partialRead ->
          hsame coeffRead W ->
            UnaryHistory A ∧ UnaryHistory W ∧ UnaryHistory S ∧
              UnaryHistory coeffRead ∧ UnaryHistory partialRead ∧
                Cont A W coeffRead ∧ Cont coeffRead S partialRead ∧
                  hsame coeffRead W ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro carrier coeffRoute partialRoute coeffSame
  obtain ⟨AUnary, _ZUnary, _XUnary, _RUnary, WUnary, SUnary, _MUnary, _EUnary,
    _HUnary, _CUnary, _PUnary, _NUnary, _coefficientWindow, _radiusMajorant,
    _majorantEndpoint, pkgSig⟩ := carrier
  have coeffReadUnary : UnaryHistory coeffRead :=
    unary_cont_closed AUnary WUnary coeffRoute
  have partialReadUnary : UnaryHistory partialRead :=
    unary_cont_closed coeffReadUnary SUnary partialRoute
  exact
    ⟨AUnary, WUnary, SUnary, coeffReadUnary, partialReadUnary, coeffRoute,
      partialRoute, coeffSame, pkgSig⟩

theorem RealPowerSeriesCarrier_majorant_regseqrat_budget [AskSetup] [PackageSetup]
    {A Z X R W S M E H C P N regBudget endpointRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealPowerSeriesCarrier A Z X R W S M E H C P N bundle pkg ->
      Cont S M regBudget ->
        Cont regBudget E endpointRead ->
          PkgSig bundle regBudget pkg ->
            PkgSig bundle endpointRead pkg ->
              UnaryHistory A ∧ UnaryHistory R ∧ UnaryHistory W ∧ UnaryHistory S ∧
                UnaryHistory M ∧ UnaryHistory E ∧ UnaryHistory regBudget ∧
                  UnaryHistory endpointRead ∧ Cont A W S ∧ Cont R S M ∧
                    Cont S M regBudget ∧ Cont regBudget E endpointRead ∧
                      PkgSig bundle P pkg ∧ PkgSig bundle regBudget pkg ∧
                        PkgSig bundle endpointRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier budgetRoute endpointRoute budgetPkg endpointPkg
  obtain ⟨AUnary, _ZUnary, _XUnary, RUnary, WUnary, SUnary, MUnary, EUnary,
    _HUnary, _CUnary, _PUnary, _NUnary, coefficientWindow, radiusMajorant,
    _majorantEndpoint, pkgSig⟩ := carrier
  have budgetUnary : UnaryHistory regBudget :=
    unary_cont_closed SUnary MUnary budgetRoute
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed budgetUnary EUnary endpointRoute
  exact
    ⟨AUnary, RUnary, WUnary, SUnary, MUnary, EUnary, budgetUnary, endpointUnary,
      coefficientWindow, radiusMajorant, budgetRoute, endpointRoute, pkgSig, budgetPkg,
      endpointPkg⟩

end BEDC.Derived.RealPowerSeriesUp
