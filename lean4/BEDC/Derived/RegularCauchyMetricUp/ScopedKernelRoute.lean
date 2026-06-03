import BEDC.Derived.RegularCauchyMetricUp

namespace BEDC.Derived.RegularCauchyMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyMetricScopedKernelRoute [AskSetup] [PackageSetup]
    {R0 R1 W D Q E H C P N distanceRead quotientRead sealRead scopeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyMetricCarrier R0 R1 W D Q E H C P N bundle pkg →
      Cont W D distanceRead →
        Cont distanceRead Q quotientRead →
          Cont quotientRead E sealRead →
            Cont sealRead P scopeRead →
              PkgSig bundle scopeRead pkg →
                UnaryHistory distanceRead ∧ UnaryHistory quotientRead ∧
                  UnaryHistory sealRead ∧ UnaryHistory scopeRead ∧ Cont W D distanceRead ∧
                    Cont distanceRead Q quotientRead ∧ Cont quotientRead E sealRead ∧
                      Cont sealRead P scopeRead ∧ PkgSig bundle P pkg ∧
                        PkgSig bundle scopeRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier distanceRoute quotientRoute sealRoute scopeRoute scopePkg
  obtain ⟨_r0Unary, _r1Unary, windowUnary, dyadicUnary, quotientUnary, equalityUnary,
    _hUnary, _cUnary, provenanceUnary, _nUnary, _pairRoute, _dyadicRoute, _realRoute,
      _structRoute, provenancePkg, _namePkg⟩ := carrier
  have distanceUnary : UnaryHistory distanceRead :=
    unary_cont_closed windowUnary dyadicUnary distanceRoute
  have quotientReadUnary : UnaryHistory quotientRead :=
    unary_cont_closed distanceUnary quotientUnary quotientRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed quotientReadUnary equalityUnary sealRoute
  have scopeReadUnary : UnaryHistory scopeRead :=
    unary_cont_closed sealReadUnary provenanceUnary scopeRoute
  exact
    ⟨distanceUnary, quotientReadUnary, sealReadUnary, scopeReadUnary, distanceRoute,
      quotientRoute, sealRoute, scopeRoute, provenancePkg, scopePkg⟩

end BEDC.Derived.RegularCauchyMetricUp
