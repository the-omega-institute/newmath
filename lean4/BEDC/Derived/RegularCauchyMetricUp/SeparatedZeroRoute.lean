import BEDC.Derived.RegularCauchyMetricUp
import BEDC.Derived.RegularCauchyMetricUp.ScopedKernelRoute

namespace BEDC.Derived.RegularCauchyMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyMetricCarrier_separated_zero_route [AskSetup] [PackageSetup]
    {R0 R1 W D Q E H C P N zeroRead sealRead scopeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyMetricCarrier R0 R1 W D Q E H C P N bundle pkg →
      Cont W D zeroRead →
        Cont zeroRead E sealRead →
          Cont sealRead P scopeRead →
            PkgSig bundle scopeRead pkg →
              UnaryHistory zeroRead ∧ UnaryHistory sealRead ∧ UnaryHistory scopeRead ∧
                Cont W D zeroRead ∧ Cont zeroRead E sealRead ∧
                  Cont sealRead P scopeRead ∧ PkgSig bundle P pkg ∧
                    PkgSig bundle scopeRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier zeroRoute sealRoute scopeRoute scopePkg
  obtain ⟨_r0Unary, _r1Unary, windowUnary, dyadicUnary, _quotientUnary, equalityUnary,
    _hUnary, _cUnary, provenanceUnary, _nUnary, _pairRoute, _dyadicRoute, _realRoute,
      _structRoute, provenancePkg, _namePkg⟩ := carrier
  have zeroUnary : UnaryHistory zeroRead :=
    unary_cont_closed windowUnary dyadicUnary zeroRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed zeroUnary equalityUnary sealRoute
  have scopeUnary : UnaryHistory scopeRead :=
    unary_cont_closed sealUnary provenanceUnary scopeRoute
  exact
    ⟨zeroUnary, sealUnary, scopeUnary, zeroRoute, sealRoute, scopeRoute, provenancePkg,
      scopePkg⟩

end BEDC.Derived.RegularCauchyMetricUp
