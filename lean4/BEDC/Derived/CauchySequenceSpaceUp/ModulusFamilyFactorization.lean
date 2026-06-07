import BEDC.Derived.CauchySequenceSpaceUp

namespace BEDC.Derived.CauchySequenceSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchySequenceSpaceCarrier_modulus_family_factorization [AskSetup] [PackageSetup]
    {family schedule window tolerance completion transport route name modulusRead familyRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchySequenceSpaceCarrier family schedule window tolerance completion transport route name
        bundle pkg ->
      Cont family window modulusRead ->
        Cont modulusRead tolerance familyRead ->
          PkgSig bundle familyRead pkg ->
            UnaryHistory modulusRead ∧ UnaryHistory familyRead ∧
              Cont family window modulusRead ∧ Cont modulusRead tolerance familyRead ∧
                PkgSig bundle route pkg ∧ PkgSig bundle familyRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier modulusRoute familyRoute familyPkg
  obtain ⟨familyUnary, _scheduleUnary, windowUnary, toleranceUnary, _completionUnary,
    _transportUnary, _routeUnary, _nameUnary, _familyScheduleWindow,
    _windowToleranceCompletion, _completionTransportRoute, routePkg, _namePkg⟩ := carrier
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed familyUnary windowUnary modulusRoute
  have familyReadUnary : UnaryHistory familyRead :=
    unary_cont_closed modulusUnary toleranceUnary familyRoute
  exact
    ⟨modulusUnary, familyReadUnary, modulusRoute, familyRoute, routePkg, familyPkg⟩

end BEDC.Derived.CauchySequenceSpaceUp
