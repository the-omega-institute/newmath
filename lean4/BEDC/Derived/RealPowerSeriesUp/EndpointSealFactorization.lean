import BEDC.Derived.RealPowerSeriesUp

namespace BEDC.Derived.RealPowerSeriesUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealPowerSeriesCarrier_endpoint_seal_factorization [AskSetup] [PackageSetup]
    {A Z X R W S M E H C P N endpointRead terminalSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealPowerSeriesCarrier A Z X R W S M E H C P N bundle pkg ->
      Cont S M endpointRead ->
        Cont E C terminalSeal ->
          PkgSig bundle endpointRead pkg ->
            PkgSig bundle terminalSeal pkg ->
              UnaryHistory A ∧ UnaryHistory Z ∧ UnaryHistory X ∧ UnaryHistory R ∧
                UnaryHistory W ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory E ∧
                  UnaryHistory C ∧ UnaryHistory endpointRead ∧
                    UnaryHistory terminalSeal ∧ Cont A W S ∧ Cont R S M ∧
                      Cont S M endpointRead ∧ Cont M E C ∧ Cont E C terminalSeal ∧
                        PkgSig bundle P pkg ∧ PkgSig bundle endpointRead pkg ∧
                          PkgSig bundle terminalSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier endpointRoute terminalRoute endpointPkg terminalPkg
  obtain ⟨AUnary, ZUnary, XUnary, RUnary, WUnary, SUnary, MUnary, EUnary,
    _HUnary, CUnary, _PUnary, _NUnary, coefficientWindow, radiusMajorant,
    majorantEndpoint, pkgSig⟩ := carrier
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed SUnary MUnary endpointRoute
  have terminalUnary : UnaryHistory terminalSeal :=
    unary_cont_closed EUnary CUnary terminalRoute
  exact
    ⟨AUnary, ZUnary, XUnary, RUnary, WUnary, SUnary, MUnary, EUnary, CUnary,
      endpointUnary, terminalUnary, coefficientWindow, radiusMajorant, endpointRoute,
      majorantEndpoint, terminalRoute, pkgSig, endpointPkg, terminalPkg⟩

end BEDC.Derived.RealPowerSeriesUp
