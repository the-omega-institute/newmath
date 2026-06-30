import BEDC.Derived.RegularCauchyAdditionUp.TasteGate

namespace BEDC.Derived.RegularCauchyAdditionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyAdditionCarrier_window_sum_stability [AskSetup] [PackageSetup]
    {R0 R1 W0 W1 T0 T1 D S E Z H C P N sourceRead endpointRead
      ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyAdditionCarrier R0 R1 W0 W1 T0 T1 D S E Z H C P N bundle pkg ->
      Cont R0 R1 sourceRead ->
        Cont T0 T1 endpointRead ->
          Cont D E ledgerRead ->
            PkgSig bundle ledgerRead pkg ->
              UnaryHistory R0 ∧ UnaryHistory R1 ∧ UnaryHistory T0 ∧
                UnaryHistory T1 ∧ UnaryHistory D ∧ UnaryHistory E ∧
                  UnaryHistory sourceRead ∧ UnaryHistory endpointRead ∧
                    UnaryHistory ledgerRead ∧ Cont R0 R1 sourceRead ∧
                      Cont T0 T1 endpointRead ∧ Cont D E ledgerRead ∧
                        PkgSig bundle P pkg ∧ PkgSig bundle ledgerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier sourceRoute endpointRoute ledgerRoute ledgerSig
  obtain ⟨R0Unary, R1Unary, _W0Unary, _W1Unary, T0Unary, T1Unary, DUnary,
    _SUnary, EUnary, _ZUnary, _HUnary, _CUnary, _PUnary, _NUnary, _R0R1W0,
    _W0W1T0, _T0T1D, _DEH, _HCS, _SZP, provenanceSig, _nameSig⟩ := carrier
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed R0Unary R1Unary sourceRoute
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed T0Unary T1Unary endpointRoute
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed DUnary EUnary ledgerRoute
  exact
    ⟨R0Unary, R1Unary, T0Unary, T1Unary, DUnary, EUnary, sourceReadUnary,
      endpointReadUnary, ledgerReadUnary, sourceRoute, endpointRoute, ledgerRoute,
      provenanceSig, ledgerSig⟩

end BEDC.Derived.RegularCauchyAdditionUp
