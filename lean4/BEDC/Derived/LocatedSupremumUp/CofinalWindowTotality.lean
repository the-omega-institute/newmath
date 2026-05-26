import BEDC.Derived.LocatedSupremumUp.RegSeqRatHandoffRoute
import BEDC.Derived.LocatedSupremumUp.RootUpperLowerWindow

namespace BEDC.Derived.LocatedSupremumUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LocatedSupremumCarrier_cofinal_window_totality [AskSetup] [PackageSetup]
    {L U A W R E H C P N upperRead lowerRead sharedRead bracketRead handoffRead
      terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedSupremumCarrier L U A W R E H C P N bundle pkg ->
      UnaryHistory U ->
        Cont U W upperRead ->
          Cont A W lowerRead ->
            Cont upperRead lowerRead sharedRead ->
              Cont W A bracketRead ->
                Cont bracketRead R handoffRead ->
                  Cont handoffRead E terminalRead ->
                    PkgSig bundle sharedRead pkg ->
                      PkgSig bundle terminalRead pkg ->
                        UnaryHistory upperRead ∧ UnaryHistory lowerRead ∧
                          UnaryHistory sharedRead ∧ UnaryHistory bracketRead ∧
                            UnaryHistory handoffRead ∧ UnaryHistory terminalRead ∧
                              PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: LocatedSupremumCarrier BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier upperUnary upperRoute lowerRoute sharedRoute bracketRoute handoffRoute
    terminalRoute sharedPkg _terminalPkg
  have rootWindow :=
    LocatedSupremumCarrier_root_upper_lower_window carrier upperUnary upperRoute lowerRoute
      sharedRoute sharedPkg
  have handoffWindow :=
    LocatedSupremumCarrier_regseqrat_handoff_route carrier bracketRoute handoffRoute
      terminalRoute
  rcases rootWindow with
    ⟨upperReadUnary, lowerReadUnary, sharedReadUnary, _upperRoute, _lowerRoute, _sharedRoute,
      pkgSig, _sharedPkg⟩
  rcases handoffWindow with
    ⟨bracketUnary, handoffUnary, terminalUnary, _bracketRoute, _handoffRoute, _terminalRoute,
      _pkgSig⟩
  exact
    ⟨upperReadUnary, lowerReadUnary, sharedReadUnary, bracketUnary, handoffUnary, terminalUnary,
      pkgSig⟩

end BEDC.Derived.LocatedSupremumUp
