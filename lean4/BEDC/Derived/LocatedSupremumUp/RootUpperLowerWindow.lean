import BEDC.Derived.LocatedSupremumUp.Carrier

namespace BEDC.Derived.LocatedSupremumUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LocatedSupremumCarrier_root_upper_lower_window [AskSetup] [PackageSetup]
    {L U A W R E H C P N upperRead lowerRead sharedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedSupremumCarrier L U A W R E H C P N bundle pkg ->
      UnaryHistory U ->
        Cont U W upperRead ->
          Cont A W lowerRead ->
            Cont upperRead lowerRead sharedRead ->
              PkgSig bundle sharedRead pkg ->
                UnaryHistory upperRead ∧ UnaryHistory lowerRead ∧ UnaryHistory sharedRead ∧
                  Cont U W upperRead ∧ Cont A W lowerRead ∧
                    Cont upperRead lowerRead sharedRead ∧ PkgSig bundle P pkg ∧
                      PkgSig bundle sharedRead pkg := by
  -- BEDC touchpoint anchor: LocatedSupremumCarrier BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier upperUnary upperRoute lowerRoute sharedRoute sharedPkg
  have lowerUnary : UnaryHistory A := carrier.right.left
  have windowUnary : UnaryHistory W := carrier.right.right.right.right.left
  have pkgSig : PkgSig bundle P pkg :=
    carrier.right.right.right.right.right.right.right.left
  have upperReadUnary : UnaryHistory upperRead :=
    unary_cont_closed upperUnary windowUnary upperRoute
  have lowerReadUnary : UnaryHistory lowerRead :=
    unary_cont_closed lowerUnary windowUnary lowerRoute
  have sharedReadUnary : UnaryHistory sharedRead :=
    unary_cont_closed upperReadUnary lowerReadUnary sharedRoute
  exact
    ⟨upperReadUnary, lowerReadUnary, sharedReadUnary, upperRoute, lowerRoute, sharedRoute,
      pkgSig, sharedPkg⟩

end BEDC.Derived.LocatedSupremumUp
