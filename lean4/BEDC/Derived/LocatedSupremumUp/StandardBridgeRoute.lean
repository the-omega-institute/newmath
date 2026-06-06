import BEDC.Derived.LocatedSupremumUp.WindowTransport

namespace BEDC.Derived.LocatedSupremumUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LocatedSupremumCarrier_standard_bridge_route [AskSetup] [PackageSetup]
    {L U A W R E H C P N upperRead lowerRead sharedRead transportedRead realRead
      exportedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedSupremumCarrier L U A W R E H C P N bundle pkg →
      UnaryHistory U →
        Cont U W upperRead →
          Cont A W lowerRead →
            Cont upperRead lowerRead sharedRead →
              Cont sharedRead H transportedRead →
                Cont R E realRead →
                  Cont transportedRead realRead exportedRead →
                    PkgSig bundle exportedRead pkg →
                      UnaryHistory upperRead ∧ UnaryHistory lowerRead ∧
                        UnaryHistory sharedRead ∧ UnaryHistory transportedRead ∧
                          UnaryHistory realRead ∧ UnaryHistory exportedRead ∧
                            Cont upperRead lowerRead sharedRead ∧
                              Cont sharedRead H transportedRead ∧ Cont R E realRead ∧
                                Cont transportedRead realRead exportedRead ∧ hsame L U ∧
                                  PkgSig bundle P pkg ∧ PkgSig bundle exportedRead pkg := by
  -- BEDC touchpoint anchor: LocatedSupremumCarrier BHist Cont UnaryHistory hsame ProbeBundle PkgSig
  intro carrier upperUnary upperRoute lowerRoute sharedRoute transportRoute realRoute
    exportRoute exportedPkg
  have rootUnary : UnaryHistory R := carrier.left
  have lowerUnary : UnaryHistory A := carrier.right.left
  have windowUnary : UnaryHistory W := carrier.right.right.right.right.left
  have replayRoute : Cont W R C := carrier.right.right.right.right.right.left
  have replayUnary : UnaryHistory C :=
    unary_cont_closed windowUnary rootUnary replayRoute
  have transportSame : hsame H (append C W) :=
    carrier.right.right.right.right.right.right.left
  have transportUnary : UnaryHistory H :=
    unary_transport (unary_append_closed replayUnary windowUnary) (hsame_symm transportSame)
  have upperReadUnary : UnaryHistory upperRead :=
    unary_cont_closed upperUnary windowUnary upperRoute
  have lowerReadUnary : UnaryHistory lowerRead :=
    unary_cont_closed lowerUnary windowUnary lowerRoute
  have sharedReadUnary : UnaryHistory sharedRead :=
    unary_cont_closed upperReadUnary lowerReadUnary sharedRoute
  have transportedReadUnary : UnaryHistory transportedRead :=
    unary_cont_closed sharedReadUnary transportUnary transportRoute
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed rootUnary (unary_cont_closed rootUnary lowerUnary carrier.right.right.left)
      realRoute
  have exportedReadUnary : UnaryHistory exportedRead :=
    unary_cont_closed transportedReadUnary realReadUnary exportRoute
  exact
    ⟨upperReadUnary, lowerReadUnary, sharedReadUnary, transportedReadUnary, realReadUnary,
      exportedReadUnary, sharedRoute, transportRoute, realRoute, exportRoute,
      carrier.right.right.right.left, carrier.right.right.right.right.right.right.right.left,
      exportedPkg⟩

end BEDC.Derived.LocatedSupremumUp
