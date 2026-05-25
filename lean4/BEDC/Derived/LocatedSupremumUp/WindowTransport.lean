import BEDC.Derived.LocatedSupremumUp.RootUpperLowerWindow

namespace BEDC.Derived.LocatedSupremumUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LocatedSupremumCarrier_window_transport [AskSetup] [PackageSetup]
    {L U A W R E H C P N upperRead lowerRead sharedRead transportedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedSupremumCarrier L U A W R E H C P N bundle pkg ->
      UnaryHistory U ->
        Cont U W upperRead ->
          Cont A W lowerRead ->
            Cont upperRead lowerRead sharedRead ->
              Cont sharedRead H transportedRead ->
                PkgSig bundle transportedRead pkg ->
                  UnaryHistory sharedRead ∧ UnaryHistory transportedRead ∧
                    Cont upperRead lowerRead sharedRead ∧ Cont sharedRead H transportedRead ∧
                      hsame L U ∧ PkgSig bundle P pkg ∧
                        PkgSig bundle transportedRead pkg := by
  -- BEDC touchpoint anchor: LocatedSupremumCarrier BHist ProbeBundle Pkg Cont UnaryHistory hsame
  intro carrier upperUnary upperRoute lowerRoute sharedRoute transportRoute transportedPkg
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
  have transportedUnary : UnaryHistory transportedRead :=
    unary_cont_closed sharedReadUnary transportUnary transportRoute
  exact
    ⟨sharedReadUnary, transportedUnary, sharedRoute, transportRoute,
      carrier.right.right.right.left, carrier.right.right.right.right.right.right.right.left,
      transportedPkg⟩

end BEDC.Derived.LocatedSupremumUp
