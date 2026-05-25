import BEDC.Derived.LocatedSupremumUp.Carrier

namespace BEDC.Derived.LocatedSupremumUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LocatedSupremumCarrier_monotone_sequence_handoff [AskSetup] [PackageSetup]
    {L U A W R E H C P N sourceRead upperRead lowerRead sharedRead bracketRead handoffRead
      realRead exportedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedSupremumCarrier L U A W R E H C P N bundle pkg →
      UnaryHistory L →
        UnaryHistory U →
          Cont L U sourceRead →
            Cont U W upperRead →
              Cont A W lowerRead →
                Cont upperRead lowerRead sharedRead →
                  Cont W A bracketRead →
                    Cont bracketRead R handoffRead →
                      Cont handoffRead E realRead →
                        Cont sourceRead realRead exportedRead →
                          PkgSig bundle sharedRead pkg →
                            PkgSig bundle realRead pkg →
                              PkgSig bundle exportedRead pkg →
                                UnaryHistory sourceRead ∧ UnaryHistory upperRead ∧
                                  UnaryHistory lowerRead ∧ UnaryHistory sharedRead ∧
                                    UnaryHistory bracketRead ∧ UnaryHistory handoffRead ∧
                                      UnaryHistory realRead ∧ UnaryHistory exportedRead ∧
                                        hsame L U ∧ PkgSig bundle P pkg ∧
                                          PkgSig bundle exportedRead pkg := by
  -- BEDC touchpoint anchor: LocatedSupremumCarrier BHist ProbeBundle Pkg Cont UnaryHistory hsame
  intro carrier sourceUnary upperUnary sourceRoute upperRoute lowerRoute sharedRoute
    bracketRoute handoffRoute realRoute exportedRoute _sharedPkg _realPkg exportedPkg
  have rootUnary : UnaryHistory R := carrier.left
  have lowerUnary : UnaryHistory A := carrier.right.left
  have carrierRoute : Cont R A E := carrier.right.right.left
  have hLU : hsame L U := carrier.right.right.right.left
  have windowUnary : UnaryHistory W := carrier.right.right.right.right.left
  have pkgSig : PkgSig bundle P pkg :=
    carrier.right.right.right.right.right.right.right.left
  have realSealUnary : UnaryHistory E :=
    unary_cont_closed rootUnary lowerUnary carrierRoute
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed sourceUnary upperUnary sourceRoute
  have upperReadUnary : UnaryHistory upperRead :=
    unary_cont_closed upperUnary windowUnary upperRoute
  have lowerReadUnary : UnaryHistory lowerRead :=
    unary_cont_closed lowerUnary windowUnary lowerRoute
  have sharedReadUnary : UnaryHistory sharedRead :=
    unary_cont_closed upperReadUnary lowerReadUnary sharedRoute
  have bracketReadUnary : UnaryHistory bracketRead :=
    unary_cont_closed windowUnary lowerUnary bracketRoute
  have handoffReadUnary : UnaryHistory handoffRead :=
    unary_cont_closed bracketReadUnary rootUnary handoffRoute
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed handoffReadUnary realSealUnary realRoute
  have exportedReadUnary : UnaryHistory exportedRead :=
    unary_cont_closed sourceReadUnary realReadUnary exportedRoute
  exact
    ⟨sourceReadUnary, upperReadUnary, lowerReadUnary, sharedReadUnary, bracketReadUnary,
      handoffReadUnary, realReadUnary, exportedReadUnary, hLU, pkgSig, exportedPkg⟩

end BEDC.Derived.LocatedSupremumUp
