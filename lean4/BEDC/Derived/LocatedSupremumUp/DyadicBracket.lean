import BEDC.Derived.LocatedSupremumUp.Carrier

namespace BEDC.Derived.LocatedSupremumUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LocatedSupremumCarrier_dyadic_bracket [AskSetup] [PackageSetup]
    {L U A W R E H C P N dyadic upperRead lowerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedSupremumCarrier L U A W R E H C P N bundle pkg ->
      UnaryHistory L ->
        Cont W L dyadic ->
          Cont dyadic U upperRead ->
            Cont dyadic A lowerRead ->
              PkgSig bundle upperRead pkg ->
                PkgSig bundle lowerRead pkg ->
                  UnaryHistory W ∧ UnaryHistory L ∧ UnaryHistory U ∧ UnaryHistory dyadic ∧
                    UnaryHistory upperRead ∧ UnaryHistory lowerRead ∧ Cont W L dyadic ∧
                      Cont dyadic U upperRead ∧ Cont dyadic A lowerRead ∧
                        PkgSig bundle upperRead pkg ∧ PkgSig bundle lowerRead pkg := by
  -- BEDC touchpoint anchor: LocatedSupremumCarrier BHist ProbeBundle Pkg Cont UnaryHistory hsame
  intro carrier locatedUnary windowLocatedDyadic dyadicUpperRead dyadicLowerRead upperPkg
    lowerPkg
  have approximationUnary : UnaryHistory A := carrier.right.left
  have locatedUpperSame : hsame L U := carrier.right.right.right.left
  have windowUnary : UnaryHistory W := carrier.right.right.right.right.left
  have upperUnary : UnaryHistory U :=
    unary_transport locatedUnary locatedUpperSame
  have dyadicUnary : UnaryHistory dyadic :=
    unary_cont_closed windowUnary locatedUnary windowLocatedDyadic
  have upperReadUnary : UnaryHistory upperRead :=
    unary_cont_closed dyadicUnary upperUnary dyadicUpperRead
  have lowerReadUnary : UnaryHistory lowerRead :=
    unary_cont_closed dyadicUnary approximationUnary dyadicLowerRead
  exact
    ⟨windowUnary, locatedUnary, upperUnary, dyadicUnary, upperReadUnary, lowerReadUnary,
      windowLocatedDyadic, dyadicUpperRead, dyadicLowerRead, upperPkg, lowerPkg⟩

end BEDC.Derived.LocatedSupremumUp
