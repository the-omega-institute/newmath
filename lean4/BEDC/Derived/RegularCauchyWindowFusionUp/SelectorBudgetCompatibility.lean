import BEDC.Derived.RegularCauchyWindowFusionUp.NameCertObligations

namespace BEDC.Derived.RegularCauchyWindowFusionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyWindowFusionSelectorBudgetCompatibility [AskSetup] [PackageSetup]
    {R W S D E P seedWindow alternateSeed regularDyadic sealMeet named : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory R →
      UnaryHistory W →
        UnaryHistory S →
          UnaryHistory D →
            UnaryHistory E →
              Cont R W seedWindow →
                Cont R W alternateSeed →
                  Cont S D regularDyadic →
                    Cont seedWindow regularDyadic sealMeet →
                      Cont sealMeet E named →
                        PkgSig bundle P pkg →
                          PkgSig bundle named pkg →
                            hsame alternateSeed seedWindow ∧ UnaryHistory alternateSeed ∧
                              UnaryHistory regularDyadic ∧ UnaryHistory sealMeet ∧
                                UnaryHistory named ∧ Cont R W alternateSeed ∧
                                  Cont S D regularDyadic ∧
                                    Cont seedWindow regularDyadic sealMeet ∧
                                      Cont sealMeet E named ∧ PkgSig bundle P pkg ∧
                                        PkgSig bundle named pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame UnaryHistory
  intro rUnary wUnary sUnary dUnary eUnary seedRoute alternateRoute dyadicRoute meetRoute
    namedRoute provenancePkg namedPkg
  have sameSeed : hsame alternateSeed seedWindow :=
    hsame_symm (cont_deterministic seedRoute alternateRoute)
  have alternateUnary : UnaryHistory alternateSeed :=
    unary_cont_closed rUnary wUnary alternateRoute
  have regularDyadicUnary : UnaryHistory regularDyadic :=
    unary_cont_closed sUnary dUnary dyadicRoute
  have sealMeetUnary : UnaryHistory sealMeet :=
    unary_cont_closed (unary_cont_closed rUnary wUnary seedRoute) regularDyadicUnary meetRoute
  have namedUnary : UnaryHistory named :=
    unary_cont_closed sealMeetUnary eUnary namedRoute
  exact
    ⟨sameSeed, alternateUnary, regularDyadicUnary, sealMeetUnary, namedUnary,
      alternateRoute, dyadicRoute, meetRoute, namedRoute, provenancePkg, namedPkg⟩

end BEDC.Derived.RegularCauchyWindowFusionUp
