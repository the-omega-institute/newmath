import BEDC.Derived.RegularCauchyWindowFusionUp.NameCertObligations

namespace BEDC.Derived.RegularCauchyWindowFusionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyWindowFusionSharedWindowHandoff [AskSetup] [PackageSetup]
    {R W S D _E _H _C P _N seedWindow regularDyadic fusedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory R ->
      UnaryHistory W ->
        UnaryHistory S ->
          UnaryHistory D ->
            Cont R W seedWindow ->
              Cont S D regularDyadic ->
                Cont seedWindow regularDyadic fusedRead ->
                  PkgSig bundle P pkg ->
                    UnaryHistory seedWindow ∧ UnaryHistory regularDyadic ∧
                      UnaryHistory fusedRead ∧ Cont R W seedWindow ∧
                        Cont S D regularDyadic ∧ Cont seedWindow regularDyadic fusedRead ∧
                          PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro rUnary wUnary sUnary dUnary seedRoute dyadicRoute fusedRoute provenancePkg
  have seedUnary : UnaryHistory seedWindow :=
    unary_cont_closed rUnary wUnary seedRoute
  have regularDyadicUnary : UnaryHistory regularDyadic :=
    unary_cont_closed sUnary dUnary dyadicRoute
  have fusedUnary : UnaryHistory fusedRead :=
    unary_cont_closed seedUnary regularDyadicUnary fusedRoute
  exact
    ⟨seedUnary, regularDyadicUnary, fusedUnary, seedRoute, dyadicRoute, fusedRoute,
      provenancePkg⟩

end BEDC.Derived.RegularCauchyWindowFusionUp
