import BEDC.Derived.ContinuationMonadUp

namespace BEDC.Derived.ContinuationMonadUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ContinuationMonadCarrier_route_bridge_boundary [AskSetup] [PackageSetup]
    {A B C f g u H K L N standard boundary : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationMonadCarrier A B C f g u H K L N ->
      Cont L N standard ->
        Cont standard K boundary ->
          PkgSig bundle boundary pkg ->
            UnaryHistory A /\ UnaryHistory B /\ UnaryHistory C /\ UnaryHistory f /\
              UnaryHistory g /\ UnaryHistory u /\ UnaryHistory K /\ UnaryHistory L /\
                UnaryHistory N /\ UnaryHistory standard /\ UnaryHistory boundary /\
                  Cont A f B /\ Cont B g C /\ Cont f g K /\ Cont K u L /\
                    Cont L N standard /\ Cont standard K boundary /\ hsame N L /\
                      PkgSig bundle boundary pkg /\
                        SemanticNameCert
                          (fun row : BHist => hsame row boundary /\ UnaryHistory row)
                          (fun row : BHist => hsame row boundary /\ Cont L N standard)
                          (fun row : BHist => hsame row boundary /\ PkgSig bundle boundary pkg)
                          hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier standardRoute boundaryRoute boundaryPkg
  obtain ⟨unaryA, unaryF, unaryG, unaryU, routeB, routeC, routeK, routeL,
    sameEndpoint⟩ := carrier
  have unaryB : UnaryHistory B :=
    unary_cont_closed unaryA unaryF routeB
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryB unaryG routeC
  have unaryK : UnaryHistory K :=
    unary_cont_closed unaryF unaryG routeK
  have unaryL : UnaryHistory L :=
    unary_cont_closed unaryK unaryU routeL
  have unaryN : UnaryHistory N :=
    unary_transport unaryL (hsame_symm sameEndpoint)
  have unaryStandard : UnaryHistory standard :=
    unary_cont_closed unaryL unaryN standardRoute
  have unaryBoundary : UnaryHistory boundary :=
    unary_cont_closed unaryStandard unaryK boundaryRoute
  have sourceBoundary :
      (fun row : BHist => hsame row boundary /\ UnaryHistory row) boundary := by
    exact ⟨hsame_refl boundary, unaryBoundary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row boundary /\ UnaryHistory row)
        (fun row : BHist => hsame row boundary /\ Cont L N standard)
        (fun row : BHist => hsame row boundary /\ PkgSig bundle boundary pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro boundary sourceBoundary
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other sameRows
          exact hsame_symm sameRows
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other sameRows source
          exact And.intro (hsame_trans (hsame_symm sameRows) source.left)
            (unary_transport source.right sameRows)
      }
      pattern_sound := by
        intro _row source
        exact And.intro source.left standardRoute
      ledger_sound := by
        intro _row source
        exact And.intro source.left boundaryPkg
    }
  exact
    ⟨unaryA, unaryB, unaryC, unaryF, unaryG, unaryU, unaryK, unaryL, unaryN,
      unaryStandard, unaryBoundary, routeB, routeC, routeK, routeL, standardRoute,
      boundaryRoute, sameEndpoint, boundaryPkg, cert⟩

end BEDC.Derived.ContinuationMonadUp
