import BEDC.Derived.ContinuationMonadUp

namespace BEDC.Derived.ContinuationMonadUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ContinuationMonadCarrier_finite_standard_handoff [AskSetup] [PackageSetup]
    {A B C f g u H K L N standard boundary handoff : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationMonadCarrier A B C f g u H K L N ->
      Cont L N standard ->
        Cont standard K boundary ->
          Cont boundary u handoff ->
            PkgSig bundle handoff pkg ->
              UnaryHistory A /\ UnaryHistory B /\ UnaryHistory C /\ UnaryHistory f /\
                UnaryHistory g /\ UnaryHistory u /\ UnaryHistory K /\ UnaryHistory L /\
                  UnaryHistory N /\ UnaryHistory standard /\ UnaryHistory boundary /\
                    UnaryHistory handoff /\ Cont A f B /\ Cont B g C /\ Cont f g K /\
                      Cont K u L /\ Cont L N standard /\ Cont standard K boundary /\
                        Cont boundary u handoff /\ hsame N L /\ PkgSig bundle handoff pkg /\
                          SemanticNameCert
                            (fun row : BHist => hsame row handoff /\ UnaryHistory row)
                            (fun row : BHist => hsame row handoff /\ Cont boundary u handoff)
                            (fun row : BHist => hsame row handoff /\ PkgSig bundle handoff pkg)
                            hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier standardRoute boundaryRoute handoffRoute handoffPkg
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
  have unaryHandoff : UnaryHistory handoff :=
    unary_cont_closed unaryBoundary unaryU handoffRoute
  have sourceHandoff :
      (fun row : BHist => hsame row handoff /\ UnaryHistory row) handoff := by
    exact ⟨hsame_refl handoff, unaryHandoff⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row handoff /\ UnaryHistory row)
        (fun row : BHist => hsame row handoff /\ Cont boundary u handoff)
        (fun row : BHist => hsame row handoff /\ PkgSig bundle handoff pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro handoff sourceHandoff
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
        exact And.intro source.left handoffRoute
      ledger_sound := by
        intro _row source
        exact And.intro source.left handoffPkg
    }
  exact
    ⟨unaryA, unaryB, unaryC, unaryF, unaryG, unaryU, unaryK, unaryL, unaryN,
      unaryStandard, unaryBoundary, unaryHandoff, routeB, routeC, routeK, routeL,
      standardRoute, boundaryRoute, handoffRoute, sameEndpoint, handoffPkg, cert⟩

end BEDC.Derived.ContinuationMonadUp
