import BEDC.Derived.ContinuationMonadUp

namespace BEDC.Derived.ContinuationMonadUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ContinuationMonadCarrier_root_bind_schedule_exhaustion [AskSetup] [PackageSetup]
    {A B C f g u H K L N unitRead bindRead schedule : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationMonadCarrier A B C f g u H K L N →
      Cont u N unitRead →
        Cont K L bindRead →
          Cont unitRead bindRead schedule →
            PkgSig bundle schedule pkg →
              SemanticNameCert
                (fun row : BHist =>
                  ContinuationMonadCarrier A B C f g u H K L N ∧
                    Cont u N unitRead ∧ Cont K L bindRead ∧
                      Cont unitRead bindRead schedule ∧ hsame row schedule)
                (fun row : BHist =>
                  Cont A f B ∧ Cont B g C ∧ Cont f g K ∧ Cont K u L ∧
                    Cont u N unitRead ∧ Cont K L bindRead ∧
                      Cont unitRead bindRead schedule ∧ hsame row schedule)
                (fun row : BHist => UnaryHistory row ∧ hsame N L ∧
                  PkgSig bundle schedule pkg)
                hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier unitRoute bindRoute scheduleRoute schedulePkg
  obtain ⟨unaryA, unaryF, unaryG, unaryU, routeB, routeC, routeK, routeL,
    sameEndpoint⟩ := carrier
  have carrierSource : ContinuationMonadCarrier A B C f g u H K L N :=
    ⟨unaryA, unaryF, unaryG, unaryU, routeB, routeC, routeK, routeL, sameEndpoint⟩
  have unaryK : UnaryHistory K :=
    unary_cont_closed unaryF unaryG routeK
  have unaryL : UnaryHistory L :=
    unary_cont_closed unaryK unaryU routeL
  have unaryN : UnaryHistory N :=
    unary_transport unaryL (hsame_symm sameEndpoint)
  have unaryUnitRead : UnaryHistory unitRead :=
    unary_cont_closed unaryU unaryN unitRoute
  have unaryBindRead : UnaryHistory bindRead :=
    unary_cont_closed unaryK unaryL bindRoute
  have unarySchedule : UnaryHistory schedule :=
    unary_cont_closed unaryUnitRead unaryBindRead scheduleRoute
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro schedule
          ⟨carrierSource, unitRoute, bindRoute, scheduleRoute, hsame_refl schedule⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same source
        exact
          ⟨source.left, source.right.left, source.right.right.left,
            source.right.right.right.left,
            hsame_trans (hsame_symm same) source.right.right.right.right⟩
    }
    pattern_sound := by
      intro _row source
      exact
        ⟨routeB, routeC, routeK, routeL, source.right.left,
          source.right.right.left, source.right.right.right.left,
          source.right.right.right.right⟩
    ledger_sound := by
      intro _row source
      exact
        ⟨unary_transport unarySchedule (hsame_symm source.right.right.right.right),
          sameEndpoint, schedulePkg⟩
  }

end BEDC.Derived.ContinuationMonadUp
