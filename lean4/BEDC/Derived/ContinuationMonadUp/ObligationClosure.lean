import BEDC.Derived.ContinuationMonadUp

namespace BEDC.Derived.ContinuationMonadUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ContinuationMonadCarrier_obligation_closure
    [AskSetup] [PackageSetup]
    {A B C f g u H K L N unitRead bindRead closure : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationMonadCarrier A B C f g u H K L N ->
      Cont u f unitRead ->
        Cont K N bindRead ->
          Cont bindRead L closure ->
            PkgSig bundle closure pkg ->
              UnaryHistory A ∧ UnaryHistory B ∧ UnaryHistory C ∧ UnaryHistory f ∧
                UnaryHistory g ∧ UnaryHistory u ∧ UnaryHistory K ∧ UnaryHistory L ∧
                  UnaryHistory N ∧ UnaryHistory unitRead ∧ UnaryHistory bindRead ∧
                    UnaryHistory closure ∧ Cont A f B ∧ Cont B g C ∧ Cont f g K ∧
                      Cont K u L ∧ Cont u f unitRead ∧ Cont K N bindRead ∧
                        Cont bindRead L closure ∧ hsame N L ∧ PkgSig bundle closure pkg ∧
                          SemanticNameCert
                            (fun row : BHist => hsame row closure ∧ UnaryHistory row)
                            (fun row : BHist =>
                              Cont bindRead L row ∧ Cont u f unitRead ∧
                                Cont K N bindRead)
                            (fun row : BHist =>
                              hsame row closure ∧ PkgSig bundle closure pkg)
                            hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier unitRoute bindRoute closureRoute closurePkg
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
  have unaryUnitRead : UnaryHistory unitRead :=
    unary_cont_closed unaryU unaryF unitRoute
  have unaryBindRead : UnaryHistory bindRead :=
    unary_cont_closed unaryK unaryN bindRoute
  have unaryClosure : UnaryHistory closure :=
    unary_cont_closed unaryBindRead unaryL closureRoute
  have sourceClosure :
      (fun row : BHist => hsame row closure ∧ UnaryHistory row) closure := by
    exact ⟨hsame_refl closure, unaryClosure⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row closure ∧ UnaryHistory row)
        (fun row : BHist => Cont bindRead L row ∧ Cont u f unitRead ∧ Cont K N bindRead)
        (fun row : BHist => hsame row closure ∧ PkgSig bundle closure pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro closure sourceClosure
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
          exact And.intro (hsame_trans (hsame_symm same) source.left)
            (unary_transport source.right same)
      }
      pattern_sound := by
        intro row source
        cases source.left
        exact ⟨closureRoute, unitRoute, bindRoute⟩
      ledger_sound := by
        intro _row source
        exact And.intro source.left closurePkg
    }
  exact
    ⟨unaryA, unaryB, unaryC, unaryF, unaryG, unaryU, unaryK, unaryL, unaryN,
      unaryUnitRead, unaryBindRead, unaryClosure, routeB, routeC, routeK, routeL,
      unitRoute, bindRoute, closureRoute, sameEndpoint, closurePkg, cert⟩

end BEDC.Derived.ContinuationMonadUp
