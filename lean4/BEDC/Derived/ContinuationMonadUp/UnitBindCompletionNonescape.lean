import BEDC.Derived.ContinuationMonadUp

namespace BEDC.Derived.ContinuationMonadUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ContinuationMonadCarrier_unit_bind_completion_nonescape [AskSetup] [PackageSetup]
    {A B C f g u H K L N unitRead bindRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationMonadCarrier A B C f g u H K L N ->
      Cont u f unitRead ->
        Cont K N bindRead ->
          Cont bindRead N completionRead ->
            PkgSig bundle completionRead pkg ->
              UnaryHistory A ∧ UnaryHistory B ∧ UnaryHistory C ∧ UnaryHistory f ∧
                UnaryHistory g ∧ UnaryHistory u ∧ UnaryHistory K ∧ UnaryHistory L ∧
                  UnaryHistory unitRead ∧ UnaryHistory bindRead ∧
                    UnaryHistory completionRead ∧ Cont A f B ∧ Cont B g C ∧
                      Cont f g K ∧ Cont K u L ∧ Cont u f unitRead ∧
                        Cont K N bindRead ∧ Cont bindRead N completionRead ∧
                          hsame N L ∧ PkgSig bundle completionRead pkg ∧
                            SemanticNameCert
                              (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
                              (fun row : BHist => hsame row completionRead)
                              (fun row : BHist =>
                                hsame row completionRead ∧ PkgSig bundle completionRead pkg)
                              hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier unitRoute bindRoute completionRoute completionPkg
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
  have unaryCompletionRead : UnaryHistory completionRead :=
    unary_cont_closed unaryBindRead unaryN completionRoute
  have sourceCompletion :
      (fun row : BHist => hsame row completionRead ∧ UnaryHistory row) completionRead := by
    exact ⟨hsame_refl completionRead, unaryCompletionRead⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
        (fun row : BHist => hsame row completionRead)
        (fun row : BHist => hsame row completionRead ∧ PkgSig bundle completionRead pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro completionRead sourceCompletion
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
        exact source.left
      ledger_sound := by
        intro _row source
        exact And.intro source.left completionPkg
    }
  exact
    ⟨unaryA, unaryB, unaryC, unaryF, unaryG, unaryU, unaryK, unaryL, unaryUnitRead,
      unaryBindRead, unaryCompletionRead, routeB, routeC, routeK, routeL, unitRoute,
      bindRoute, completionRoute, sameEndpoint, completionPkg, cert⟩

end BEDC.Derived.ContinuationMonadUp
