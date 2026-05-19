import BEDC.Derived.ContinuationMonadUp

namespace BEDC.Derived.ContinuationMonadUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ContinuationMonadCarrier_root_downstream_monad_package [AskSetup] [PackageSetup]
    {A B C f g u H K L N category generator unitRead bindRead publicRead consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationMonadCarrier A B C f g u H K L N ->
      Cont L N category ->
        Cont category K generator ->
          Cont u N unitRead ->
            Cont K L bindRead ->
              Cont generator unitRead publicRead ->
                Cont publicRead N consumer ->
                  PkgSig bundle consumer pkg ->
                    SemanticNameCert
                      (fun row : BHist =>
                        ContinuationMonadCarrier A B C f g u H K L N ∧
                          hsame row consumer)
                      (fun row : BHist =>
                        hsame row consumer ∧ Cont publicRead N row ∧
                          Cont generator unitRead publicRead ∧ Cont K L bindRead ∧
                            Cont u N unitRead)
                      (fun row : BHist =>
                        hsame row consumer ∧ PkgSig bundle consumer pkg)
                      hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier categoryRoute generatorRoute unitRoute bindRoute publicRoute consumerRoute
    consumerPkg
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
  have unaryCategory : UnaryHistory category :=
    unary_cont_closed unaryL unaryN categoryRoute
  have unaryGenerator : UnaryHistory generator :=
    unary_cont_closed unaryCategory unaryK generatorRoute
  have unaryUnitRead : UnaryHistory unitRead :=
    unary_cont_closed unaryU unaryN unitRoute
  have _unaryBindRead : UnaryHistory bindRead :=
    unary_cont_closed unaryK unaryL bindRoute
  have unaryPublicRead : UnaryHistory publicRead :=
    unary_cont_closed unaryGenerator unaryUnitRead publicRoute
  have _unaryConsumer : UnaryHistory consumer :=
    unary_cont_closed unaryPublicRead unaryN consumerRoute
  have carrierSource : ContinuationMonadCarrier A B C f g u H K L N :=
    ⟨unaryA, unaryF, unaryG, unaryU, routeB, routeC, routeK, routeL, sameEndpoint⟩
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro consumer ⟨carrierSource, hsame_refl consumer⟩
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
        exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact
        ⟨source.right, cont_result_hsame_transport consumerRoute (hsame_symm source.right),
          publicRoute, bindRoute, unitRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.right, consumerPkg⟩
  }

end BEDC.Derived.ContinuationMonadUp
