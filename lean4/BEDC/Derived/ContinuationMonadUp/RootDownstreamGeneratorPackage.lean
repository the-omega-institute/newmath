import BEDC.Derived.ContinuationMonadUp

namespace BEDC.Derived.ContinuationMonadUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ContinuationMonadCarrier_root_downstream_generator_package [AskSetup] [PackageSetup]
    {A B C f g u H K L N category generator unitRead bindRead publicRead consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationMonadCarrier A B C f g u H K L N →
      Cont L N category →
        Cont category K generator →
          Cont u N unitRead →
            Cont K L bindRead →
              Cont generator unitRead publicRead →
                Cont publicRead N consumer →
                  PkgSig bundle consumer pkg →
                    UnaryHistory A ∧ UnaryHistory B ∧ UnaryHistory C ∧ UnaryHistory f ∧
                      UnaryHistory g ∧ UnaryHistory u ∧ UnaryHistory K ∧ UnaryHistory L ∧
                        UnaryHistory N ∧ UnaryHistory category ∧ UnaryHistory generator ∧
                          UnaryHistory unitRead ∧ UnaryHistory bindRead ∧
                            UnaryHistory publicRead ∧ UnaryHistory consumer ∧
                              Cont A f B ∧ Cont B g C ∧ Cont f g K ∧ Cont K u L ∧
                                Cont L N category ∧ Cont category K generator ∧
                                  Cont u N unitRead ∧ Cont K L bindRead ∧
                                    Cont generator unitRead publicRead ∧
                                      Cont publicRead N consumer ∧ hsame N L ∧
                                        PkgSig bundle consumer pkg ∧
                                          SemanticNameCert
                                            (fun row : BHist =>
                                              hsame row consumer ∧ UnaryHistory row)
                                            (fun row : BHist =>
                                              Cont publicRead N row ∧
                                                Cont category K generator)
                                            (fun row : BHist =>
                                              hsame row consumer ∧
                                                PkgSig bundle consumer pkg)
                                            hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier categoryRoute generatorRoute unitRoute bindRoute publicRoute consumerRoute
    consumerPkg
  obtain ⟨unaryA, unaryF, unaryG, unaryU, routeB, routeC, routeK, routeL,
    sameEndpoint⟩ := carrier
  have unaryB : UnaryHistory B := unary_cont_closed unaryA unaryF routeB
  have unaryC : UnaryHistory C := unary_cont_closed unaryB unaryG routeC
  have unaryK : UnaryHistory K := unary_cont_closed unaryF unaryG routeK
  have unaryL : UnaryHistory L := unary_cont_closed unaryK unaryU routeL
  have unaryN : UnaryHistory N := unary_transport unaryL (hsame_symm sameEndpoint)
  have categoryUnary : UnaryHistory category := unary_cont_closed unaryL unaryN categoryRoute
  have generatorUnary : UnaryHistory generator :=
    unary_cont_closed categoryUnary unaryK generatorRoute
  have unitUnary : UnaryHistory unitRead := unary_cont_closed unaryU unaryN unitRoute
  have bindUnary : UnaryHistory bindRead := unary_cont_closed unaryK unaryL bindRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed generatorUnary unitUnary publicRoute
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed publicUnary unaryN consumerRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
        (fun row : BHist => Cont publicRead N row ∧ Cont category K generator)
        (fun row : BHist => hsame row consumer ∧ PkgSig bundle consumer pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro consumer ⟨hsame_refl consumer, consumerUnary⟩
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
          exact ⟨hsame_trans (hsame_symm same) source.left,
            unary_transport source.right same⟩
      }
      pattern_sound := by
        intro row source
        exact ⟨cont_result_hsame_transport consumerRoute source.left.symm, generatorRoute⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.left, consumerPkg⟩
    }
  exact
    ⟨unaryA, unaryB, unaryC, unaryF, unaryG, unaryU, unaryK, unaryL, unaryN,
      categoryUnary, generatorUnary, unitUnary, bindUnary, publicUnary, consumerUnary,
      routeB, routeC, routeK, routeL, categoryRoute, generatorRoute, unitRoute, bindRoute,
      publicRoute, consumerRoute, sameEndpoint, consumerPkg, cert⟩

end BEDC.Derived.ContinuationMonadUp
