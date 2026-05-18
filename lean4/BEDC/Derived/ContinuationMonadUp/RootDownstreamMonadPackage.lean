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
    {A B C f g u H K L N unitRead bindRead assocRead generatorRead categoryRead monadRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationMonadCarrier A B C f g u H K L N ->
      Cont u f unitRead ->
        Cont K L bindRead ->
          Cont unitRead bindRead assocRead ->
            Cont L N generatorRead ->
              Cont generatorRead assocRead categoryRead ->
                Cont categoryRead N monadRead ->
                  PkgSig bundle monadRead pkg ->
                    UnaryHistory A ∧ UnaryHistory B ∧ UnaryHistory C ∧ UnaryHistory f ∧
                      UnaryHistory g ∧ UnaryHistory u ∧ UnaryHistory K ∧ UnaryHistory L ∧
                        UnaryHistory N ∧ UnaryHistory unitRead ∧ UnaryHistory bindRead ∧
                          UnaryHistory assocRead ∧ UnaryHistory generatorRead ∧
                            UnaryHistory categoryRead ∧ UnaryHistory monadRead ∧
                              Cont A f B ∧ Cont B g C ∧ Cont f g K ∧ Cont K u L ∧
                                Cont u f unitRead ∧ Cont K L bindRead ∧
                                  Cont unitRead bindRead assocRead ∧
                                    Cont L N generatorRead ∧
                                      Cont generatorRead assocRead categoryRead ∧
                                        Cont categoryRead N monadRead ∧ hsame N L ∧
                                          PkgSig bundle monadRead pkg ∧
                                            SemanticNameCert
                                              (fun row : BHist =>
                                                hsame row monadRead ∧ UnaryHistory row)
                                              (fun row : BHist =>
                                                Cont categoryRead N row ∧
                                                  Cont L N generatorRead)
                                              (fun row : BHist =>
                                                hsame row monadRead ∧
                                                  PkgSig bundle monadRead pkg)
                                              hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier unitRoute bindRoute assocRoute generatorRoute categoryRoute monadRoute
    monadPkg
  obtain ⟨unaryA, unaryF, unaryG, unaryU, routeB, routeC, routeK, routeL,
    sameEndpoint⟩ := carrier
  have unaryB : UnaryHistory B := unary_cont_closed unaryA unaryF routeB
  have unaryC : UnaryHistory C := unary_cont_closed unaryB unaryG routeC
  have unaryK : UnaryHistory K := unary_cont_closed unaryF unaryG routeK
  have unaryL : UnaryHistory L := unary_cont_closed unaryK unaryU routeL
  have unaryN : UnaryHistory N := unary_transport unaryL (hsame_symm sameEndpoint)
  have unaryUnit : UnaryHistory unitRead := unary_cont_closed unaryU unaryF unitRoute
  have unaryBind : UnaryHistory bindRead := unary_cont_closed unaryK unaryL bindRoute
  have unaryAssoc : UnaryHistory assocRead := unary_cont_closed unaryUnit unaryBind assocRoute
  have unaryGenerator : UnaryHistory generatorRead :=
    unary_cont_closed unaryL unaryN generatorRoute
  have unaryCategory : UnaryHistory categoryRead :=
    unary_cont_closed unaryGenerator unaryAssoc categoryRoute
  have unaryMonad : UnaryHistory monadRead :=
    unary_cont_closed unaryCategory unaryN monadRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row monadRead ∧ UnaryHistory row)
        (fun row : BHist => Cont categoryRead N row ∧ Cont L N generatorRead)
        (fun row : BHist => hsame row monadRead ∧ PkgSig bundle monadRead pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro monadRead ⟨hsame_refl monadRead, unaryMonad⟩
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
          ⟨hsame_trans (hsame_symm same) source.left, unary_transport source.right same⟩
    }
    pattern_sound := by
      intro _row source
      exact ⟨cont_result_hsame_transport monadRoute (hsame_symm source.left), generatorRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, monadPkg⟩
  }
  exact
    ⟨unaryA, unaryB, unaryC, unaryF, unaryG, unaryU, unaryK, unaryL, unaryN,
      unaryUnit, unaryBind, unaryAssoc, unaryGenerator, unaryCategory, unaryMonad, routeB,
      routeC, routeK, routeL, unitRoute, bindRoute, assocRoute, generatorRoute,
      categoryRoute, monadRoute, sameEndpoint, monadPkg, cert⟩

end BEDC.Derived.ContinuationMonadUp
