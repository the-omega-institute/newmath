import BEDC.Derived.ContinuationMonadUp

namespace BEDC.Derived.ContinuationMonadUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ContinuationMonadCarrier_root_terminal_readback_coverage [AskSetup] [PackageSetup]
    {A B C f g u H K L N category generator publicRead formalRead terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationMonadCarrier A B C f g u H K L N ->
      Cont L N category ->
        Cont category N generator ->
          Cont L generator publicRead ->
            Cont publicRead N formalRead ->
              Cont formalRead N terminal ->
                PkgSig bundle terminal pkg ->
                  UnaryHistory A ∧ UnaryHistory B ∧ UnaryHistory C ∧ UnaryHistory f ∧
                    UnaryHistory g ∧ UnaryHistory u ∧ UnaryHistory K ∧ UnaryHistory L ∧
                      UnaryHistory category ∧ UnaryHistory generator ∧
                        UnaryHistory publicRead ∧ UnaryHistory formalRead ∧
                          UnaryHistory terminal ∧ Cont A f B ∧ Cont B g C ∧
                            Cont f g K ∧ Cont K u L ∧ Cont L N category ∧
                              Cont category N generator ∧ Cont L generator publicRead ∧
                                Cont publicRead N formalRead ∧ Cont formalRead N terminal ∧
                                  hsame N L ∧ PkgSig bundle terminal pkg ∧
                                    SemanticNameCert
                                      (fun row : BHist =>
                                        hsame row terminal ∧ UnaryHistory row)
                                      (fun row : BHist =>
                                        Cont formalRead N row ∧
                                          Cont publicRead N formalRead ∧
                                            Cont L generator publicRead)
                                      (fun row : BHist =>
                                        hsame row terminal ∧
                                          PkgSig bundle terminal pkg)
                                      hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier categoryRoute generatorRoute publicRoute formalRoute terminalRoute
    terminalPkg
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
    unary_cont_closed unaryCategory unaryN generatorRoute
  have unaryPublicRead : UnaryHistory publicRead :=
    unary_cont_closed unaryL unaryGenerator publicRoute
  have unaryFormalRead : UnaryHistory formalRead :=
    unary_cont_closed unaryPublicRead unaryN formalRoute
  have unaryTerminal : UnaryHistory terminal :=
    unary_cont_closed unaryFormalRead unaryN terminalRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row terminal ∧ UnaryHistory row)
        (fun row : BHist =>
          Cont formalRead N row ∧ Cont publicRead N formalRead ∧
            Cont L generator publicRead)
        (fun row : BHist => hsame row terminal ∧ PkgSig bundle terminal pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro terminal ⟨hsame_refl terminal, unaryTerminal⟩
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
        intro _row source
        exact
          ⟨cont_result_hsame_transport terminalRoute (hsame_symm source.left),
            formalRoute, publicRoute⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.left, terminalPkg⟩
    }
  exact
    ⟨unaryA, unaryB, unaryC, unaryF, unaryG, unaryU, unaryK, unaryL,
      unaryCategory, unaryGenerator, unaryPublicRead, unaryFormalRead, unaryTerminal,
      routeB, routeC, routeK, routeL, categoryRoute, generatorRoute, publicRoute,
      formalRoute, terminalRoute, sameEndpoint, terminalPkg, cert⟩

end BEDC.Derived.ContinuationMonadUp
