import BEDC.Derived.ContinuationMonadUp

namespace BEDC.Derived.ContinuationMonadUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ContinuationMonadCarrier_root_public_refusal_totality [AskSetup] [PackageSetup]
    {A B C f g u H K L N category generator unitRead bindRead publicRead refusal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationMonadCarrier A B C f g u H K L N ->
      Cont L N category ->
        Cont category K generator ->
          Cont u N unitRead ->
            Cont K L bindRead ->
              Cont generator unitRead publicRead ->
                Cont K N refusal ->
                  PkgSig bundle refusal pkg ->
                    UnaryHistory A ∧ UnaryHistory B ∧ UnaryHistory C ∧
                      UnaryHistory f ∧ UnaryHistory g ∧ UnaryHistory u ∧
                        UnaryHistory K ∧ UnaryHistory L ∧ UnaryHistory N ∧
                          UnaryHistory category ∧ UnaryHistory generator ∧
                            UnaryHistory unitRead ∧ UnaryHistory bindRead ∧
                              UnaryHistory publicRead ∧ UnaryHistory refusal ∧
                                Cont A f B ∧ Cont B g C ∧ Cont f g K ∧
                                  Cont K u L ∧ Cont L N category ∧
                                    Cont category K generator ∧ Cont u N unitRead ∧
                                      Cont K L bindRead ∧
                                        Cont generator unitRead publicRead ∧
                                          Cont K N refusal ∧ hsame N L ∧
                                            PkgSig bundle refusal pkg ∧
                                              SemanticNameCert
                                                (fun row : BHist =>
                                                  hsame row refusal ∧ UnaryHistory row)
                                                (fun row : BHist =>
                                                  Cont K N row ∧
                                                    Cont generator unitRead publicRead)
                                                (fun row : BHist =>
                                                  hsame row refusal ∧
                                                    PkgSig bundle refusal pkg)
                                                hsame := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier categoryRoute generatorRoute unitRoute bindRoute publicRoute refusalRoute
    refusalPkg
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
  have unaryBindRead : UnaryHistory bindRead :=
    unary_cont_closed unaryK unaryL bindRoute
  have unaryPublicRead : UnaryHistory publicRead :=
    unary_cont_closed unaryGenerator unaryUnitRead publicRoute
  have unaryRefusal : UnaryHistory refusal :=
    unary_cont_closed unaryK unaryN refusalRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row refusal ∧ UnaryHistory row)
        (fun row : BHist => Cont K N row ∧ Cont generator unitRead publicRead)
        (fun row : BHist => hsame row refusal ∧ PkgSig bundle refusal pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro refusal (And.intro (hsame_refl refusal) unaryRefusal)
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
        exact And.intro refusalRoute publicRoute
      ledger_sound := by
        intro _row source
        exact And.intro source.left refusalPkg
    }
  exact
    ⟨unaryA, unaryB, unaryC, unaryF, unaryG, unaryU, unaryK, unaryL, unaryN,
      unaryCategory, unaryGenerator, unaryUnitRead, unaryBindRead, unaryPublicRead,
      unaryRefusal, routeB, routeC, routeK, routeL, categoryRoute, generatorRoute,
      unitRoute, bindRoute, publicRoute, refusalRoute, sameEndpoint, refusalPkg, cert⟩

end BEDC.Derived.ContinuationMonadUp
