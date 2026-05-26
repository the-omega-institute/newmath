import BEDC.Derived.ContinuationMonadUp

namespace BEDC.Derived.ContinuationMonadUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ContinuationMonadCarrier_root_category_generator_factorization
    [AskSetup] [PackageSetup]
    {A B C f g u H K L N categoryRead generatorRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationMonadCarrier A B C f g u H K L N ->
      Cont K L categoryRead ->
        Cont categoryRead N generatorRead ->
          PkgSig bundle generatorRead pkg ->
            UnaryHistory A ∧ UnaryHistory B ∧ UnaryHistory C ∧ UnaryHistory f ∧
              UnaryHistory g ∧ UnaryHistory u ∧ UnaryHistory K ∧ UnaryHistory L ∧
                UnaryHistory categoryRead ∧ UnaryHistory generatorRead ∧
                  Cont A f B ∧ Cont B g C ∧ Cont f g K ∧ Cont K u L ∧
                    Cont K L categoryRead ∧ Cont categoryRead N generatorRead ∧
                      hsame N L ∧ PkgSig bundle generatorRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory hsame
  intro carrier categoryRoute generatorRoute generatorPkg
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
  have unaryCategoryRead : UnaryHistory categoryRead :=
    unary_cont_closed unaryK unaryL categoryRoute
  have unaryGeneratorRead : UnaryHistory generatorRead :=
    unary_cont_closed unaryCategoryRead unaryN generatorRoute
  exact
    ⟨unaryA, unaryB, unaryC, unaryF, unaryG, unaryU, unaryK, unaryL,
      unaryCategoryRead, unaryGeneratorRead, routeB, routeC, routeK, routeL,
      categoryRoute, generatorRoute, sameEndpoint, generatorPkg⟩

theorem ContinuationMonadCarrier_root_downstream_surface_exactness
    [AskSetup] [PackageSetup]
    {A B C f g u H K L N categoryRead generatorRead unitRead bindRead surface : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationMonadCarrier A B C f g u H K L N ->
      Cont K L categoryRead ->
        Cont categoryRead N generatorRead ->
          Cont u N unitRead ->
            Cont K L bindRead ->
              Cont generatorRead unitRead surface ->
                PkgSig bundle surface pkg ->
                  UnaryHistory A ∧ UnaryHistory B ∧ UnaryHistory C ∧ UnaryHistory f ∧
                    UnaryHistory g ∧ UnaryHistory u ∧ UnaryHistory K ∧ UnaryHistory L ∧
                      UnaryHistory N ∧ UnaryHistory categoryRead ∧
                        UnaryHistory generatorRead ∧ UnaryHistory unitRead ∧
                          UnaryHistory bindRead ∧ UnaryHistory surface ∧
                            Cont A f B ∧ Cont B g C ∧ Cont f g K ∧ Cont K u L ∧
                              Cont K L categoryRead ∧ Cont categoryRead N generatorRead ∧
                                Cont u N unitRead ∧ Cont K L bindRead ∧
                                  Cont generatorRead unitRead surface ∧ hsame N L ∧
                                    PkgSig bundle surface pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory hsame
  intro carrier categoryRoute generatorRoute unitRoute bindRoute surfaceRoute surfacePkg
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
  have unaryCategoryRead : UnaryHistory categoryRead :=
    unary_cont_closed unaryK unaryL categoryRoute
  have unaryGeneratorRead : UnaryHistory generatorRead :=
    unary_cont_closed unaryCategoryRead unaryN generatorRoute
  have unaryUnitRead : UnaryHistory unitRead :=
    unary_cont_closed unaryU unaryN unitRoute
  have unaryBindRead : UnaryHistory bindRead :=
    unary_cont_closed unaryK unaryL bindRoute
  have unarySurface : UnaryHistory surface :=
    unary_cont_closed unaryGeneratorRead unaryUnitRead surfaceRoute
  exact
    ⟨unaryA, unaryB, unaryC, unaryF, unaryG, unaryU, unaryK, unaryL, unaryN,
      unaryCategoryRead, unaryGeneratorRead, unaryUnitRead, unaryBindRead, unarySurface,
      routeB, routeC, routeK, routeL, categoryRoute, generatorRoute, unitRoute, bindRoute,
      surfaceRoute, sameEndpoint, surfacePkg⟩

theorem ContinuationMonadCarrier_root_category_generator_bridge_determinacy
    [AskSetup] [PackageSetup]
    {A B C f g u H K L N categoryRead generatorRead surface : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationMonadCarrier A B C f g u H K L N ->
      Cont K L categoryRead ->
        Cont categoryRead N generatorRead ->
          Cont generatorRead L surface ->
            PkgSig bundle surface pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row surface ∧ UnaryHistory row)
                  (fun row : BHist => hsame row surface)
                  (fun row : BHist => hsame row surface ∧ PkgSig bundle surface pkg)
                  hsame ∧
                UnaryHistory categoryRead ∧ UnaryHistory generatorRead ∧
                  UnaryHistory surface := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame UnaryHistory
  intro carrier categoryRoute generatorRoute surfaceRoute surfacePkg
  obtain ⟨_unaryA, unaryF, unaryG, unaryU, _routeB, _routeC, routeK, routeL,
    sameEndpoint⟩ := carrier
  have unaryK : UnaryHistory K :=
    unary_cont_closed unaryF unaryG routeK
  have unaryL : UnaryHistory L :=
    unary_cont_closed unaryK unaryU routeL
  have unaryN : UnaryHistory N :=
    unary_transport unaryL (hsame_symm sameEndpoint)
  have unaryCategoryRead : UnaryHistory categoryRead :=
    unary_cont_closed unaryK unaryL categoryRoute
  have unaryGeneratorRead : UnaryHistory generatorRead :=
    unary_cont_closed unaryCategoryRead unaryN generatorRoute
  have unarySurface : UnaryHistory surface :=
    unary_cont_closed unaryGeneratorRead unaryL surfaceRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row surface ∧ UnaryHistory row)
          (fun row : BHist => hsame row surface)
          (fun row : BHist => hsame row surface ∧ PkgSig bundle surface pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro surface ⟨hsame_refl surface, unarySurface⟩
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
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.left, surfacePkg⟩
  }
  exact ⟨cert, unaryCategoryRead, unaryGeneratorRead, unarySurface⟩

end BEDC.Derived.ContinuationMonadUp
