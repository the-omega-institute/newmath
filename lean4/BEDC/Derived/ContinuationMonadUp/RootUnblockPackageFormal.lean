import BEDC.Derived.ContinuationMonadUp

namespace BEDC.Derived.ContinuationMonadUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ContinuationMonadCarrier_root_unblock_package [AskSetup] [PackageSetup]
    {A B C f g u H K L N category generator packageRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationMonadCarrier A B C f g u H K L N ->
      Cont L N category ->
        Cont category N generator ->
          Cont generator L packageRead ->
            PkgSig bundle packageRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row packageRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row packageRead ∧ Cont L N category ∧
                      Cont category N generator)
                  (fun row : BHist =>
                    hsame row packageRead ∧ Cont generator L packageRead ∧
                      PkgSig bundle packageRead pkg)
                  hsame ∧
                UnaryHistory A ∧ UnaryHistory B ∧ UnaryHistory C ∧ UnaryHistory K ∧
                  UnaryHistory L ∧ UnaryHistory category ∧ UnaryHistory generator ∧
                    UnaryHistory packageRead ∧ Cont A f B ∧ Cont B g C ∧
                      Cont f g K ∧ Cont K u L ∧ Cont L N category ∧
                        Cont category N generator ∧ Cont generator L packageRead ∧
                          hsame N L ∧ PkgSig bundle packageRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier categoryRoute generatorRoute packageRoute packagePkg
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
  have unaryPackageRead : UnaryHistory packageRead :=
    unary_cont_closed unaryGenerator unaryL packageRoute
  have sourcePackage :
      (fun row : BHist => hsame row packageRead ∧ UnaryHistory row) packageRead := by
    exact ⟨hsame_refl packageRead, unaryPackageRead⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row packageRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row packageRead ∧ Cont L N category ∧ Cont category N generator)
          (fun row : BHist =>
            hsame row packageRead ∧ Cont generator L packageRead ∧
              PkgSig bundle packageRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro packageRead sourcePackage
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
        exact ⟨source.left, categoryRoute, generatorRoute⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.left, packageRoute, packagePkg⟩
    }
  exact
    ⟨cert, unaryA, unaryB, unaryC, unaryK, unaryL, unaryCategory, unaryGenerator,
      unaryPackageRead, routeB, routeC, routeK, routeL, categoryRoute, generatorRoute,
      packageRoute, sameEndpoint, packagePkg⟩

theorem ContinuationMonadCarrier_root_downstream_unblock_package [AskSetup] [PackageSetup]
    {A B C f g u H K L N unitRead bindRead categoryRead generatorRead surface : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationMonadCarrier A B C f g u H K L N ->
      Cont u N unitRead ->
        Cont K L bindRead ->
          Cont L N categoryRead ->
            Cont categoryRead bindRead generatorRead ->
              Cont generatorRead unitRead surface ->
                PkgSig bundle surface pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row surface ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row surface ∧ Cont generatorRead unitRead surface)
                      (fun row : BHist =>
                        hsame row surface ∧ PkgSig bundle surface pkg)
                      hsame ∧
                    UnaryHistory A ∧ UnaryHistory B ∧ UnaryHistory C ∧
                      UnaryHistory K ∧ UnaryHistory L ∧ UnaryHistory unitRead ∧
                        UnaryHistory bindRead ∧ UnaryHistory categoryRead ∧
                          UnaryHistory generatorRead ∧ UnaryHistory surface ∧
                            hsame N L := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier unitRoute bindRoute categoryRoute generatorRoute surfaceRoute surfacePkg
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
    unary_cont_closed unaryU unaryN unitRoute
  have unaryBindRead : UnaryHistory bindRead :=
    unary_cont_closed unaryK unaryL bindRoute
  have unaryCategoryRead : UnaryHistory categoryRead :=
    unary_cont_closed unaryL unaryN categoryRoute
  have unaryGeneratorRead : UnaryHistory generatorRead :=
    unary_cont_closed unaryCategoryRead unaryBindRead generatorRoute
  have unarySurface : UnaryHistory surface :=
    unary_cont_closed unaryGeneratorRead unaryUnitRead surfaceRoute
  have sourceSurface :
      (fun row : BHist => hsame row surface ∧ UnaryHistory row) surface := by
    exact ⟨hsame_refl surface, unarySurface⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row surface ∧ UnaryHistory row)
          (fun row : BHist => hsame row surface ∧ Cont generatorRead unitRead surface)
          (fun row : BHist => hsame row surface ∧ PkgSig bundle surface pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro surface sourceSurface
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
        intro _row source
        exact ⟨source.left, surfaceRoute⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.left, surfacePkg⟩
    }
  exact
    ⟨cert, unaryA, unaryB, unaryC, unaryK, unaryL, unaryUnitRead, unaryBindRead,
      unaryCategoryRead, unaryGeneratorRead, unarySurface, sameEndpoint⟩

end BEDC.Derived.ContinuationMonadUp
