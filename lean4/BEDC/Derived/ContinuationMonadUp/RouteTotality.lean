import BEDC.Derived.ContinuationMonadUp

namespace BEDC.Derived.ContinuationMonadUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ContinuationMonadCarrier_generator_category_route_totality
    [AskSetup] [PackageSetup]
    {A B C f g u H K L N category generator : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationMonadCarrier A B C f g u H K L N ->
      Cont L N category ->
        Cont category K generator ->
          PkgSig bundle generator pkg ->
            UnaryHistory A ∧ UnaryHistory B ∧ UnaryHistory C ∧ UnaryHistory f ∧
              UnaryHistory g ∧ UnaryHistory u ∧ UnaryHistory K ∧ UnaryHistory L ∧
                UnaryHistory N ∧ UnaryHistory category ∧ UnaryHistory generator ∧
                  Cont A f B ∧ Cont B g C ∧ Cont f g K ∧ Cont K u L ∧
                    Cont L N category ∧ Cont category K generator ∧ hsame N L ∧
                      PkgSig bundle generator pkg := by
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
  have unaryCategory : UnaryHistory category :=
    unary_cont_closed unaryL unaryN categoryRoute
  have unaryGenerator : UnaryHistory generator :=
    unary_cont_closed unaryCategory unaryK generatorRoute
  exact
    ⟨unaryA, unaryB, unaryC, unaryF, unaryG, unaryU, unaryK, unaryL, unaryN,
      unaryCategory, unaryGenerator, routeB, routeC, routeK, routeL, categoryRoute,
      generatorRoute, sameEndpoint, generatorPkg⟩

theorem ContinuationMonadCarrier_root_category_generator_namecert_source_lock
    [AskSetup] [PackageSetup]
    {A B C f g u H K L N category generator publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationMonadCarrier A B C f g u H K L N ->
      Cont L N category ->
        Cont category K generator ->
          Cont generator u publicRead ->
            PkgSig bundle publicRead pkg ->
              UnaryHistory A ∧ UnaryHistory B ∧ UnaryHistory C ∧ UnaryHistory f ∧
                UnaryHistory g ∧ UnaryHistory u ∧ UnaryHistory K ∧ UnaryHistory L ∧
                  UnaryHistory N ∧ UnaryHistory category ∧ UnaryHistory generator ∧
                    UnaryHistory publicRead ∧ Cont A f B ∧ Cont B g C ∧
                      Cont f g K ∧ Cont K u L ∧ Cont L N category ∧
                        Cont category K generator ∧ Cont generator u publicRead ∧
                          hsame N L ∧ PkgSig bundle publicRead pkg ∧
                            SemanticNameCert
                              (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row publicRead ∧ Cont L N category ∧
                                  Cont category K generator ∧ Cont generator u publicRead)
                              (fun row : BHist =>
                                hsame row publicRead ∧ PkgSig bundle publicRead pkg)
                              hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier categoryRoute generatorRoute publicRoute publicPkg
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
  have unaryPublicRead : UnaryHistory publicRead :=
    unary_cont_closed unaryGenerator unaryU publicRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row publicRead ∧ Cont L N category ∧ Cont category K generator ∧
            Cont generator u publicRead)
        (fun row : BHist => hsame row publicRead ∧ PkgSig bundle publicRead pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro publicRead (And.intro (hsame_refl publicRead) unaryPublicRead)
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
        exact ⟨source.left, categoryRoute, generatorRoute, publicRoute⟩
      ledger_sound := by
        intro _row source
        exact And.intro source.left publicPkg
    }
  exact
    ⟨unaryA, unaryB, unaryC, unaryF, unaryG, unaryU, unaryK, unaryL, unaryN,
      unaryCategory, unaryGenerator, unaryPublicRead, routeB, routeC, routeK, routeL,
      categoryRoute, generatorRoute, publicRoute, sameEndpoint, publicPkg, cert⟩

theorem ContinuationMonadCarrier_displayed_bind_readback_exhaustion
    [AskSetup] [PackageSetup]
    {A B C f g u H K L N bindRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationMonadCarrier A B C f g u H K L N ->
      Cont K L bindRead ->
        PkgSig bundle bindRead pkg ->
          UnaryHistory A ∧ UnaryHistory B ∧ UnaryHistory C ∧ UnaryHistory f ∧
            UnaryHistory g ∧ UnaryHistory u ∧ UnaryHistory K ∧ UnaryHistory L ∧
              UnaryHistory bindRead ∧ Cont A f B ∧ Cont B g C ∧ Cont f g K ∧
                Cont K u L ∧ Cont K L bindRead ∧ hsame N L ∧
                  PkgSig bundle bindRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory hsame
  intro carrier bindReadRoute bindReadPkg
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
  have unaryBindRead : UnaryHistory bindRead :=
    unary_cont_closed unaryK unaryL bindReadRoute
  exact
    ⟨unaryA, unaryB, unaryC, unaryF, unaryG, unaryU, unaryK, unaryL, unaryBindRead,
      routeB, routeC, routeK, routeL, bindReadRoute, sameEndpoint, bindReadPkg⟩

theorem ContinuationMonadCarrier_root_consumer_nonescape
    [AskSetup] [PackageSetup]
    {A B C f g u H K L N category generator formal consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationMonadCarrier A B C f g u H K L N ->
      Cont L N category ->
        Cont category K generator ->
          Cont generator u formal ->
            Cont formal N consumer ->
              PkgSig bundle consumer pkg ->
                UnaryHistory A ∧ UnaryHistory B ∧ UnaryHistory C ∧ UnaryHistory f ∧
                  UnaryHistory g ∧ UnaryHistory u ∧ UnaryHistory K ∧ UnaryHistory L ∧
                    UnaryHistory N ∧ UnaryHistory category ∧ UnaryHistory generator ∧
                      UnaryHistory formal ∧ UnaryHistory consumer ∧ Cont A f B ∧
                        Cont B g C ∧ Cont f g K ∧ Cont K u L ∧ Cont L N category ∧
                          Cont category K generator ∧ Cont generator u formal ∧
                            Cont formal N consumer ∧ hsame N L ∧
                              PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory hsame
  intro carrier categoryRoute generatorRoute formalRoute consumerRoute consumerPkg
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
  have unaryFormal : UnaryHistory formal :=
    unary_cont_closed unaryGenerator unaryU formalRoute
  have unaryConsumer : UnaryHistory consumer :=
    unary_cont_closed unaryFormal unaryN consumerRoute
  exact
    ⟨unaryA, unaryB, unaryC, unaryF, unaryG, unaryU, unaryK, unaryL, unaryN,
      unaryCategory, unaryGenerator, unaryFormal, unaryConsumer, routeB, routeC,
      routeK, routeL, categoryRoute, generatorRoute, formalRoute, consumerRoute,
      sameEndpoint, consumerPkg⟩

end BEDC.Derived.ContinuationMonadUp
