import BEDC.Derived.ContinuationMonadUp

namespace BEDC.Derived.ContinuationMonadUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ContinuationMonadCarrier_root_generator_category_lock [AskSetup] [PackageSetup]
    {A B C f g u H K L N generatorRead categoryRead locked : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationMonadCarrier A B C f g u H K L N ->
      Cont L N generatorRead ->
        Cont L N categoryRead ->
          hsame generatorRead categoryRead ->
            Cont categoryRead N locked ->
              PkgSig bundle locked pkg ->
                UnaryHistory A ∧ UnaryHistory B ∧ UnaryHistory C ∧ UnaryHistory f ∧
                  UnaryHistory g ∧ UnaryHistory u ∧ UnaryHistory K ∧ UnaryHistory L ∧
                    UnaryHistory N ∧ UnaryHistory generatorRead ∧
                      UnaryHistory categoryRead ∧ UnaryHistory locked ∧
                        Cont A f B ∧ Cont B g C ∧ Cont f g K ∧ Cont K u L ∧
                          Cont L N generatorRead ∧ Cont L N categoryRead ∧
                            Cont categoryRead N locked ∧ hsame generatorRead categoryRead ∧
                              hsame N L ∧ PkgSig bundle locked pkg ∧
                                SemanticNameCert
                                  (fun row : BHist => hsame row locked ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row locked ∧ Cont L N generatorRead ∧
                                      Cont L N categoryRead)
                                  (fun row : BHist =>
                                    hsame row locked ∧ PkgSig bundle locked pkg)
                                  hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier generatorRoute categoryRoute sameGeneratorCategory lockedRoute lockedPkg
  obtain ⟨unaryA, unaryF, unaryG, unaryU, routeB, routeC, routeK, routeL,
    sameEndpoint⟩ := carrier
  have unaryB : UnaryHistory B := unary_cont_closed unaryA unaryF routeB
  have unaryC : UnaryHistory C := unary_cont_closed unaryB unaryG routeC
  have unaryK : UnaryHistory K := unary_cont_closed unaryF unaryG routeK
  have unaryL : UnaryHistory L := unary_cont_closed unaryK unaryU routeL
  have unaryN : UnaryHistory N := unary_transport unaryL (hsame_symm sameEndpoint)
  have unaryGenerator : UnaryHistory generatorRead :=
    unary_cont_closed unaryL unaryN generatorRoute
  have unaryCategory : UnaryHistory categoryRead :=
    unary_cont_closed unaryL unaryN categoryRoute
  have unaryLocked : UnaryHistory locked :=
    unary_cont_closed unaryCategory unaryN lockedRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row locked ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row locked ∧ Cont L N generatorRead ∧ Cont L N categoryRead)
        (fun row : BHist => hsame row locked ∧ PkgSig bundle locked pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro locked ⟨hsame_refl locked, unaryLocked⟩
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
      exact ⟨source.left, generatorRoute, categoryRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, lockedPkg⟩
  }
  exact
    ⟨unaryA, unaryB, unaryC, unaryF, unaryG, unaryU, unaryK, unaryL, unaryN,
      unaryGenerator, unaryCategory, unaryLocked, routeB, routeC, routeK, routeL,
      generatorRoute, categoryRoute, lockedRoute, sameGeneratorCategory, sameEndpoint,
      lockedPkg, cert⟩

end BEDC.Derived.ContinuationMonadUp
