import BEDC.Derived.ContinuationMonadUp

namespace BEDC.Derived.ContinuationMonadUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ContinuationMonadCarrier_root_formal_route_budget_exhaustion [AskSetup] [PackageSetup]
    {A B C f g u H K L N rootRead formalRead budgetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationMonadCarrier A B C f g u H K L N ->
      Cont L N rootRead ->
        Cont rootRead N formalRead ->
          Cont formalRead N budgetRead ->
            PkgSig bundle budgetRead pkg ->
              UnaryHistory A ∧ UnaryHistory B ∧ UnaryHistory C ∧ UnaryHistory f ∧
                UnaryHistory g ∧ UnaryHistory u ∧ UnaryHistory K ∧ UnaryHistory L ∧
                  UnaryHistory N ∧ UnaryHistory rootRead ∧ UnaryHistory formalRead ∧
                    UnaryHistory budgetRead ∧ Cont A f B ∧ Cont B g C ∧
                      Cont f g K ∧ Cont K u L ∧ Cont L N rootRead ∧
                        Cont rootRead N formalRead ∧ Cont formalRead N budgetRead ∧
                          hsame N L ∧ PkgSig bundle budgetRead pkg ∧
                            SemanticNameCert
                              (fun row : BHist => hsame row budgetRead ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row budgetRead ∧ Cont formalRead N budgetRead)
                              (fun row : BHist =>
                                hsame row budgetRead ∧ PkgSig bundle budgetRead pkg)
                              hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier rootRoute formalRoute budgetRoute budgetPkg
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
  have unaryRootRead : UnaryHistory rootRead :=
    unary_cont_closed unaryL unaryN rootRoute
  have unaryFormalRead : UnaryHistory formalRead :=
    unary_cont_closed unaryRootRead unaryN formalRoute
  have unaryBudgetRead : UnaryHistory budgetRead :=
    unary_cont_closed unaryFormalRead unaryN budgetRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row budgetRead ∧ UnaryHistory row)
        (fun row : BHist => hsame row budgetRead ∧ Cont formalRead N budgetRead)
        (fun row : BHist => hsame row budgetRead ∧ PkgSig bundle budgetRead pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro budgetRead ⟨hsame_refl budgetRead, unaryBudgetRead⟩
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
            ⟨hsame_trans (hsame_symm same) source.left,
              unary_transport source.right same⟩
      }
      pattern_sound := by
        intro _row source
        exact ⟨source.left, budgetRoute⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.left, budgetPkg⟩
    }
  exact
    ⟨unaryA, unaryB, unaryC, unaryF, unaryG, unaryU, unaryK, unaryL, unaryN,
      unaryRootRead, unaryFormalRead, unaryBudgetRead, routeB, routeC, routeK, routeL,
      rootRoute, formalRoute, budgetRoute, sameEndpoint, budgetPkg, cert⟩

end BEDC.Derived.ContinuationMonadUp
