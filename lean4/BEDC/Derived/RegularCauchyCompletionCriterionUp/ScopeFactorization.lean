import BEDC.Derived.RegularCauchyCompletionCriterionUp.RealSealHandoff

namespace BEDC.Derived.RegularCauchyCompletionCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyCompletionCriterionScopeFactorization [AskSetup] [PackageSetup]
    {R W D M L Q H C P N windowRead toleranceRead modulusRead limitRead completionRead
      functorRead recursorRead realRead scopeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyCompletionCriterionCarrier R W D M L Q H C P N bundle pkg ->
      Cont W D windowRead ->
        Cont windowRead R toleranceRead ->
          Cont toleranceRead M modulusRead ->
            Cont modulusRead L limitRead ->
              Cont limitRead Q completionRead ->
                Cont completionRead H functorRead ->
                  Cont functorRead C recursorRead ->
                    Cont recursorRead P realRead ->
                      Cont realRead N scopeRead ->
                        PkgSig bundle scopeRead pkg ->
                          SemanticNameCert
                              (fun row : BHist => hsame row scopeRead ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row R ∨ hsame row W ∨ hsame row D ∨
                                  hsame row M ∨ hsame row L ∨ hsame row Q ∨
                                    hsame row H ∨ hsame row C ∨ hsame row P ∨
                                      hsame row N ∨ hsame row scopeRead)
                              (fun row : BHist =>
                                UnaryHistory row ∧ Cont W D windowRead ∧
                                  Cont windowRead R toleranceRead ∧
                                    Cont toleranceRead M modulusRead ∧
                                      Cont modulusRead L limitRead ∧
                                        Cont limitRead Q completionRead ∧
                                          Cont completionRead H functorRead ∧
                                            Cont functorRead C recursorRead ∧
                                              Cont recursorRead P realRead ∧
                                                Cont realRead N scopeRead ∧
                                                  PkgSig bundle scopeRead pkg)
                              hsame ∧
                            UnaryHistory scopeRead := by
  -- BEDC touchpoint anchor: RegularCauchyCompletionCriterionCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier windowRoute toleranceRoute modulusRoute limitRoute completionRoute
    functorRoute recursorRoute realRoute scopeRoute scopePkg
  obtain ⟨rUnary, wUnary, dUnary, mUnary, lUnary, qUnary, hUnary, cUnary, pUnary,
    nUnary, _pkgP, _pkgN⟩ := carrier
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed wUnary dUnary windowRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed windowUnary rUnary toleranceRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed toleranceUnary mUnary modulusRoute
  have limitUnary : UnaryHistory limitRead :=
    unary_cont_closed modulusUnary lUnary limitRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed limitUnary qUnary completionRoute
  have functorUnary : UnaryHistory functorRead :=
    unary_cont_closed completionUnary hUnary functorRoute
  have recursorUnary : UnaryHistory recursorRead :=
    unary_cont_closed functorUnary cUnary recursorRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed recursorUnary pUnary realRoute
  have scopeUnary : UnaryHistory scopeRead :=
    unary_cont_closed realUnary nUnary scopeRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row scopeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row R ∨ hsame row W ∨ hsame row D ∨ hsame row M ∨ hsame row L ∨
              hsame row Q ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row scopeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W D windowRead ∧ Cont windowRead R toleranceRead ∧
              Cont toleranceRead M modulusRead ∧ Cont modulusRead L limitRead ∧
                Cont limitRead Q completionRead ∧ Cont completionRead H functorRead ∧
                  Cont functorRead C recursorRead ∧ Cont recursorRead P realRead ∧
                    Cont realRead N scopeRead ∧ PkgSig bundle scopeRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro scopeRead ⟨hsame_refl scopeRead, scopeUnary⟩
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, windowRoute, toleranceRoute, modulusRoute, limitRoute,
          completionRoute, functorRoute, recursorRoute, realRoute, scopeRoute, scopePkg⟩
  }
  exact ⟨cert, scopeUnary⟩

end BEDC.Derived.RegularCauchyCompletionCriterionUp
