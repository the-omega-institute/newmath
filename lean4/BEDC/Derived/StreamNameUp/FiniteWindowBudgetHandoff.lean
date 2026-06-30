import BEDC.Derived.StreamNameUp
import BEDC.FKernel.Package

namespace BEDC.Derived.StreamNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem StreamNameRealRegseqFiniteWindowBudgetHandoff [AskSetup] [PackageSetup]
    {window membership unaryBudget limiter tailBudget dyadicTolerance regseqRead realSeal
      namedRead : BHist}
    {bundle : ProbeBundle BHist} {pkgBundle : ProbeBundle ProbeName} {pkg : Pkg} :
    InBundle window bundle ->
      UnaryHistory window ->
        UnaryHistory membership ->
          UnaryHistory unaryBudget ->
            UnaryHistory dyadicTolerance ->
              UnaryHistory realSeal ->
                Cont window membership limiter ->
                  Cont limiter unaryBudget tailBudget ->
                    Cont tailBudget dyadicTolerance regseqRead ->
                      Cont regseqRead realSeal namedRead ->
                        PkgSig pkgBundle namedRead pkg ->
                          SemanticNameCert
                              (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row window ∨ hsame row membership ∨
                                  hsame row unaryBudget ∨ hsame row limiter ∨
                                    hsame row tailBudget ∨ hsame row regseqRead ∨
                                      hsame row dyadicTolerance ∨ hsame row realSeal ∨
                                        hsame row namedRead)
                              (fun row : BHist =>
                                UnaryHistory row ∧ InBundle window bundle ∧
                                  Cont window membership limiter ∧
                                    Cont limiter unaryBudget tailBudget ∧
                                      Cont tailBudget dyadicTolerance regseqRead ∧
                                        Cont regseqRead realSeal namedRead ∧
                                          PkgSig pkgBundle namedRead pkg)
                              hsame ∧
                            UnaryHistory limiter ∧ UnaryHistory tailBudget ∧
                              UnaryHistory regseqRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle InBundle Pkg PkgSig Cont hsame SemanticNameCert
  intro windowMember windowUnary membershipUnary unaryBudgetUnary dyadicToleranceUnary realSealUnary
    limiterRoute tailBudgetRoute regseqRoute namedRoute namedPkg
  have limiterUnary : UnaryHistory limiter :=
    unary_cont_closed windowUnary membershipUnary limiterRoute
  have tailBudgetUnary : UnaryHistory tailBudget :=
    unary_cont_closed limiterUnary unaryBudgetUnary tailBudgetRoute
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed tailBudgetUnary dyadicToleranceUnary regseqRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed regseqUnary realSealUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row window ∨ hsame row membership ∨ hsame row unaryBudget ∨
              hsame row limiter ∨ hsame row tailBudget ∨ hsame row regseqRead ∨
                hsame row dyadicTolerance ∨ hsame row realSeal ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ InBundle window bundle ∧ Cont window membership limiter ∧
              Cont limiter unaryBudget tailBudget ∧ Cont tailBudget dyadicTolerance regseqRead ∧
                Cont regseqRead realSeal namedRead ∧ PkgSig pkgBundle namedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
      exact Or.inr
        (Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, windowMember, limiterRoute, tailBudgetRoute, regseqRoute, namedRoute,
          namedPkg⟩
  }
  exact ⟨cert, limiterUnary, tailBudgetUnary, regseqUnary, namedUnary⟩

end BEDC.Derived.StreamNameUp
