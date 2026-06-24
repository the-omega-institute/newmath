import BEDC.Derived.RegularCauchyCompletionCriterionUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyCompletionCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyCompletionCriterionNameCertObligations [AskSetup] [PackageSetup]
    {R W D M L Q H C P N finiteRead toleranceRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    regularCauchyCompletionCriterionFields
        (RegularCauchyCompletionCriterionUp.mk R W D M L Q H C P N) =
        [R, W, D, M, L, Q, H, C, P, N] ->
      UnaryHistory W ->
        UnaryHistory D ->
          UnaryHistory M ->
            UnaryHistory Q ->
              Cont W D finiteRead ->
                Cont finiteRead M toleranceRead ->
                  Cont toleranceRead Q completionRead ->
                    PkgSig bundle P pkg ->
                      PkgSig bundle N pkg ->
                        SemanticNameCert
                          (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
                          (fun row : BHist => hsame row Q ∨ hsame row completionRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont W D finiteRead ∧
                              Cont finiteRead M toleranceRead ∧
                                Cont toleranceRead Q completionRead ∧
                                  PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                          hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro _fields wUnary dUnary mUnary qUnary finiteRoute toleranceRoute completionRoute
    provenancePkg namePkg
  have finiteUnary : UnaryHistory finiteRead :=
    unary_cont_closed wUnary dUnary finiteRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed finiteUnary mUnary toleranceRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed toleranceUnary qUnary completionRoute
  exact {
    core := {
      carrier_inhabited := Exists.intro completionRead ⟨hsame_refl completionRead, completionUnary⟩
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
      exact Or.inr source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, finiteRoute, toleranceRoute, completionRoute, provenancePkg, namePkg⟩
  }

end BEDC.Derived.RegularCauchyCompletionCriterionUp
