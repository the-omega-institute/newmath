import BEDC.Derived.CauchyFilterCompletionCriterionUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyFilterCompletionCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyFilterCompletionCriterionBasisRoute [AskSetup] [PackageSetup]
    {source filter basis completion separated _route provenance _localCert basisRead completionRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory source ->
      UnaryHistory filter ->
        UnaryHistory basis ->
          UnaryHistory completion ->
            UnaryHistory separated ->
              Cont source filter basisRead ->
                Cont basisRead completion completionRead ->
                  PkgSig bundle provenance pkg ->
                    PkgSig bundle completionRead pkg ->
                      SemanticNameCert
                          (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row source ∨ hsame row filter ∨ hsame row basisRead ∨
                              hsame row completionRead)
                          (fun row : BHist =>
                            hsame row completionRead ∧ PkgSig bundle completionRead pkg)
                          hsame ∧
                        UnaryHistory basisRead ∧ UnaryHistory completionRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro sourceUnary filterUnary _basisUnary completionUnary _separatedUnary basisRoute
    completionRoute _provenancePkg completionPkg
  have basisReadUnary : UnaryHistory basisRead :=
    unary_cont_closed sourceUnary filterUnary basisRoute
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed basisReadUnary completionUnary completionRoute
  have sourceAtCompletion : hsame completionRead completionRead ∧
      UnaryHistory completionRead :=
    ⟨hsame_refl completionRead, completionReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row filter ∨ hsame row basisRead ∨
              hsame row completionRead)
          (fun row : BHist =>
            hsame row completionRead ∧ PkgSig bundle completionRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro completionRead sourceAtCompletion
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
      exact Or.inr (Or.inr (Or.inr source.left))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, completionPkg⟩
  }
  exact ⟨cert, basisReadUnary, completionReadUnary⟩

end BEDC.Derived.CauchyFilterCompletionCriterionUp
