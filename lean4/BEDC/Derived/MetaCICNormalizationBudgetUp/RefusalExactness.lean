import BEDC.Derived.MetaCICNormalizationBudgetUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MetaCICNormalizationBudgetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationBudgetCarrier_refusal_exactness [AskSetup] [PackageSetup]
    {T C E S A R Q positiveRead refusalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory T →
      UnaryHistory C →
        UnaryHistory E →
          UnaryHistory S →
            UnaryHistory A →
              UnaryHistory R →
                UnaryHistory Q →
                  Cont T C E →
                    Cont E S positiveRead →
                      Cont R Q refusalRead →
                        PkgSig bundle refusalRead pkg →
                          SemanticNameCert
                              (fun row : BHist => hsame row refusalRead ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row T ∨ hsame row C ∨ hsame row E ∨ hsame row S ∨
                                  hsame row A ∨ hsame row R ∨ hsame row refusalRead)
                              (fun row : BHist =>
                                UnaryHistory row ∧ Cont T C E ∧
                                  Cont E S positiveRead ∧ Cont R Q refusalRead ∧
                                    PkgSig bundle refusalRead pkg)
                              hsame ∧
                            UnaryHistory positiveRead ∧ UnaryHistory refusalRead ∧
                              Cont T C E ∧ Cont E S positiveRead ∧
                                Cont R Q refusalRead ∧ PkgSig bundle refusalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro _tUnary _cUnary eUnary sUnary _aUnary rUnary qUnary candidateRoute positiveRoute
    refusalRoute refusalPkg
  have positiveUnary : UnaryHistory positiveRead :=
    unary_cont_closed eUnary sUnary positiveRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed rUnary qUnary refusalRoute
  have sourceRefusal :
      (fun row : BHist => hsame row refusalRead ∧ UnaryHistory row) refusalRead := by
    exact ⟨hsame_refl refusalRead, refusalUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row refusalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row T ∨ hsame row C ∨ hsame row E ∨ hsame row S ∨ hsame row A ∨
              hsame row R ∨ hsame row refusalRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont T C E ∧ Cont E S positiveRead ∧
              Cont R Q refusalRead ∧ PkgSig bundle refusalRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro refusalRead sourceRefusal
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, candidateRoute, positiveRoute, refusalRoute, refusalPkg⟩
  }
  exact
    ⟨cert, positiveUnary, refusalUnary, candidateRoute, positiveRoute, refusalRoute,
      refusalPkg⟩

end BEDC.Derived.MetaCICNormalizationBudgetUp
