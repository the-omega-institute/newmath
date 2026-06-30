import BEDC.Derived.MetaCICNormalizationBudgetUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
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
    {T C E S A P R H Q L N positiveRead refusalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory T →
      UnaryHistory C →
        UnaryHistory E →
          UnaryHistory S →
            UnaryHistory A →
              UnaryHistory R →
                UnaryHistory H →
                  UnaryHistory Q →
                    Cont T C E →
                      Cont E S positiveRead →
                        Cont R Q refusalRead →
                          PkgSig bundle L pkg →
                            PkgSig bundle refusalRead pkg →
                              SemanticNameCert
                                  (fun row : BHist =>
                                    hsame row refusalRead ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row R ∨ hsame row H ∨ hsame row Q ∨
                                      hsame row refusalRead)
                                  (fun row : BHist =>
                                    hsame row refusalRead ∧ Cont R Q refusalRead ∧
                                      PkgSig bundle refusalRead pkg)
                                  hsame ∧
                                UnaryHistory positiveRead ∧
                                  UnaryHistory refusalRead ∧
                                    Cont T C E ∧ Cont E S positiveRead ∧
                                      Cont R Q refusalRead ∧ PkgSig bundle L pkg ∧
                                        PkgSig bundle refusalRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame SemanticNameCert
  intro _tUnary _cUnary eUnary sUnary _aUnary rUnary _hUnary qUnary candidateRoute
    positiveRoute refusalRoute lPkg refusalPkg
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
            hsame row R ∨ hsame row H ∨ hsame row Q ∨ hsame row refusalRead)
          (fun row : BHist =>
            hsame row refusalRead ∧ Cont R Q refusalRead ∧ PkgSig bundle refusalRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro refusalRead sourceRefusal
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
        exact ⟨hsame_trans (hsame_symm same) source.left, unary_transport source.right same⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr source.left))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, refusalRoute, refusalPkg⟩
  }
  exact
    ⟨cert, positiveUnary, refusalUnary, candidateRoute, positiveRoute, refusalRoute, lPkg,
      refusalPkg⟩

end BEDC.Derived.MetaCICNormalizationBudgetUp
