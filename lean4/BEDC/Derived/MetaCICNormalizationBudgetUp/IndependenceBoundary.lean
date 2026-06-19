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

theorem MetaCICNormalizationBudgetCarrier_independence_boundary [AskSetup] [PackageSetup]
    {T C E S A P R H Q L N positiveRead refusalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory C ->
      UnaryHistory E ->
        UnaryHistory S ->
          UnaryHistory R ->
            UnaryHistory Q ->
              UnaryHistory L ->
                UnaryHistory N ->
                  Cont C E positiveRead ->
                    Cont R Q refusalRead ->
                      PkgSig bundle L pkg ->
                        PkgSig bundle N pkg ->
                          SemanticNameCert
                              (fun row : BHist =>
                                (hsame row positiveRead ∨ hsame row refusalRead) ∧
                                  UnaryHistory row)
                              (fun row : BHist =>
                                hsame row C ∨ hsame row E ∨ hsame row S ∨ hsame row R ∨
                                  hsame row Q ∨ hsame row L ∨ hsame row N ∨
                                    hsame row positiveRead ∨ hsame row refusalRead)
                              (fun row : BHist =>
                                UnaryHistory row ∧ Cont C E positiveRead ∧
                                  Cont R Q refusalRead ∧ PkgSig bundle L pkg ∧
                                    PkgSig bundle N pkg)
                              hsame ∧
                            UnaryHistory positiveRead ∧ UnaryHistory refusalRead ∧
                              PkgSig bundle L pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro cUnary eUnary _sUnary rUnary qUnary _lUnary _nUnary positiveRoute
    refusalRoute provenancePkg namePkg
  have positiveUnary : UnaryHistory positiveRead :=
    unary_cont_closed cUnary eUnary positiveRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed rUnary qUnary refusalRoute
  have sourcePositive :
      (fun row : BHist =>
        (hsame row positiveRead ∨ hsame row refusalRead) ∧ UnaryHistory row)
        positiveRead := by
    exact ⟨Or.inl (hsame_refl positiveRead), positiveUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row positiveRead ∨ hsame row refusalRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row C ∨ hsame row E ∨ hsame row S ∨ hsame row R ∨ hsame row Q ∨
              hsame row L ∨ hsame row N ∨ hsame row positiveRead ∨
                hsame row refusalRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont C E positiveRead ∧ Cont R Q refusalRead ∧
              PkgSig bundle L pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro positiveRead sourcePositive
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
        constructor
        · cases source.left with
          | inl samePositive =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) samePositive)
          | inr sameRefusal =>
              exact Or.inr (hsame_trans (hsame_symm sameRows) sameRefusal)
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl samePositive =>
          exact Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr (Or.inr (Or.inr (Or.inl samePositive)))))))
      | inr sameRefusal =>
          exact Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr (Or.inr (Or.inr (Or.inr sameRefusal)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, positiveRoute, refusalRoute, provenancePkg, namePkg⟩
  }
  exact ⟨cert, positiveUnary, refusalUnary, provenancePkg, namePkg⟩

end BEDC.Derived.MetaCICNormalizationBudgetUp
