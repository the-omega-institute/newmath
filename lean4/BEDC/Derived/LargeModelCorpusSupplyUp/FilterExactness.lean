import BEDC.Derived.LargeModelCorpusSupplyUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.LargeModelCorpusSupplyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LargeModelCorpusSupplyFilterExactness [AskSetup] [PackageSetup]
    {R F W I A H K P N sourceRead weightRead inferenceRead auditRead namedRead
      filterRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory R →
      UnaryHistory F →
        UnaryHistory W →
          UnaryHistory I →
            UnaryHistory A →
              UnaryHistory H →
                UnaryHistory K →
                  UnaryHistory P →
                    UnaryHistory N →
                      Cont R F sourceRead →
                        Cont sourceRead W weightRead →
                          Cont weightRead I inferenceRead →
                            Cont inferenceRead A auditRead →
                              Cont auditRead K namedRead →
                                Cont F R filterRead →
                                  PkgSig bundle P pkg →
                                    PkgSig bundle N pkg →
                                      SemanticNameCert
                                          (fun row : BHist =>
                                            hsame row filterRead ∧ UnaryHistory row)
                                          (fun row : BHist =>
                                            hsame row R ∨ hsame row F ∨ hsame row W ∨
                                              hsame row I ∨ hsame row A ∨ hsame row K ∨
                                                hsame row P ∨ hsame row N ∨
                                                  hsame row filterRead)
                                          (fun row : BHist =>
                                            UnaryHistory row ∧ Cont F R filterRead ∧
                                              Cont R F sourceRead ∧
                                                Cont sourceRead W weightRead ∧
                                                  Cont weightRead I inferenceRead ∧
                                                    Cont inferenceRead A auditRead ∧
                                                      PkgSig bundle P pkg)
                                          hsame ∧
                                        UnaryHistory filterRead ∧ UnaryHistory sourceRead ∧
                                          UnaryHistory weightRead ∧ UnaryHistory inferenceRead ∧
                                            UnaryHistory auditRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert UnaryHistory
  intro rUnary fUnary wUnary iUnary aUnary _hUnary _kUnary _pUnary _nUnary sourceRoute
    weightRoute inferenceRoute auditRoute _namedRoute filterRoute provenancePkg _namePkg
  have filterUnary : UnaryHistory filterRead :=
    unary_cont_closed fUnary rUnary filterRoute
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed rUnary fUnary sourceRoute
  have weightUnary : UnaryHistory weightRead :=
    unary_cont_closed sourceUnary wUnary weightRoute
  have inferenceUnary : UnaryHistory inferenceRead :=
    unary_cont_closed weightUnary iUnary inferenceRoute
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed inferenceUnary aUnary auditRoute
  have sourceFilter :
      (fun row : BHist => hsame row filterRead ∧ UnaryHistory row) filterRead := by
    exact ⟨hsame_refl filterRead, filterUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row filterRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row R ∨ hsame row F ∨ hsame row W ∨ hsame row I ∨ hsame row A ∨
              hsame row K ∨ hsame row P ∨ hsame row N ∨ hsame row filterRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont F R filterRead ∧ Cont R F sourceRead ∧
              Cont sourceRead W weightRead ∧ Cont weightRead I inferenceRead ∧
                Cont inferenceRead A auditRead ∧ PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro filterRead sourceFilter
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, filterRoute, sourceRoute, weightRoute, inferenceRoute, auditRoute,
          provenancePkg⟩
  }
  exact ⟨cert, filterUnary, sourceUnary, weightUnary, inferenceUnary, auditUnary⟩

end BEDC.Derived.LargeModelCorpusSupplyUp
