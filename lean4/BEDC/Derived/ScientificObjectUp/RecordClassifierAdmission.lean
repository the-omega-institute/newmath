import BEDC.Derived.ScientificObjectUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.ScientificObjectUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ScientificObjectRecordClassifierAdmission [AskSetup] [PackageSetup]
    {R K H recordRead classifierRead : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory R →
      UnaryHistory K →
        UnaryHistory H →
          Cont R K recordRead →
            Cont K H classifierRead →
              PkgSig bundle classifierRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row recordRead ∨ hsame row classifierRead)
                    (fun row : BHist =>
                      hsame row R ∨ hsame row K ∨ hsame row H ∨ hsame row recordRead ∨
                        hsame row classifierRead)
                    (fun row : BHist => UnaryHistory row ∧ PkgSig bundle classifierRead pkg)
                    hsame ∧
                  UnaryHistory recordRead ∧ UnaryHistory classifierRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro rUnary kUnary hUnary recordRoute classifierRoute classifierPkg
  have recordUnary : UnaryHistory recordRead :=
    unary_cont_closed rUnary kUnary recordRoute
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed kUnary hUnary classifierRoute
  have source :
      (fun row : BHist => hsame row recordRead ∨ hsame row classifierRead) recordRead := by
    exact Or.inl (hsame_refl recordRead)
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row recordRead ∨ hsame row classifierRead)
          (fun row : BHist =>
            hsame row R ∨ hsame row K ∨ hsame row H ∨ hsame row recordRead ∨
              hsame row classifierRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle classifierRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro recordRead source
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
        intro _row _other sameRows rowSource
        cases rowSource with
        | inl sameRecord =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameRecord)
        | inr sameClassifier =>
            exact Or.inr (hsame_trans (hsame_symm sameRows) sameClassifier)
    }
    pattern_sound := by
      intro _row rowSource
      cases rowSource with
      | inl sameRecord =>
          exact Or.inr (Or.inr (Or.inr (Or.inl sameRecord)))
      | inr sameClassifier =>
          exact Or.inr (Or.inr (Or.inr (Or.inr sameClassifier)))
    ledger_sound := by
      intro _row rowSource
      cases rowSource with
      | inl sameRecord =>
          exact ⟨unary_transport recordUnary (hsame_symm sameRecord), classifierPkg⟩
      | inr sameClassifier =>
          exact ⟨unary_transport classifierUnary (hsame_symm sameClassifier), classifierPkg⟩
  }
  exact ⟨cert, recordUnary, classifierUnary⟩

end BEDC.Derived.ScientificObjectUp
