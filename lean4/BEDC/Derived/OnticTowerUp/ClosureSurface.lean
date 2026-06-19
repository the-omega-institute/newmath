import BEDC.Derived.OnticTowerUp.Classifier

namespace BEDC.Derived.OnticTowerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem OnticTower_obligation_closure_surface [AskSetup] [PackageSetup]
    {O A S R B L H C P N O' A' S' R' B' L' H' C' P' N' provenance localName :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    OnticTowerClassifier O A S R B L H C P N O' A' S' R' B' L' H' C' P' N' ->
      UnaryHistory B ->
        PkgSig bundle provenance pkg ->
          PkgSig bundle localName pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row B ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row O ∨ hsame row A ∨ hsame row S ∨ hsame row R ∨
                    hsame row B ∨ hsame row L ∨ hsame row H ∨ hsame row C ∨
                      hsame row P ∨ hsame row N)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle localName pkg)
                hsame ∧ hsame L (append A S) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory SemanticNameCert hsame append
  intro classifier budgetUnary provenancePkg localNamePkg
  obtain ⟨_sameO, _sameA, _sameS, _sameR, _sameB, _sameL, _sameH, _sameC, _sameP,
    _sameN, ledgerAppend⟩ := classifier
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row B ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row O ∨ hsame row A ∨ hsame row S ∨ hsame row R ∨ hsame row B ∨
              hsame row L ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle localName pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro B ⟨hsame_refl B, budgetUnary⟩
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
          intro _row _other sameRows sourceRow
          exact
            ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
              unary_transport sourceRow.right sameRows⟩
      }
      pattern_sound := by
        intro _row sourceRow
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sourceRow.left))))
      ledger_sound := by
        intro _row sourceRow
        exact ⟨sourceRow.right, provenancePkg, localNamePkg⟩
    }
  exact ⟨cert, ledgerAppend⟩

end BEDC.Derived.OnticTowerUp
