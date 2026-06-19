import BEDC.Derived.OnticTowerUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.OnticTowerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def OnticTowerClassifier
    (O A S R B L H C P N O' A' S' R' B' L' H' C' P' N' : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist hsame Cont
  hsame O O' ∧ hsame A A' ∧ hsame S S' ∧ hsame R R' ∧ hsame B B' ∧
    hsame L L' ∧ hsame H H' ∧ hsame C C' ∧ hsame P P' ∧ hsame N N' ∧
    hsame L (append A S)

theorem OnticTower_namecert_obligation_surface
    {O A S R B L H C P N O' A' S' R' B' L' H' C' P' N' : BHist} :
    OnticTowerClassifier O A S R B L H C P N O' A' S' R' B' L' H' C' P' N' →
      onticTowerFields (OnticTowerUp.mk O A S R B L H C P N) =
          [O, A, S, R, B, L, H, C, P, N] ∧
        hsame O O' ∧ hsame A A' ∧ hsame S S' ∧ hsame R R' ∧ hsame B B' ∧
        hsame L L' ∧ hsame H H' ∧ hsame C C' ∧ hsame P P' ∧ hsame N N' ∧
        hsame L (append A S) := by
  -- BEDC touchpoint anchor: BHist hsame Cont
  intro classifier
  obtain
    ⟨sameO, sameA, sameS, sameR, sameB, sameL, sameH, sameC, sameP, sameN,
      sameAppend⟩ := classifier
  exact
    ⟨rfl, sameO, sameA, sameS, sameR, sameB, sameL, sameH, sameC, sameP, sameN,
      sameAppend⟩

theorem OnticTower_observer_budget_semantic_name_certificate [AskSetup] [PackageSetup]
    {O A S R B L H C P N provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory O →
      UnaryHistory A →
        UnaryHistory S →
          UnaryHistory R →
            UnaryHistory B →
              UnaryHistory L →
                UnaryHistory H →
                  UnaryHistory C →
                    UnaryHistory P →
                      UnaryHistory N →
                        Cont A S L →
                          PkgSig bundle provenance pkg →
                            PkgSig bundle localName pkg →
                              SemanticNameCert
                                  (fun row : BHist => hsame row B ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row O ∨ hsame row A ∨ hsame row S ∨
                                      hsame row R ∨ hsame row B ∨ hsame row L ∨
                                        hsame row H ∨ hsame row C ∨ hsame row P ∨
                                          hsame row N)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                                      PkgSig bundle localName pkg)
                                  hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro _unaryO _unaryA _unaryS _unaryR unaryB _unaryL _unaryH _unaryC _unaryP
    _unaryN _budgetRoute provenancePkg localNamePkg
  exact {
    core := {
      carrier_inhabited := Exists.intro B ⟨hsame_refl B, unaryB⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, localNamePkg⟩
  }

end BEDC.Derived.OnticTowerUp
