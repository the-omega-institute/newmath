import BEDC.Derived.MetaCICConfluenceDiamondBoundaryUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.MetaCICConfluenceDiamondBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def MetaCICConfluenceDiamondBoundaryCarrier [AskSetup] [PackageSetup]
    (K J R S B O H C P N replay : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg PkgSig UnaryHistory
  UnaryHistory K ∧ UnaryHistory J ∧ UnaryHistory R ∧ UnaryHistory S ∧
    UnaryHistory B ∧ UnaryHistory O ∧ UnaryHistory H ∧ UnaryHistory C ∧
      UnaryHistory P ∧ UnaryHistory N ∧ UnaryHistory replay ∧
        PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem MetaCICConfluenceDiamondBoundaryCarrier_namecert_obligations
    [AskSetup] [PackageSetup]
    {K J R S B O H C P N replay : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICConfluenceDiamondBoundaryCarrier K J R S B O H C P N replay bundle pkg ->
      SemanticNameCert
        (fun row : BHist => hsame row replay ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row K ∨ hsame row J ∨ hsame row R ∨ hsame row S ∨
            hsame row B ∨ hsame row O ∨ hsame row H ∨ hsame row C ∨
              hsame row P ∨ hsame row N ∨ hsame row replay)
        (fun row : BHist => UnaryHistory row ∧ PkgSig bundle P pkg)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg PkgSig UnaryHistory hsame SemanticNameCert
  intro carrier
  obtain ⟨_unaryK, _unaryJ, _unaryR, _unaryS, _unaryB, _unaryO, _unaryH,
    _unaryC, _unaryP, _unaryN, unaryReplay, pkgP, _pkgN⟩ := carrier
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro replay ⟨hsame_refl replay, unaryReplay⟩
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, pkgP⟩
  }

end BEDC.Derived.MetaCICConfluenceDiamondBoundaryUp
