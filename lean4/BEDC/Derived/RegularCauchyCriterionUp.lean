import BEDC.Derived.RegularCauchyCriterionUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegularCauchyCriterionCarrier [AskSetup] [PackageSetup]
    (S R M D Q V A H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory S ∧ UnaryHistory R ∧ UnaryHistory M ∧ UnaryHistory D ∧
    UnaryHistory Q ∧ UnaryHistory V ∧ UnaryHistory A ∧ UnaryHistory H ∧
      UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧ Cont S R M ∧
        Cont M D Q ∧ PkgSig bundle N pkg

theorem RegularCauchyCriterion_namecert_obligations [AskSetup] [PackageSetup]
    {S R M D Q V A H C P N criterionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyCriterionCarrier S R M D Q V A H C P N bundle pkg →
      Cont Q V criterionRead →
        PkgSig bundle criterionRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row criterionRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row S ∨ hsame row R ∨ hsame row M ∨ hsame row D ∨
                  hsame row Q ∨ hsame row V ∨ hsame row criterionRead)
              (fun row : BHist => hsame row criterionRead ∧ PkgSig bundle criterionRead pkg)
              hsame ∧
            UnaryHistory S ∧ UnaryHistory R ∧ UnaryHistory M ∧ UnaryHistory D ∧
              UnaryHistory Q ∧ UnaryHistory V ∧ UnaryHistory criterionRead ∧
                Cont S R M ∧ Cont M D Q ∧ Cont Q V criterionRead ∧
                  PkgSig bundle N pkg ∧ PkgSig bundle criterionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier criterionRoute criterionPkg
  obtain ⟨sUnary, rUnary, mUnary, dUnary, qUnary, vUnary, _aUnary, _hUnary, _cUnary,
    _pUnary, _nUnary, streamReadbackModulus, modulusToleranceCriterion, namePkg⟩ :=
    carrier
  have criterionUnary : UnaryHistory criterionRead :=
    unary_cont_closed qUnary vUnary criterionRoute
  have sourceAtCriterion :
      hsame criterionRead criterionRead ∧ UnaryHistory criterionRead :=
    ⟨hsame_refl criterionRead, criterionUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row criterionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row R ∨ hsame row M ∨ hsame row D ∨
              hsame row Q ∨ hsame row V ∨ hsame row criterionRead)
          (fun row : BHist => hsame row criterionRead ∧ PkgSig bundle criterionRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro criterionRead sourceAtCriterion
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
      exact ⟨source.left, criterionPkg⟩
  }
  exact
    ⟨cert, sUnary, rUnary, mUnary, dUnary, qUnary, vUnary, criterionUnary,
      streamReadbackModulus, modulusToleranceCriterion, criterionRoute, namePkg,
      criterionPkg⟩

end BEDC.Derived.RegularCauchyCriterionUp
