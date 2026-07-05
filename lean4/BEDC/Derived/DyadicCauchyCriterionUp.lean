import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History

namespace BEDC.Derived

def DyadicCauchyCriterionUp : Type :=
  Unit

namespace DyadicCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

set_option linter.unusedVariables false in
theorem DyadicCauchyCriterionCarrier_regseqrat_handoff [AskSetup] [PackageSetup]
    {D W T R E H C P N toleranceRead criterionRead regularRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory D -> UnaryHistory W -> UnaryHistory T -> UnaryHistory R ->
      Cont D W toleranceRead -> Cont toleranceRead T criterionRead ->
        Cont criterionRead R regularRead -> PkgSig bundle regularRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row regularRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row D ∨ hsame row W ∨ hsame row T ∨ hsame row R ∨
                  hsame row regularRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont D W toleranceRead ∧
                  Cont toleranceRead T criterionRead ∧ Cont criterionRead R regularRead ∧
                    PkgSig bundle regularRead pkg)
              hsame ∧
            UnaryHistory toleranceRead ∧ UnaryHistory criterionRead ∧
              UnaryHistory regularRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg PkgSig hsame Cont SemanticNameCert
  intro unaryD unaryW unaryT unaryR toleranceCont criterionCont regularCont pkgSig
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed unaryD unaryW toleranceCont
  have criterionUnary : UnaryHistory criterionRead :=
    unary_cont_closed toleranceUnary unaryT criterionCont
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed criterionUnary unaryR regularCont
  have sourceRegular :
      (fun row : BHist => hsame row regularRead ∧ UnaryHistory row) regularRead :=
    ⟨hsame_refl regularRead, regularUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row regularRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row D ∨ hsame row W ∨ hsame row T ∨ hsame row R ∨
              hsame row regularRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont D W toleranceRead ∧
              Cont toleranceRead T criterionRead ∧ Cont criterionRead R regularRead ∧
                PkgSig bundle regularRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro regularRead sourceRegular
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
        intro _row other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro row source
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro row source
      exact ⟨source.right, toleranceCont, criterionCont, regularCont, pkgSig⟩
  }
  exact ⟨cert, toleranceUnary, criterionUnary, regularUnary⟩

end DyadicCauchyCriterionUp

end BEDC.Derived
