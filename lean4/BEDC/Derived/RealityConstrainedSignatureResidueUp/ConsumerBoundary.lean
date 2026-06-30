import BEDC.Derived.RealityConstrainedSignatureResidueUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.RealityConstrainedSignatureResidueUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem RealityConstrainedSignatureResidueConsumerBoundary
    {M S G R W H C P N consumer residueRead nameRead : BHist} :
    Cont M S consumer ->
      Cont consumer G residueRead ->
        Cont residueRead W nameRead ->
          UnaryHistory M ->
            UnaryHistory S ->
              UnaryHistory G ->
                UnaryHistory W ->
                  SemanticNameCert
                      (fun row : BHist => hsame row nameRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row M ∨ hsame row S ∨ hsame row G ∨ hsame row R ∨
                          hsame row W ∨ hsame row consumer ∨ hsame row residueRead ∨
                            hsame row nameRead)
                      (fun row : BHist => hsame row nameRead ∧ Cont residueRead W nameRead)
                      hsame ∧
                    UnaryHistory consumer ∧ UnaryHistory residueRead ∧ UnaryHistory nameRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro consumerRoute residueRoute nameRoute mUnary sUnary gUnary wUnary
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed mUnary sUnary consumerRoute
  have residueUnary : UnaryHistory residueRead :=
    unary_cont_closed consumerUnary gUnary residueRoute
  have nameUnary : UnaryHistory nameRead :=
    unary_cont_closed residueUnary wUnary nameRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row nameRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row S ∨ hsame row G ∨ hsame row R ∨ hsame row W ∨
              hsame row consumer ∨ hsame row residueRead ∨ hsame row nameRead)
          (fun row : BHist => hsame row nameRead ∧ Cont residueRead W nameRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro nameRead ⟨hsame_refl nameRead, nameUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, nameRoute⟩
  }
  exact ⟨cert, consumerUnary, residueUnary, nameUnary⟩

end BEDC.Derived.RealityConstrainedSignatureResidueUp
