import BEDC.Derived.RegularCauchyTailModulusUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyTailModulusUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem RegularCauchyTailModulusWindowHandoff
    {S Q T W D H C P N thresholdRead windowRead toleranceRead : BHist} :
    regularCauchyTailModulusFields (RegularCauchyTailModulusUp.mk S Q T W D H C P N) =
        [S, Q, T, W, D, H, C, P, N] →
      UnaryHistory S →
        UnaryHistory Q →
          UnaryHistory T →
            UnaryHistory W →
              UnaryHistory D →
                Cont S Q thresholdRead →
                  Cont thresholdRead W windowRead →
                    Cont windowRead D toleranceRead →
                      SemanticNameCert
                          (fun row : BHist => hsame row toleranceRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row S ∨ hsame row Q ∨ hsame row T ∨ hsame row W ∨
                              hsame row D ∨ hsame row toleranceRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont S Q thresholdRead ∧
                              Cont thresholdRead W windowRead ∧
                                Cont windowRead D toleranceRead)
                          hsame ∧ UnaryHistory thresholdRead ∧ UnaryHistory windowRead ∧
                        UnaryHistory toleranceRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro fields unaryS unaryQ _unaryT unaryW unaryD thresholdCont windowCont toleranceCont
  have thresholdUnary : UnaryHistory thresholdRead :=
    unary_cont_closed unaryS unaryQ thresholdCont
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed thresholdUnary unaryW windowCont
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed windowUnary unaryD toleranceCont
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row toleranceRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row Q ∨ hsame row T ∨ hsame row W ∨ hsame row D ∨
              hsame row toleranceRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S Q thresholdRead ∧
              Cont thresholdRead W windowRead ∧ Cont windowRead D toleranceRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro toleranceRead ⟨hsame_refl toleranceRead, toleranceUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, thresholdCont, windowCont, toleranceCont⟩
  }
  cases fields
  exact ⟨cert, thresholdUnary, windowUnary, toleranceUnary⟩

end BEDC.Derived.RegularCauchyTailModulusUp
