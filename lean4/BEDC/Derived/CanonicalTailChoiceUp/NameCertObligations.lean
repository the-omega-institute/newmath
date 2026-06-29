import BEDC.Derived.CanonicalTailChoiceUp.TasteGate
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CanonicalTailChoiceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

def CanonicalTailChoiceObligationRowSpec
    (M E I T S R H C0 P N row : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist hsame
  hsame row M ∨ hsame row E ∨ hsame row I ∨ hsame row T ∨ hsame row S ∨
    hsame row R ∨ hsame row H ∨ hsame row C0 ∨ hsame row P ∨ hsame row N

theorem CanonicalTailChoiceNameCertObligations (M E I T S R H C0 P N : BHist) :
    SemanticNameCert
      (CanonicalTailChoiceObligationRowSpec M E I T S R H C0 P N)
      (CanonicalTailChoiceObligationRowSpec M E I T S R H C0 P N)
      (CanonicalTailChoiceObligationRowSpec M E I T S R H C0 P N)
      hsame := by
  -- BEDC touchpoint anchor: BHist hsame SemanticNameCert
  let rowSpec := CanonicalTailChoiceObligationRowSpec M E I T S R H C0 P N
  have carrierInhabited : ∃ row : BHist, rowSpec row :=
    ⟨M, Or.inl (hsame_refl M)⟩
  have rowSpecTransport :
      ∀ row other : BHist, hsame row other → rowSpec row → rowSpec other := by
    intro row other sameRows source
    cases sameRows
    exact source
  exact {
    core := {
      carrier_inhabited := carrierInhabited
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
        intro row other sameRows source
        exact rowSpecTransport row other sameRows source
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

end BEDC.Derived.CanonicalTailChoiceUp
