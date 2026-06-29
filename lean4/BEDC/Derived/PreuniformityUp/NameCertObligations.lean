import BEDC.Derived.PreuniformityUp.TasteGate
import BEDC.FKernel.NameCert

namespace BEDC.Derived.PreuniformityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

def PreuniformityObligationRowSpec (S E B T H C P N row : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist hsame
  hsame row S ∨ hsame row E ∨ hsame row B ∨ hsame row T ∨
    hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N

theorem PreuniformityNameCertObligations (S E B T H C P N : BHist) :
    SemanticNameCert
      (PreuniformityObligationRowSpec S E B T H C P N)
      (PreuniformityObligationRowSpec S E B T H C P N)
      (PreuniformityObligationRowSpec S E B T H C P N)
      hsame := by
  -- BEDC touchpoint anchor: BHist hsame SemanticNameCert
  let rowSpec := PreuniformityObligationRowSpec S E B T H C P N
  have carrierInhabited : ∃ row : BHist, rowSpec row :=
    ⟨S, Or.inl (hsame_refl S)⟩
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

end BEDC.Derived.PreuniformityUp
