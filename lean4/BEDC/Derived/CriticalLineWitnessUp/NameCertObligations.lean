import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem CriticalLineWitnessCarrier_namecert_obligations {Z S M R Q H C P N : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      SemanticNameCert
        (fun row : BHist => CriticalLineWitnessCarrier Z S M R Q H C P N ∧ hsame row N)
        (fun row : BHist => CriticalLineWitnessCarrier Z S M R Q H C P N ∧ hsame row N)
        (fun row : BHist => CriticalLineWitnessCarrier Z S M R Q H C P N ∧ hsame row N)
        hsame := by
  -- BEDC touchpoint anchor: BHist hsame SemanticNameCert CriticalLineWitnessCarrier
  intro packet
  exact {
    core := {
      carrier_inhabited := Exists.intro N ⟨packet, hsame_refl N⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same source
        exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

end BEDC.Derived.CriticalLineWitnessUp
