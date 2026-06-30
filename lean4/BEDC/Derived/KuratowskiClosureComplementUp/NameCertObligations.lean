import BEDC.Derived.KuratowskiClosureComplementUp.TasteGate
import BEDC.FKernel.NameCert

namespace BEDC.Derived.KuratowskiClosureComplementUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem KuratowskiClosureComplementCarrier_namecert_obligations
    (x : KuratowskiClosureComplementUp) :
    ∃ localCert : BHist,
      SemanticNameCert
        (fun row : BHist =>
          hsame row localCert ∧ localCert ∈ kuratowskiClosureComplementFields x)
        (fun row : BHist =>
          hsame row localCert ∧ localCert ∈ kuratowskiClosureComplementFields x)
        (fun row : BHist =>
          hsame row localCert ∧ localCert ∈ kuratowskiClosureComplementFields x)
        hsame := by
  -- BEDC touchpoint anchor: BHist hsame SemanticNameCert
  cases x with
  | mk T F L C A B H R P N =>
      refine Exists.intro T ?_
      exact {
        core := {
          carrier_inhabited := Exists.intro T ⟨hsame_refl T, List.Mem.head _⟩
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
            exact ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
        }
        pattern_sound := by
          intro _row source
          exact source
        ledger_sound := by
          intro _row source
          exact source
      }

end BEDC.Derived.KuratowskiClosureComplementUp
