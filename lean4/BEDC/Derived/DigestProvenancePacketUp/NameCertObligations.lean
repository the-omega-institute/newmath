import BEDC.Derived.DigestProvenancePacketUp.TasteGate
import BEDC.FKernel.NameCert

namespace BEDC.Derived.DigestProvenancePacketUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem DigestProvenancePacketCarrier_namecert_obligations
    (R : DigestProvenancePacketUp) :
    ∃ V S F G E H C P N : BHist,
      R = DigestProvenancePacketUp.mk V S F G E H C P N ∧
        SemanticNameCert
          (fun row : BHist => hsame row V)
          (fun row : BHist =>
            hsame row V ∨ hsame row S ∨ hsame row F ∨ hsame row G ∨ hsame row E ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N)
          (fun row : BHist => hsame row V)
          hsame := by
  -- BEDC touchpoint anchor: BHist hsame SemanticNameCert
  cases R with
  | mk V S F G E H C P N =>
      refine ⟨V, S, F, G, E, H, C, P, N, rfl, ?_⟩
      exact {
        core := {
          carrier_inhabited := Exists.intro V (hsame_refl V)
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
            exact hsame_trans (hsame_symm same) source
        }
        pattern_sound := by
          intro _row source
          exact Or.inl source
        ledger_sound := by
          intro _row source
          exact source
      }

end BEDC.Derived.DigestProvenancePacketUp
