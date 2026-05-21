import BEDC.Derived.TypeClassifierRouteJoinUp.TasteGate
import BEDC.FKernel.NameCert

namespace BEDC.Derived.TypeClassifierRouteJoinUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem TypeClassifierRouteJoinNameCertObligations (x : TypeClassifierRouteJoinUp) :
    ∃ membership routeChoice dischargeSocket transports replay provenance localName
        joinedRead : BHist,
      x = TypeClassifierRouteJoinUp.mk membership routeChoice dischargeSocket transports replay
          provenance localName joinedRead ∧
        SemanticNameCert
          (fun row : BHist => hsame row joinedRead)
          (fun row : BHist =>
            hsame row membership ∨ hsame row routeChoice ∨ hsame row dischargeSocket ∨
              hsame row transports ∨ hsame row replay ∨ hsame row provenance ∨
                hsame row localName ∨ hsame row joinedRead)
          (fun row : BHist => hsame row localName ∨ hsame row joinedRead)
          hsame := by
  -- BEDC touchpoint anchor: BHist hsame SemanticNameCert
  cases x with
  | mk membership routeChoice dischargeSocket transports replay provenance localName
      joinedRead =>
      refine
        ⟨membership, routeChoice, dischargeSocket, transports, replay, provenance, localName,
          joinedRead, rfl, ?_⟩
      exact {
        core := {
          carrier_inhabited := Exists.intro joinedRead (hsame_refl joinedRead)
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
            exact hsame_trans (hsame_symm sameRows) source
        }
        pattern_sound := by
          intro _row source
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source))))))
        ledger_sound := by
          intro _row source
          exact Or.inr source
      }

end BEDC.Derived.TypeClassifierRouteJoinUp
