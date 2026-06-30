import BEDC.Derived.PhilosophyFormalTargetLedgerUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.PhilosophyFormalTargetLedgerUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem PhilosophyFormalTargetLedger_sibling_dependency
    {R T G D S U L M B H C P N targetRead refusalRead auditRead : BHist} :
    philosophyFormalTargetLedgerFields
        (PhilosophyFormalTargetLedgerUp.mk R T G D S U L M B H C P N) =
          [R, T, G, D, S, U, L, M, B, H, C, P, N] →
      Cont R M targetRead →
        Cont targetRead B refusalRead →
          Cont refusalRead U auditRead →
            hsame R R ∧ hsame T T ∧ hsame G G ∧ hsame D D ∧
              hsame S S ∧ hsame U U ∧ hsame L L ∧ hsame M M ∧
                hsame B B ∧ hsame H H ∧ hsame C C ∧ hsame P P ∧
                  hsame N N ∧ Cont R M targetRead ∧
                    Cont targetRead B refusalRead ∧ Cont refusalRead U auditRead := by
  -- BEDC touchpoint anchor: BHist hsame Cont PhilosophyFormalTargetLedgerUp
  intro _fields targetRoute refusalRoute auditRoute
  exact
    ⟨hsame_refl R, hsame_refl T, hsame_refl G, hsame_refl D, hsame_refl S,
      hsame_refl U, hsame_refl L, hsame_refl M, hsame_refl B, hsame_refl H,
      hsame_refl C, hsame_refl P, hsame_refl N, targetRoute, refusalRoute,
      auditRoute⟩

end BEDC.Derived.PhilosophyFormalTargetLedgerUp
