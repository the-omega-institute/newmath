import BEDC.Derived.PhilosophyFormalTargetLedgerUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.PhilosophyFormalTargetLedgerUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem PhilosophyFormalTargetLedger_nonescape
    {R T G D S U L M B H C P N auditRead targetRead refusalRead : BHist} :
    philosophyFormalTargetLedgerFields
        (PhilosophyFormalTargetLedgerUp.mk R T G D S U L M B H C P N) =
          [R, T, G, D, S, U, L, M, B, H, C, P, N] ->
      Cont R M targetRead ->
        Cont targetRead B refusalRead ->
          hsame auditRead R ->
            hsame R R ∧ hsame M M ∧ hsame B B ∧ hsame U U ∧
              Cont R M targetRead ∧ Cont targetRead B refusalRead ∧ hsame auditRead R ∧
                philosophyFormalTargetLedgerFields
                    (PhilosophyFormalTargetLedgerUp.mk R T G D S U L M B H C P N) =
                  [R, T, G, D, S, U, L, M, B, H, C, P, N] := by
  -- BEDC touchpoint anchor: BHist hsame Cont PhilosophyFormalTargetLedgerUp
  intro fields targetRoute refusalRoute auditSame
  exact
    ⟨hsame_refl R, hsame_refl M, hsame_refl B, hsame_refl U, targetRoute, refusalRoute,
      auditSame, fields⟩

end BEDC.Derived.PhilosophyFormalTargetLedgerUp
