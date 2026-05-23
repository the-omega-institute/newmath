import BEDC.Derived.RealityConstrainedTruthCertUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.RealityConstrainedTruthCertUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem RealityConstrainedTruthCertL10TerminalReadbackDeterminacy
    (x : TasteGate.RealityConstrainedTruthCertUp)
    {S Sigma K T U D I L F N sourceClassifier ledgerFailure localRoute exportRoute
      terminalRead terminalRead' : BHist} :
    x = TasteGate.RealityConstrainedTruthCertUp.mk S Sigma K T U D I L F N ->
      Cont S K sourceClassifier ->
        Cont L F ledgerFailure ->
          Cont ledgerFailure N localRoute ->
            Cont sourceClassifier localRoute exportRoute ->
              Cont exportRoute N terminalRead ->
                Cont exportRoute N terminalRead' ->
                  hsame terminalRead terminalRead' ∧
                    hsame exportRoute (append (append S K) (append (append L F) N)) := by
  -- BEDC touchpoint anchor: BHist Cont hsame append
  intro packetEq sourceRoute ledgerRoute localRouteRoute exportRouteRoute terminalRoute
    terminalRoute'
  cases packetEq
  have sameTerminal : hsame terminalRead terminalRead' :=
    cont_deterministic terminalRoute terminalRoute'
  have sameExport : hsame exportRoute (append (append S K) (append (append L F) N)) := by
    cases sourceRoute
    cases ledgerRoute
    cases localRouteRoute
    cases exportRouteRoute
    rfl
  exact ⟨sameTerminal, sameExport⟩

end BEDC.Derived.RealityConstrainedTruthCertUp
