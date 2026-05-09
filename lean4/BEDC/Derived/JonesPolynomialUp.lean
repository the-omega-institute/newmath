import BEDC.FKernel.Cont
import BEDC.FKernel.Hist

namespace BEDC.Derived.JonesPolynomialUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

def JonesSkeinLedgerPacket
    (main plus minus smooth endpoint skein provenance ledger : BHist) : Prop :=
  Cont main endpoint skein ∧ Cont plus minus smooth ∧ Cont skein provenance ledger ∧
    hsame provenance BHist.Empty

theorem JonesSkeinLedgerPacket_obligation_surface
    {main plus minus smooth endpoint skein provenance ledger : BHist} :
    JonesSkeinLedgerPacket main plus minus smooth endpoint skein provenance ledger ->
      Cont main endpoint skein ∧ Cont plus minus smooth ∧ Cont skein provenance ledger ∧
        hsame provenance BHist.Empty ∧ hsame ledger (append skein provenance) := by
  intro packet
  exact And.intro packet.left
    (And.intro packet.right.left
      (And.intro packet.right.right.left
        (And.intro packet.right.right.right packet.right.right.left)))

end BEDC.Derived.JonesPolynomialUp
