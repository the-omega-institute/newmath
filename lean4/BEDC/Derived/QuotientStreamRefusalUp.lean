import BEDC.Derived.QuotientStreamRefusalUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.QuotientStreamRefusalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem QuotientStreamRefusal_refusal_ledger_changes_packet
    (S R L E F F' H C P N : BHist)
    (_refusalRoute : Cont F H C) (_refusalRoute' : Cont F' H C) (hF : F ≠ F') :
    QuotientStreamRefusalUp.mk S R L E F H C P N ≠
      QuotientStreamRefusalUp.mk S R L E F' H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hpacket
  injection hpacket with _ _ _ _ hRefusal _ _ _ _
  exact hF hRefusal

end BEDC.Derived.QuotientStreamRefusalUp
