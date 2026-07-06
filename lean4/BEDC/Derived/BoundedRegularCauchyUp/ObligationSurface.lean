import BEDC.Derived.BoundedRegularCauchyUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.BoundedRegularCauchyUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem BoundedRegularCauchyCarrier_obligation_surface
    {S M B Q A H C P N request _readback sealRow : BHist} :
    Cont request M S ->
      Cont S B Q ->
        Cont Q A sealRow ->
          hsame H H ->
            hsame C C ->
              exists route : BHist,
                Cont request M S ∧ Cont S B Q ∧ Cont Q A sealRow ∧ hsame route route := by
  -- BEDC touchpoint anchor: BHist Cont hsame BoundedRegularCauchyUp
  intro requestModulus streamBoundReadback readbackSeal _transportSame _replaySame
  let packet : BoundedRegularCauchyUp := BoundedRegularCauchyUp.mk S M B Q A H C P N
  have packetRows :
      boundedRegularCauchyFields packet = [S, M, B, Q, A, H, C, P, N] := by
    rfl
  cases packetRows
  exact
    ⟨sealRow, requestModulus, streamBoundReadback, readbackSeal, hsame_refl sealRow⟩

end BEDC.Derived.BoundedRegularCauchyUp
