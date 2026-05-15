import BEDC.Derived.CauchyWitnessLedgerUp.TasteGate

namespace BEDC.Derived.CauchyWitnessLedgerUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.Meta.TasteGate

theorem CauchyWitnessLedgerCarrier_source_sibling_readback
    {Q B S K H C P N Q' B' S' K' H' C' P' N' streamWindow dyadicRead regSeqRead
      realRead : BHist} :
    FieldFaithful.fields (CauchyWitnessLedgerUp.mk Q B S K H C P N) =
        FieldFaithful.fields (CauchyWitnessLedgerUp.mk Q' B' S' K' H' C' P' N') →
      Cont Q B S →
        Cont B H streamWindow →
          Cont streamWindow S dyadicRead →
            Cont dyadicRead K regSeqRead →
              Cont regSeqRead N realRead →
                Cont Q' B' S' ∧ Cont B' H' streamWindow ∧
                  Cont streamWindow S' dyadicRead ∧ Cont dyadicRead K' regSeqRead ∧
                    Cont regSeqRead N' realRead := by
  -- BEDC touchpoint anchor: BHist Cont FieldFaithful
  intro hfields routeSource routeWindow routeDyadic routeRegSeq routeReal
  change [Q, B, S, K, H, C, P, N] = [Q', B', S', K', H', C', P', N'] at hfields
  injection hfields with hQ tailQ
  injection tailQ with hB tailB
  injection tailB with hS tailS
  injection tailS with hK tailK
  injection tailK with hH tailH
  injection tailH with _hC tailC
  injection tailC with _hP tailP
  injection tailP with hN _tailN
  subst hQ
  subst hB
  subst hS
  subst hK
  subst hH
  subst hN
  exact ⟨routeSource, routeWindow, routeDyadic, routeRegSeq, routeReal⟩

end BEDC.Derived.CauchyWitnessLedgerUp
