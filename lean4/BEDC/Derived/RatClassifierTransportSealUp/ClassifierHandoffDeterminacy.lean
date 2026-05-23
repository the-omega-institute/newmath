import BEDC.Derived.RatClassifierTransportSealUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.RatClassifierTransportSealUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem RatClassifierTransportSealCarrier_classifier_handoff_determinacy
    {Q S W D A H C N Q' S' W' D' A' H' C' N' realRead realRead' : BHist} :
    Cont Q S W ->
      Cont W D A ->
        Cont A H realRead ->
          Cont Q' S' W' ->
            Cont W' D' A' ->
              Cont A' H' realRead' ->
                hsame Q Q' ->
                  hsame S S' ->
                    hsame W W' ->
                      hsame D D' ->
                        hsame H H' ->
                          hsame realRead realRead' ->
                            hsame A A' ∧ Cont A H realRead ∧ Cont A' H' realRead' := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  intro _sourceRoute handoffRoute realRoute _sourceRoute' handoffRoute' realRoute'
  intro _sameQ _sameS sameW sameD _sameH _sameReal
  have sameA : hsame A A' :=
    cont_respects_hsame sameW sameD handoffRoute handoffRoute'
  exact ⟨sameA, realRoute, realRoute'⟩

end BEDC.Derived.RatClassifierTransportSealUp
