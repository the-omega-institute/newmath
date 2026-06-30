import BEDC.Derived.KuratowskiClosureComplementUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.KuratowskiClosureComplementUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem KuratowskiClosureComplementCarrier_fourteen_route
    {T F L C A B H R P N TF TFL TFLC TFLCA replayRead : BHist} :
    Cont T F TF →
      Cont TF L TFL →
        Cont TFL C TFLC →
          Cont TFLC A TFLCA →
            Cont TFLCA B replayRead →
              Cont T (append F (append L (append C (append A B)))) replayRead ∧
                B ∈
                  kuratowskiClosureComplementFields
                    (KuratowskiClosureComplementUp.mk T F L C A B H R P N) := by
  -- BEDC touchpoint anchor: BHist Cont append
  intro tF tfL tflC tflcA tflcaB
  constructor
  · cases tF
    cases tfL
    cases tflC
    cases tflcA
    cases tflcaB
    exact
      (append_assoc (append (append (append T F) L) C) A B).trans
        ((append_assoc (append (append T F) L) C (append A B)).trans
          ((append_assoc (append T F) L (append C (append A B))).trans
            (append_assoc T F (append L (append C (append A B))))))
  · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
      (List.Mem.tail _ (List.Mem.head _)))))

end BEDC.Derived.KuratowskiClosureComplementUp
