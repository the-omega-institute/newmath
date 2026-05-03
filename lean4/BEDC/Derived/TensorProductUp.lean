import BEDC.Derived.ModuleUp
import BEDC.FKernel.Cont

namespace BEDC.Derived.TensorProductUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.ModuleUp

def TensorProductSingletonCarrier (h : BHist) : Prop :=
  exists l : BHist, exists r : BHist, ModuleSingletonCarrier l ∧
    ModuleSingletonCarrier r ∧ Cont l r h

theorem TensorProductSingletonCarrier_continuation_suffix_carrier {pair suffix out : BHist} :
    TensorProductSingletonCarrier pair -> Cont pair suffix out ->
      TensorProductSingletonCarrier out -> ModuleSingletonCarrier suffix := by
  intro pairCarrier pairSuffix outCarrier
  cases pairCarrier with
  | intro left pairRest =>
      cases pairRest with
      | intro right pairData =>
          cases pairData with
          | intro leftCarrier pairTail =>
              cases pairTail with
              | intro rightCarrier pairCont =>
                  cases outCarrier with
                  | intro outLeft outRest =>
                      cases outRest with
                      | intro outRight outData =>
                          cases outData with
                          | intro outLeftCarrier outTail =>
                              cases outTail with
                              | intro outRightCarrier outCont =>
                                  cases leftCarrier
                                  cases rightCarrier
                                  cases pairCont
                                  cases outLeftCarrier
                                  cases outRightCarrier
                                  cases outCont
                                  exact (append_eq_empty_iff.mp pairSuffix.symm).right

end BEDC.Derived.TensorProductUp
