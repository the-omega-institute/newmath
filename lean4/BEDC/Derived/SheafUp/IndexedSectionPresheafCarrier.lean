import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def SheafIndexedSectionPresheafCarrier
    (openHist sectionHist restrictedHist : BHist) : Prop :=
  UnaryHistory openHist ∧ UnaryHistory sectionHist ∧ Cont openHist sectionHist restrictedHist

theorem SheafIndexedSectionPresheafCarrier_endpoint_unary
    {openHist sectionHist restrictedHist : BHist} :
    SheafIndexedSectionPresheafCarrier openHist sectionHist restrictedHist ->
      UnaryHistory restrictedHist := by
  intro carrier
  exact unary_cont_closed carrier.left carrier.right.left carrier.right.right

end BEDC.Derived.SheafUp
