import BEDC.Derived.IntermediateValueUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.IntermediateValueUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

def IntermediateValueRealSealHandoff
    (packet : IntermediateValueUp) (bisectionLedger nestedWindow realSeal : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont hsame
  List.Mem realSeal (IntermediateValueTasteGate_single_carrier_alignment_fields packet) ∧
    Cont bisectionLedger nestedWindow realSeal ∧ hsame realSeal realSeal

theorem IntermediateValueCarrier_real_seal_handoff
    {locatedInterval endpointNegative endpointPositive continuousMap modulusBudget
      bisectionLedger nestedWindow realSeal transports routes provenance localNameCert :
        BHist} :
    Cont bisectionLedger nestedWindow realSeal →
      IntermediateValueRealSealHandoff
        (IntermediateValueUp.mk locatedInterval endpointNegative endpointPositive continuousMap
          modulusBudget bisectionLedger nestedWindow realSeal transports routes provenance
          localNameCert)
        bisectionLedger nestedWindow realSeal := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  intro route
  constructor
  · exact
      List.Mem.tail locatedInterval
        (List.Mem.tail endpointNegative
          (List.Mem.tail endpointPositive
            (List.Mem.tail continuousMap
              (List.Mem.tail modulusBudget
                (List.Mem.tail bisectionLedger
                  (List.Mem.tail nestedWindow
                    (List.Mem.head
                      [transports, routes, provenance, localNameCert])))))))
  · exact ⟨route, hsame_refl realSeal⟩

end BEDC.Derived.IntermediateValueUp
