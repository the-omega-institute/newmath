import BEDC.Derived.PhysicalLawBridgeUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.PhysicalLawBridgeUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark

theorem PhysicalLawBridgeFalsificationBoundary_encode_append (fit failure : BHist) :
    physicalLawBridgeEncodeBHist (append fit failure) =
      List.append (physicalLawBridgeEncodeBHist failure) (physicalLawBridgeEncodeBHist fit) := by
  -- BEDC touchpoint anchor: BHist BMark append
  induction failure with
  | Empty =>
      rfl
  | e0 failure ih =>
      exact congrArg (fun tail => BMark.b0 :: tail) ih
  | e1 failure ih =>
      exact congrArg (fun tail => BMark.b1 :: tail) ih

end BEDC.Derived.PhysicalLawBridgeUp
