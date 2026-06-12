import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package

namespace BEDC.Derived

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

structure ReducedProductUp : Type where
  modelFamily : BHist
  filterRow : BHist
  pointwiseFormula : BHist
  agreementClassifier : BHist
  transport : BHist
  replay : BHist
  provenance : BHist
  localName : BHist

def ReducedProductUp.visibleRoute (packet : ReducedProductUp) : BHist :=
  append packet.modelFamily
    (append packet.filterRow
      (append packet.pointwiseFormula
        (append packet.agreementClassifier
          (append packet.transport
            (append packet.replay (append packet.provenance packet.localName))))))

def ReducedProductUp.routeSupported (packet : ReducedProductUp) : Prop :=
  hsame packet.transport (append packet.modelFamily packet.filterRow) ∧
    Cont packet.pointwiseFormula packet.agreementClassifier packet.replay ∧
      hsame packet.provenance (append packet.replay packet.localName)

end BEDC.Derived
