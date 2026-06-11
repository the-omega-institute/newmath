import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive DirectedCofinalSubsetUp : Type where
  | mk
      (ambientIndex retainedIndex comparison ambientWindow retainedWindow cofinalWitness
        transport replay package name : BHist) :
      DirectedCofinalSubsetUp
  deriving DecidableEq

def directedCofinalSubsetFields : DirectedCofinalSubsetUp → List BHist
  | DirectedCofinalSubsetUp.mk
      ambientIndex retainedIndex comparison ambientWindow retainedWindow cofinalWitness transport
      replay package name =>
      [ambientIndex, retainedIndex, comparison, ambientWindow, retainedWindow, cofinalWitness,
        transport, replay, package, name]

end BEDC.Derived
