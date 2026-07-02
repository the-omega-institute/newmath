import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive GaloisConnectionUp : Type where
  | mk (P Q F G M A T R L N : BHist) : GaloisConnectionUp
  deriving DecidableEq

def GaloisConnectionClosureOperatorUp : Type :=
  Unit

end BEDC.Derived
