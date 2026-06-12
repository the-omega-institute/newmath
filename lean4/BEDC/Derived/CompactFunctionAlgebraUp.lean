import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive CompactFunctionAlgebraUp : Type where
  | packet
      (source functions add mul unit modulus supNorm transport replay provenance localName : BHist) :
      CompactFunctionAlgebraUp
  deriving DecidableEq

end BEDC.Derived
