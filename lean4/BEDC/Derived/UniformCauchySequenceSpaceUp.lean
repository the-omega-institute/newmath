import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive UniformCauchySequenceSpaceUp : Type where
  | mk
      (stream regular dyadic sequenceSpace modulus realSeal
        transport replay provenance name : BHist) :
      UniformCauchySequenceSpaceUp
  deriving DecidableEq

end BEDC.Derived
