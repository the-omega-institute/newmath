import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive FiniteCoverUniformModulusEnvelopeUp : Type where
  | mk
      (compactSource totalBounded continuousMap formalBall modulus window transport replay
        provenance name : BHist) :
      FiniteCoverUniformModulusEnvelopeUp
  deriving DecidableEq

end BEDC.Derived
