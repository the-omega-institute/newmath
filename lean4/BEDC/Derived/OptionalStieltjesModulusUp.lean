import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive OptionalStieltjesModulusUp : Type where
  | mk
      (integrand integrator variation partition step modulus readback realSeal transport replay
        provenance localName : BHist) : OptionalStieltjesModulusUp
  deriving DecidableEq

end BEDC.Derived
