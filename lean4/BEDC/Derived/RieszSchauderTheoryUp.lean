import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive RieszSchauderTheoryUp : Type where
  | mk
      (banach bounded compact spectral fredholm transport replay provenance name : BHist) :
      RieszSchauderTheoryUp
  deriving DecidableEq

end BEDC.Derived
