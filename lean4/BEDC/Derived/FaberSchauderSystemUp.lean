import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive FaberSchauderSystemUp : Type where
  | mk
      (dyadicLevel hat support coefficient modulus transport replay provenance name : BHist) :
      FaberSchauderSystemUp
  deriving DecidableEq

end BEDC.Derived
