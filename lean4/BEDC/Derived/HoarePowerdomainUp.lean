import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive HoarePowerdomainUp : Type where
  | mk
      (domain openRow lowerWitness lowerHit hitWindow monotoneReadback transport replay provenance
        name : BHist) :
      HoarePowerdomainUp
  deriving DecidableEq

end BEDC.Derived
