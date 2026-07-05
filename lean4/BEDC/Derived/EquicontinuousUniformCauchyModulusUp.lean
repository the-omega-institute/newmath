import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive EquicontinuousUniformCauchyModulusUp : Type where
  | mk
      (sourceWindow uniformRequest sharedModulus cauchyThreshold streamWindow readback
        dyadicLedger realSeal transport replay provenance localNameCert : BHist) :
      EquicontinuousUniformCauchyModulusUp
  deriving DecidableEq

end BEDC.Derived
