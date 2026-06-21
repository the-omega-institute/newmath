import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive DiracSequenceUp : Type where
  | mk
      (scaleSchedule supportDecay normalizationLedger convolutionWindow realSeal transport replay
        provenance localNameCert : BHist) :
      DiracSequenceUp
  deriving DecidableEq

end BEDC.Derived
