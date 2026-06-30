import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive LevyContinuityUp : Type where
  | mk
      (probabilitySource randomVariableObservation distributionReadback characteristicWindow
        toleranceLedger realSeal transport replay provenance localNameCert : BHist) :
      LevyContinuityUp
  deriving DecidableEq

end BEDC.Derived
