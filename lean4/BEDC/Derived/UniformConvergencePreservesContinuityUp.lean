import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive UniformConvergencePreservesContinuityUp : Type where
  | mk
      (uniformLimit uniformCauchy supNorm compact continuous limitRow realSeal
        window modulus transport replay provenance name : BHist) :
      UniformConvergencePreservesContinuityUp
  deriving DecidableEq

end BEDC.Derived
