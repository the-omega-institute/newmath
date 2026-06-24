import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive DunfordPettisOperatorUp : Type where
  | mk
      (sourceBanach targetBanach boundedLinearOperator weakTopology weakCompactness
        compactOrCompletelyContinuous realScalar transport replay provenance localNameCert :
        BHist) :
      DunfordPettisOperatorUp
  deriving DecidableEq

end BEDC.Derived
