import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive FiniteDimensionalNormedCompletenessUp : Type where
  | mk
      (vecSpace normedSpace finiteBasis coordinateCauchy normStability regSeqRat realSeal
        completionOperator banachSeal transport replay provenance localNameCert : BHist) :
      FiniteDimensionalNormedCompletenessUp
  deriving DecidableEq

end BEDC.Derived
