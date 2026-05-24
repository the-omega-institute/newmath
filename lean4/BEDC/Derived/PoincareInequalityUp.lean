import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive PoincareInequalityUp : Type where
  | mk : (domain boundary gradient norm constant transport replay provenance name : BHist) →
      PoincareInequalityUp
  deriving DecidableEq

end BEDC.Derived
