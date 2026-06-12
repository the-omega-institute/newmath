import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive ClopenAlgebraUp : Type where
  | mk
      (topology openRow complementOpen booleanOps stoneLedger transport replay provenance
        localName : BHist) :
      ClopenAlgebraUp
  deriving DecidableEq

end BEDC.Derived
