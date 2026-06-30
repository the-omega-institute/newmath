import BEDC.FKernel.Hist

namespace BEDC.Derived

inductive CauchyNameTruncationUp : Type where
  | mk
      (stream regSeqRat dyadic truncation realSeal transport replay provenance name :
        _root_.BEDC.FKernel.Hist.BHist) :
      CauchyNameTruncationUp

end BEDC.Derived
