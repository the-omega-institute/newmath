import BEDC.FKernel.Hist

namespace BEDC.Derived

inductive RealCompletionTailLockUp : Type where
  | mk
      (stream regSeqRat dyadic realSeal tailLock transport replay provenance name :
        _root_.BEDC.FKernel.Hist.BHist) :
      RealCompletionTailLockUp

end BEDC.Derived
