import BEDC.FKernel.Hist

namespace BEDC.Derived

inductive MonotoneBoundedConvergenceUp : Type where
  | mk
      (source monotoneLedger boundedness locatedSupremum regSeqRat realSeal
        transport replay provenance namecert : BEDC.FKernel.Hist.BHist)

end BEDC.Derived
