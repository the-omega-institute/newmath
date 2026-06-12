import BEDC.FKernel.Hist

namespace BEDC.Derived

inductive UltrametricBaireTheoremUp : Type where
  | mk
      (baireSchedule completeUltrametric baireUltrametric completeMetric streamName regSeqRat
        realSeal transport replay provenance nameCert : BEDC.FKernel.Hist.BHist) :
      UltrametricBaireTheoremUp

end BEDC.Derived
