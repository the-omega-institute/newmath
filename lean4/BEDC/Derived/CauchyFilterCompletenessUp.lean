import BEDC.FKernel.Hist

namespace BEDC.Derived

inductive CauchyFilterCompletenessUp : Type where
  | mk
      (cauchyFilter locatedTail uniformEntourage streamName regSeqRat realSeal
        transport replay provenance localName : BEDC.FKernel.Hist.BHist)

end BEDC.Derived
