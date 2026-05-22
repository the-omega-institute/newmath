import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive MarkovPrincipleBoundaryUp : Type where
  | mk
      (inspection speckerControl streamSchedule rationalReadback dyadicLedger realSeal witnessRow
        transport replay provenance name : BHist) : MarkovPrincipleBoundaryUp

end BEDC.Derived
