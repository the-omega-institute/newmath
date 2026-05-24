import BEDC.FKernel.Cont

namespace BEDC.Derived.RealSeriesUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem RealSeriesPartialSumProductRoute {S D Q M product SD SDQ SDQM handoff : BHist} :
    Cont S D SD →
      Cont SD Q SDQ →
        Cont SDQ M SDQM →
          Cont SDQM product handoff →
            hsame handoff (append S (append D (append Q (append M product)))) := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  intro hSD hSDQ hSDQM hhandoff
  cases hSD
  cases hSDQ
  cases hSDQM
  cases hhandoff
  exact
    Eq.trans (append_assoc (append (append S D) Q) M product)
      (Eq.trans (append_assoc (append S D) Q (append M product))
        (append_assoc S D (append Q (append M product))))

end BEDC.Derived.RealSeriesUp
