import BEDC.FKernel.Cont

namespace BEDC.Derived.RealSeriesUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem RealSeriesTailLedger {S W Q D M SW SWQ SWQD SWQDM : BHist} :
    Cont S W SW →
      Cont SW Q SWQ →
        Cont SWQ D SWQD →
          Cont SWQD M SWQDM →
            hsame SWQDM (append S (append W (append Q (append D M)))) := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  intro hSW hSWQ hSWQD hSWQDM
  cases hSW
  cases hSWQ
  cases hSWQD
  cases hSWQDM
  exact
    Eq.trans (append_assoc (append (append S W) Q) D M)
      (Eq.trans (append_assoc (append S W) Q (append D M))
        (append_assoc S W (append Q (append D M))))

end BEDC.Derived.RealSeriesUp
