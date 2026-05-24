import BEDC.Derived.RealSeriesUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Assoc
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.RealSeriesUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

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

theorem RealSeriesRootTailFactorization {S W D M sw dm left right outer : BHist} :
    Cont S W sw ->
      Cont D M dm ->
        Cont W dm right ->
          Cont sw dm left ->
            Cont S right outer ->
              UnaryHistory D ->
                UnaryHistory M ->
                  exists common : BHist,
                    Cont sw dm common ∧ Cont S right common ∧ hsame left common ∧
                      hsame outer common ∧ UnaryHistory dm := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro swRoute dmRoute rightRoute leftRoute outerRoute DUnary MUnary
  obtain ⟨common, commonLeft, commonRight, leftSame, outerSame⟩ :=
    cont_assoc_common_witness swRoute rightRoute leftRoute outerRoute
  have dmUnary : UnaryHistory dm :=
    unary_cont_closed DUnary MUnary dmRoute
  exact ⟨common, commonLeft, commonRight, leftSame, outerSame, dmUnary⟩

end BEDC.Derived.RealSeriesUp
