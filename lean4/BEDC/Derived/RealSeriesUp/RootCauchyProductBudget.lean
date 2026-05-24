import BEDC.Derived.RealSeriesUp.TasteGate
import BEDC.FKernel.Cont.Assoc
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.RealSeriesUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem RealSeriesRootProductTailBudget {S W Q D M right outer : BHist} :
    Cont S W Q ->
      Cont W D right ->
        Cont Q D M ->
          Cont S right outer ->
            UnaryHistory S ->
              UnaryHistory W ->
                UnaryHistory D ->
                  exists common : BHist,
                    Cont Q D common ∧ Cont S right common ∧ hsame M common ∧
                      hsame outer common ∧ UnaryHistory Q ∧ UnaryHistory common := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro qRoute rightRoute mRoute outerRoute SUnary WUnary DUnary
  obtain ⟨common, commonLeft, commonRight, mSame, outerSame⟩ :=
    cont_assoc_common_witness qRoute rightRoute mRoute outerRoute
  have QUnary : UnaryHistory Q :=
    unary_cont_closed SUnary WUnary qRoute
  have commonUnary : UnaryHistory common :=
    unary_cont_closed QUnary DUnary commonLeft
  exact ⟨common, commonLeft, commonRight, mSame, outerSame, QUnary, commonUnary⟩

end BEDC.Derived.RealSeriesUp
