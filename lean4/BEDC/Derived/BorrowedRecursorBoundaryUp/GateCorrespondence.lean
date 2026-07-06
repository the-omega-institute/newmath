import BEDC.FKernel.Cont

namespace BEDC.Derived.BorrowedRecursorBoundaryUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem BorrowedRecursorBoundary_gate_correspondence
    {R A S F H _C _P _N ancestryRead socketRead refusalRead gateRead : BHist} :
    Cont R A ancestryRead →
      Cont ancestryRead S socketRead →
        Cont socketRead F refusalRead →
          Cont refusalRead H gateRead →
            hsame gateRead (append R (append A (append S (append F H)))) := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  intro ancestryRoute socketRoute refusalRoute gateRoute
  cases ancestryRoute
  cases socketRoute
  cases refusalRoute
  cases gateRoute
  exact
    (append_assoc (append (append R A) S) F H).trans
      ((append_assoc (append R A) S (append F H)).trans
        (append_assoc R A (append S (append F H))))

end BEDC.Derived.BorrowedRecursorBoundaryUp
