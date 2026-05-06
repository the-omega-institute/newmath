import BEDC.FKernel.Unary

namespace BEDC.Derived.OdeUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def OdeLocalFlowSource (t0 x0 p v ell t1 x1 : BHist) : Prop :=
  UnaryHistory t0 ∧ UnaryHistory x0 ∧ UnaryHistory p ∧ UnaryHistory v ∧
    UnaryHistory ell ∧ UnaryHistory t1 ∧ UnaryHistory x1 ∧
      Cont t0 x0 p ∧ Cont p v ell ∧ Cont t1 ell x1

theorem OdeLocalFlowSource_picard_continuation_scope
    {t0 x0 p v ell t1 x1 p2 v2 ell2 t2 x2 : BHist} :
    OdeLocalFlowSource t0 x0 p v ell t1 x1 →
      OdeLocalFlowSource t1 x1 p2 v2 ell2 t2 x2 →
        ∃ route : BHist,
          UnaryHistory route ∧ Cont ell ell2 route ∧
            UnaryHistory p ∧ UnaryHistory p2 ∧ UnaryHistory x1 ∧ UnaryHistory x2 := by
  intro first second
  cases first with
  | intro _t0Unary firstRest =>
      cases firstRest with
      | intro _x0Unary firstRest =>
          cases firstRest with
          | intro pUnary firstRest =>
              cases firstRest with
              | intro _vUnary firstRest =>
                  cases firstRest with
                  | intro ellUnary firstRest =>
                      cases firstRest with
                      | intro _t1Unary firstRest =>
                          cases firstRest with
                          | intro x1Unary firstLedger =>
                              cases firstLedger with
                              | intro _t0x0Cont firstLedger =>
                                  cases firstLedger with
                                  | intro _pvCont _t1ellCont =>
                                      cases second with
                                      | intro _t1UnarySecond secondRest =>
                                          cases secondRest with
                                          | intro _x1UnarySecond secondRest =>
                                              cases secondRest with
                                              | intro p2Unary secondRest =>
                                                  cases secondRest with
                                                  | intro _v2Unary secondRest =>
                                                      cases secondRest with
                                                      | intro ell2Unary secondRest =>
                                                          cases secondRest with
                                                          | intro _t2Unary secondRest =>
                                                              cases secondRest with
                                                              | intro x2Unary secondLedger =>
                                                                  cases secondLedger with
                                                                  | intro _t1x1Cont secondLedger =>
                                                                      cases secondLedger with
                                                                      | intro _p2v2Cont _t2ell2Cont =>
                                                                          exact
                                                                            ⟨append ell ell2,
                                                                              unary_append_closed ellUnary
                                                                                ell2Unary,
                                                                              cont_intro rfl,
                                                                              pUnary,
                                                                              p2Unary,
                                                                              x1Unary,
                                                                              x2Unary⟩

end BEDC.Derived.OdeUp
