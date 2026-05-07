import BEDC.FKernel.Unary

namespace BEDC.Derived.OdeUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def OdeLocalFlowRow (t0 x0 t1 x1 v p ell : BHist) : Prop :=
  Cont t0 x0 p ∧ Cont p v ell ∧ Cont t1 ell x1

theorem OdeLocalFlowRow_picard_continuation_scope
    {t0 x0 t1 x1 v p ell next route : BHist} :
    OdeLocalFlowRow t0 x0 t1 x1 v p ell → Cont x1 next route →
      ∃ carried : BHist, Cont ell next carried ∧ Cont t1 carried route := by
  intro row endpoint
  exact cont_assoc_left_exists row.right.right endpoint

theorem OdeLocalFlow_endpoint_classifier_deterministic
    {t0 x0 p p' v v' ell ell' t1 x1 x1' : BHist} :
    Cont t0 x0 p →
      Cont t0 x0 p' →
        hsame v v' →
          Cont p v ell →
            Cont p' v' ell' →
              Cont t1 ell x1 →
                Cont t1 ell' x1' → hsame x1 x1' := by
  intro initial initial' vectorSame step step' endpoint endpoint'
  have picardSame : hsame p p' := cont_deterministic initial initial'
  have localSame : hsame ell ell' :=
    cont_respects_hsame picardSame vectorSame step step'
  exact cont_respects_hsame (hsame_refl t1) localSame endpoint endpoint'

theorem OdeLocalFlowRow_concatenation_endpoint_determinacy
    {t0 x0 t2 x2 y vComp pComp ellComp vDirect pDirect ellDirect : BHist} :
    OdeLocalFlowRow t0 x0 t2 x2 vComp pComp ellComp ->
      OdeLocalFlowRow t0 x0 t2 y vDirect pDirect ellDirect ->
        hsame vComp vDirect -> hsame x2 y := by
  intro compRow directRow vectorSame
  exact
    OdeLocalFlow_endpoint_classifier_deterministic
      compRow.left
      directRow.left
      vectorSame
      compRow.right.left
      directRow.right.left
      compRow.right.right
      directRow.right.right

def OdeLocalFlowSource (t0 x0 p v ell t1 x1 : BHist) : Prop :=
  UnaryHistory t0 ∧ UnaryHistory x0 ∧ UnaryHistory p ∧ UnaryHistory v ∧
    UnaryHistory ell ∧ UnaryHistory t1 ∧ UnaryHistory x1 ∧
      Cont t0 x0 p ∧ Cont p v ell ∧ Cont t1 ell x1

theorem OdeLocalFlowSource_vector_field_carrier_stability
    {t0 x0 p v ell t1 x1 v' ell' : BHist} :
    OdeLocalFlowSource t0 x0 p v ell t1 x1 -> hsame v v' -> Cont p v' ell' ->
      UnaryHistory v ∧ UnaryHistory v' ∧ hsame ell ell' := by
  intro source sameVector transportedStep
  have vectorUnary : UnaryHistory v := source.right.right.right.left
  have transportedVectorUnary : UnaryHistory v' :=
    unary_transport vectorUnary sameVector
  have sourceStep : Cont p v ell :=
    source.right.right.right.right.right.right.right.right.left
  have sameEll : hsame ell ell' :=
    cont_respects_hsame (hsame_refl p) sameVector sourceStep transportedStep
  exact And.intro vectorUnary (And.intro transportedVectorUnary sameEll)

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
