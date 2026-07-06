import BEDC.Derived.CommRingUp

namespace BEDC.Derived.CommRingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem CommRingSingletonClassifier_continuation_empty_result_iff {P Q R : BHist} :
    Cont P Q R -> (CommRingSingletonClassifier P Q <-> hsame R BHist.Empty) := by
  intro continuation
  constructor
  · intro classified
    cases continuation
    exact append_eq_empty_iff.mpr (And.intro classified.left classified.right.left)
  · intro resultEmpty
    cases continuation
    have endpoints := append_eq_empty_iff.mp resultEmpty
    exact And.intro endpoints.left
      (And.intro endpoints.right (hsame_trans endpoints.left (hsame_symm endpoints.right)))

theorem CommRingSingletonCarrier_continuation_split_iff {P Q R : BHist} :
    Cont P Q R ->
      (CommRingSingletonCarrier R ↔
        CommRingSingletonCarrier P ∧ CommRingSingletonCarrier Q) := by
  intro continuation
  constructor
  · intro resultCarrier
    cases continuation
    exact append_eq_empty_iff.mp resultCarrier
  · intro carriers
    cases continuation
    exact append_eq_empty_iff.mpr carriers

theorem CommRingSingletonCont_commutative_laws {x y z xy yx left right : BHist} :
    CommRingSingletonCarrier x ->
      CommRingSingletonCarrier y ->
        CommRingSingletonCarrier z ->
          Cont x y xy ->
            Cont y x yx ->
              Cont x z left ->
                Cont y z right ->
                  CommRingSingletonClassifier xy yx ∧ CommRingSingletonCarrier left ∧
                    CommRingSingletonCarrier right := by
  -- BEDC touchpoint anchor: BHist Cont hsame CommRingSingletonCarrier CommRingSingletonClassifier
  intro xCarrier yCarrier zCarrier xyRoute yxRoute leftRoute rightRoute
  have xyCarrier : CommRingSingletonCarrier xy := by
    cases xyRoute
    exact append_eq_empty_iff.mpr (And.intro xCarrier yCarrier)
  have yxCarrier : CommRingSingletonCarrier yx := by
    cases yxRoute
    exact append_eq_empty_iff.mpr (And.intro yCarrier xCarrier)
  have xy_yx_same : hsame xy yx :=
    hsame_trans xyCarrier (hsame_symm yxCarrier)
  have leftCarrier : CommRingSingletonCarrier left := by
    cases leftRoute
    exact append_eq_empty_iff.mpr (And.intro xCarrier zCarrier)
  have rightCarrier : CommRingSingletonCarrier right := by
    cases rightRoute
    exact append_eq_empty_iff.mpr (And.intro yCarrier zCarrier)
  exact ⟨⟨xyCarrier, yxCarrier, xy_yx_same⟩, leftCarrier, rightCarrier⟩

end BEDC.Derived.CommRingUp
