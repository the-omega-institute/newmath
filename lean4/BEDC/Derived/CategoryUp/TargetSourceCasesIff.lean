import BEDC.Derived.CategoryUp.TargetCases

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem CategoryHomCarrier_e1_target_e1_morphism_source_cases_iff {source r k : BHist} :
    CategoryHomCarrier source (BHist.e1 r) (BHist.e1 k) <->
      (source = BHist.Empty /\ hsame k r /\ UnaryHistory r) \/
        (Exists (fun a : BHist =>
          source = BHist.e1 a /\ UnaryHistory a /\ UnaryHistory k /\ UnaryHistory r /\
            Cont (BHist.e1 a) k r)) := by
  constructor
  · intro homCarrier
    cases source with
    | Empty =>
        left
        have emptyData :=
          (CategoryHomCarrier_empty_source_e1_target_iff (r := r) (morph := BHist.e1 k)).mp
            homCarrier
        exact ⟨rfl, hsame_e1_iff.mp emptyData.left, emptyData.right⟩
    | e0 a =>
        exact False.elim (CategoryHomCarrier_e0_source_absurd homCarrier)
    | e1 a =>
        right
        have data :=
          (CategoryHomCarrier_e1_morphism_target_iff (a := BHist.e1 a) (k := k) (r := r)).mp
            homCarrier
        exact Exists.intro a
          ⟨rfl, unary_e1_inversion data.left, data.right.left,
            unary_e1_inversion homCarrier.right.left, data.right.right⟩
  · intro splitCases
    cases splitCases with
    | inl emptyCase =>
        cases emptyCase with
        | intro sourceEq rest =>
            cases rest with
            | intro sameKR targetCarrier =>
                cases sourceEq
                cases sameKR
                exact
                  (CategoryHomCarrier_empty_source_e1_target_iff (r := r)
                    (morph := BHist.e1 r)).mpr
                    ⟨rfl, targetCarrier⟩
    | inr visibleCase =>
        cases visibleCase with
        | intro a data =>
            cases data with
            | intro sourceEq rest =>
                cases rest with
                | intro sourceCarrier rest =>
                    cases rest with
                    | intro morphCarrier rest =>
                        cases rest with
                        | intro _targetCarrier homCont =>
                            cases sourceEq
                            exact
                              (CategoryHomCarrier_e1_morphism_target_iff
                                (a := BHist.e1 a) (k := k) (r := r)).mpr
                                ⟨unary_e1_closed sourceCarrier, morphCarrier, homCont⟩

end BEDC.Derived.CategoryUp
