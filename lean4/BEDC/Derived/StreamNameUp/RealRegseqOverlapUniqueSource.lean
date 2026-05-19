import BEDC.Derived.StreamNameUp.OverlapExactness

namespace BEDC.Derived.StreamNameUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

theorem StreamNameRealRegseqOverlapUniqueSource {h k sourceFromRegseq sourceFromReal : BHist}
    {left right overlap : ProbeBundle BHist} :
    (exists n : BHist, InBundle n overlap ∧ UnaryHistory n) ->
      (forall n : BHist, InBundle n overlap -> InBundle n left) ->
        (forall n : BHist, InBundle n overlap -> InBundle n right) ->
          RatStreamNameFiniteWindowClassifier (RatConstStream h) (RatConstStream k) left ->
            RatStreamNameFiniteWindowClassifier (RatConstStream h) (RatConstStream k) right ->
              Cont h k sourceFromRegseq ->
                Cont h k sourceFromReal ->
                  RatHistoryClassifier h k ∧ hsame sourceFromRegseq sourceFromReal ∧
                    Cont h k sourceFromRegseq ∧ Cont h k sourceFromReal := by
  -- BEDC touchpoint anchor: BHist ProbeBundle InBundle Cont hsame RatHistoryClassifier
  intro overlapWitness overlapLeft overlapRight leftClassified rightClassified
    regseqSource realSource
  have overlapExact :
      RatStreamNameFiniteWindowClassifier (RatConstStream h) (RatConstStream k) overlap ∧
        RatHistoryClassifier h k :=
    StreamNameConstantWindow_overlap_exactness overlapWitness overlapLeft overlapRight
      leftClassified rightClassified
  have sameSource : hsame sourceFromRegseq sourceFromReal :=
    cont_deterministic regseqSource realSource
  exact ⟨overlapExact.right, sameSource, regseqSource, realSource⟩

end BEDC.Derived.StreamNameUp
