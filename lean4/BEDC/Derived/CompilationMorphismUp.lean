import BEDC.FKernel.Ext
import BEDC.FKernel.Cont

namespace BEDC.Derived.CompilationMorphismUp

open BEDC.FKernel.Mark
open BEDC.FKernel.Hist
open BEDC.FKernel.Ext
open BEDC.FKernel.Cont

structure SourceRows where
  sourceHistory : BHist
  targetHistory : BHist
  sourceEndpoint : BHist
  targetEndpoint : BHist
  sourceMark : BMark
  targetMark : BMark
  morphismLedger : BHist
  correctnessLedger : BHist

def Pattern (s : SourceRows) : Prop :=
  Ext s.sourceHistory s.sourceMark s.sourceEndpoint ∧
    Ext s.targetHistory s.targetMark s.targetEndpoint ∧
      Cont s.sourceEndpoint s.morphismLedger s.targetEndpoint ∧
        Cont s.sourceHistory s.correctnessLedger s.targetHistory

def Classifier (s t : SourceRows) : Prop :=
  hsame s.sourceHistory t.sourceHistory ∧
    hsame s.targetHistory t.targetHistory ∧
      hsame s.sourceEndpoint t.sourceEndpoint ∧
        hsame s.targetEndpoint t.targetEndpoint ∧
          msame s.sourceMark t.sourceMark ∧
            msame s.targetMark t.targetMark ∧
              hsame s.morphismLedger t.morphismLedger ∧
                hsame s.correctnessLedger t.correctnessLedger

theorem stability {s t : SourceRows} :
    Classifier s t -> Pattern s -> Pattern t := by
  cases s with
  | mk sourceHistory targetHistory sourceEndpoint targetEndpoint sourceMark targetMark
      morphismLedger correctnessLedger =>
  cases t with
  | mk sourceHistory' targetHistory' sourceEndpoint' targetEndpoint' sourceMark' targetMark'
      morphismLedger' correctnessLedger' =>
      intro same pattern
      unfold Classifier at same
      unfold Pattern at pattern ⊢
      cases same with
      | intro sameSourceHistory rest =>
          cases rest with
          | intro sameTargetHistory rest =>
              cases rest with
              | intro sameSourceEndpoint rest =>
                  cases rest with
                  | intro sameTargetEndpoint rest =>
                      cases rest with
                      | intro sameSourceMark rest =>
                          cases rest with
                          | intro sameTargetMark rest =>
                              cases rest with
                              | intro sameMorphismLedger sameCorrectnessLedger =>
                                  cases sameSourceHistory
                                  cases sameTargetHistory
                                  cases sameSourceEndpoint
                                  cases sameTargetEndpoint
                                  cases sameSourceMark
                                  cases sameTargetMark
                                  cases sameMorphismLedger
                                  cases sameCorrectnessLedger
                                  exact pattern

def Ledger : Type := SourceRows

end BEDC.Derived.CompilationMorphismUp
