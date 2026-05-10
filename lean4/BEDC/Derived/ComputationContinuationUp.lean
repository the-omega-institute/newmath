import BEDC.FKernel.Cont

namespace BEDC.Derived.ComputationContinuationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

structure SourceRows where
  source : BHist
  step : BHist
  target : BHist
  transition : Cont source step target

def Pattern (s : SourceRows) : Prop :=
  Cont s.source s.step s.target

def Classifier (s t : SourceRows) : Prop :=
  hsame s.source t.source ∧ hsame s.step t.step ∧ hsame s.target t.target

def compose (first second : SourceRows)
    (middle : hsame first.target second.source) : SourceRows where
  source := first.source
  step := append first.step second.step
  target := second.target
  transition := by
    exact Eq.trans second.transition
      (Eq.trans (congrArg (fun h : BHist => append h second.step) middle.symm)
        (Eq.trans (congrArg (fun h : BHist => append h second.step) first.transition)
          (append_assoc first.source first.step second.step)))

theorem stability {first second : SourceRows}
    (middle : hsame first.target second.source) :
    Pattern (compose first second middle) ∧
      Classifier (compose first second middle) (compose first second middle) := by
  constructor
  · exact (compose first second middle).transition
  · constructor
    · rfl
    · constructor
      · rfl
      · rfl

def Ledger : Type := SourceRows

end BEDC.Derived.ComputationContinuationUp
