import BEDC.FKernel.Mark
import BEDC.FKernel.Hist
import BEDC.FKernel.Ext

namespace BEDC.Derived.ObserverHistIdentityUp

open BEDC.FKernel.Mark
open BEDC.FKernel.Hist
open BEDC.FKernel.Ext

structure SourceRows where
  source : BHist
  mark : BMark
  target : BHist

def Pattern (s : SourceRows) : Prop :=
  Ext s.source s.mark s.target

def Classifier (s t : SourceRows) : Prop :=
  hsame s.source t.source ∧ msame s.mark t.mark ∧ hsame s.target t.target

theorem stability {s t : SourceRows} :
    Pattern s → Classifier s t → Pattern t := by
  cases s with
  | mk sSource sMark sTarget =>
      cases t with
      | mk tSource tMark tTarget =>
          intro pattern classified
          unfold Pattern at pattern ⊢
          unfold Classifier at classified
          cases classified with
          | intro sameSource rest =>
              cases rest with
              | intro sameMark sameTarget =>
                  cases sameSource
                  cases sameMark
                  cases sameTarget
                  exact pattern

def Ledger : Type :=
  { s : SourceRows // Pattern s }

end BEDC.Derived.ObserverHistIdentityUp
