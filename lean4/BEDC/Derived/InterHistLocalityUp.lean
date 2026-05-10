import BEDC.FKernel.Cont

namespace BEDC.Derived.InterHistLocalityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

structure SourceRows where
  historyA : BHist
  historyB : BHist
  localityWitness : BHist
  endpointA : BHist
  endpointB : BHist
  localA : Cont historyA localityWitness endpointA
  localB : Cont historyB localityWitness endpointB

def Pattern (s : SourceRows) : Prop :=
  Cont s.historyA s.localityWitness s.endpointA ∧
    Cont s.historyB s.localityWitness s.endpointB

def Classifier (s t : SourceRows) : Prop :=
  hsame s.endpointA t.endpointA ∧ hsame s.endpointB t.endpointB

def extend (s : SourceRows) (extension : BHist) : SourceRows where
  historyA := s.historyA
  historyB := s.historyB
  localityWitness := append s.localityWitness extension
  endpointA := append s.endpointA extension
  endpointB := append s.endpointB extension
  localA := by
    exact Eq.trans (congrArg (fun h : BHist => append h extension) s.localA)
      (append_assoc s.historyA s.localityWitness extension)
  localB := by
    exact Eq.trans (congrArg (fun h : BHist => append h extension) s.localB)
      (append_assoc s.historyB s.localityWitness extension)

theorem stability {s t : SourceRows} :
    Classifier s t →
      ∀ extension : BHist,
        Pattern (extend s extension) ∧
          Pattern (extend t extension) ∧
            Classifier (extend s extension) (extend t extension) := by
  intro same extension
  constructor
  · constructor
    · exact (extend s extension).localA
    · exact (extend s extension).localB
  · constructor
    · constructor
      · exact (extend t extension).localA
      · exact (extend t extension).localB
    · constructor
      · exact congrArg (fun h : BHist => append h extension) same.left
      · exact congrArg (fun h : BHist => append h extension) same.right

def Ledger : Type := SourceRows

end BEDC.Derived.InterHistLocalityUp
