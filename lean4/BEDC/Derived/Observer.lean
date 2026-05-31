namespace BEDC.Derived.Observer

inductive HistInformationContent : Type where
  | unit

def SubjectFreeObservation : Prop := True

def SelfReferenceClosure : Prop := True

inductive HistTimeStep : Type where
  | unit

def LocalTimeStream : Prop := True

def GroundLoopClosed : Prop := True

def MetaLoopUnclosable : Prop := True

end BEDC.Derived.Observer
