import BEDC.FKernel.Hist

namespace BEDC.StructuralDna.TestTargets

open BEDC.FKernel.Hist

def SomeP : BHist → Prop := fun h => BHist.e0 h = h

def SomeQ : BHist → Prop := fun h => BHist.e1 h = h

def TA : BHist → Prop := fun hist => SomeP hist

def TB : BHist → Prop := fun z => SomeP z

def FA : Prop := ∀ hist : BHist, SomeP hist

def FB : Prop := ∀ z : BHist, SomeP z

def C1 : BHist → BHist → Prop := fun h k => SomeP h ∧ SomeQ k

def C2 : BHist → BHist → Prop := fun h k => SomeQ h ∧ SomeP k

def Hollow : BHist → Prop := fun _ => True

end BEDC.StructuralDna.TestTargets
