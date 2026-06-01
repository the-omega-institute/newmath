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

def C1DirectEta : BHist → BHist → Prop := fun h k => C1 h k

def C1LetEta : BHist → BHist → Prop := fun h k => (let f := C1; f) h k

def C1MidEta : BHist → BHist → Prop := fun h k => C1 h k

def C1MultiEta : BHist → BHist → Prop := fun h k => C1MidEta h k

def Hollow : BHist → Prop := fun _ => True

def ExplicitArrow : Type := ∀ _ : BHist, BHist

def ImplicitArrow : Type := {_ : BHist} → BHist

def InstanceArrow : Type := [Inhabited BHist] → BHist

def AlphaLamA : BHist → Prop := fun hist => SomeP hist

def AlphaLamB : BHist → Prop := fun z => SomeP z

def PropDefTrue : Prop := True

def PropDefFalse : Prop := False

def PropDefEq : Prop := BHist.Empty = BHist.Empty

theorem ProofA : BHist.Empty = BHist.Empty := rfl

theorem ProofB : BHist.Empty = BHist.Empty := Eq.refl _

end BEDC.StructuralDna.TestTargets
