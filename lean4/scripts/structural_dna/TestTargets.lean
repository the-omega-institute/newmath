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

def BaseClassifier : BHist → BHist → Prop :=
  fun h _k => SomeP h

def ExtendedClassifier : BHist → BHist → Prop :=
  fun h k => SomeP h ∧ SomeQ k

def ReorderedClassifier : BHist → BHist → Prop :=
  fun h k => SomeQ k ∧ SomeP h

def SharedOnlyClassifier : BHist → BHist → Prop :=
  fun h k => SomeP h ∨ SomeQ k

def FixedShapeClassifier : BHist → BHist → Prop :=
  fun _h _k => SomeP BHist.Empty

def ExtendedEtaClassifier : BHist → BHist → Prop :=
  fun h k => ExtendedClassifier h k

def PairPriorClassifier : BHist → BHist → Prop :=
  fun h k => SomeP h ∧ SomeQ k

def TripleCandidateClassifier : BHist → BHist → Prop :=
  fun h k => SomeP h ∧ SomeQ k ∧ SomeP k

def HeadDependsClassifier : BHist → Prop :=
  fun h =>
    (match h with
    | BHist.Empty => SomeP
    | BHist.e0 _ => SomeQ
    | BHist.e1 _ => SomeP) h

def Hollow : BHist → Prop := fun _ => True

def HollowRefiner : BHist → Prop := fun h => True ∧ SomeP h

def DefinitionalTrue : BHist → Prop := fun _ => True

def DefinitionalTrueRefiner : BHist → Prop := fun h => DefinitionalTrue h ∧ SomeP h

def ReflexiveEqPrior : BHist → Prop := fun _ => BHist.Empty = BHist.Empty

def ReflexiveEqRefiner : BHist → Prop := fun h => ReflexiveEqPrior h ∧ SomeP h

def ParamReflexiveEqPrior : BHist → Prop := fun h => h = h

def ParamReflexiveEqRefiner : BHist → Prop :=
  fun h => ParamReflexiveEqPrior h ∧ SomeP h

def MatchTruePrior : BHist → Prop :=
  fun h =>
    match h with
    | BHist.Empty => True
    | BHist.e0 _ => True
    | BHist.e1 _ => True

def MatchTrueRefiner : BHist → Prop := fun h => MatchTruePrior h ∧ SomeP h

def DuplicatePriorClassifier : BHist → BHist → Prop :=
  fun h k => SomeP h ∧ SomeP h ∧ SomeQ k

def DuplicateCandidateClassifier : BHist → BHist → Prop :=
  fun h k => SomeP h ∧ SomeQ k ∧ SomeP k

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
