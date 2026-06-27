import BEDC.Algebra.Rel.Basic
import BEDC.Derived.OnticCollapseModes

namespace BEDC.Derived.ObservationClassifiedSymmetryUp

open BEDC.Algebra.Rel
open BEDC.Derived.OnticCollapseModes

universe u v

def ClassifierFiberRel {α : Sort u} {κ : Type v}
    (classifier : α -> κ) (classEquiv : RelEquiv κ) (x y : α) : Prop :=
  classEquiv.rel (classifier x) (classifier y)

theorem classifierFiberRel_refl {α : Sort u} {κ : Type v}
    (classifier : α -> κ) (classEquiv : RelEquiv κ) (x : α) :
    ClassifierFiberRel classifier classEquiv x x :=
  classEquiv.refl (classifier x)

theorem classifierFiberRel_symm {α : Sort u} {κ : Type v}
    {classifier : α -> κ} {classEquiv : RelEquiv κ} {x y : α} :
    ClassifierFiberRel classifier classEquiv x y ->
      ClassifierFiberRel classifier classEquiv y x := by
  intro same
  exact classEquiv.symm same

theorem classifierFiberRel_trans {α : Sort u} {κ : Type v}
    {classifier : α -> κ} {classEquiv : RelEquiv κ} {x y z : α} :
    ClassifierFiberRel classifier classEquiv x y ->
      ClassifierFiberRel classifier classEquiv y z ->
        ClassifierFiberRel classifier classEquiv x z := by
  intro sameXY sameYZ
  exact classEquiv.trans sameXY sameYZ

def classifierFiberRelEquiv {α : Type u} {κ : Type v}
    (classifier : α -> κ) (classEquiv : RelEquiv κ) : RelEquiv α where
  rel := ClassifierFiberRel classifier classEquiv
  refl := classifierFiberRel_refl classifier classEquiv
  symm := by
    intro _x _y same
    exact classifierFiberRel_symm same
  trans := by
    intro _x _y _z sameXY sameYZ
    exact classifierFiberRel_trans sameXY sameYZ

structure ObservationClassifiedSymmetry
    (O : OnticPacket.{u}) (κ : Type v) where
  classifier : O.Symmetry -> κ
  classEquiv : RelEquiv κ
  observe : O.Time -> O.Symmetry -> O.Symmetry
  distinction : O.Symmetry -> O.Symmetry -> Prop
  distinction_preserved :
    ∀ time {x y : O.Symmetry},
      distinction x y -> distinction (observe time x) (observe time y)
  fiber_preserved :
    ∀ time {x y : O.Symmetry},
      ClassifierFiberRel classifier classEquiv x y ->
        ClassifierFiberRel classifier classEquiv (observe time x) (observe time y)

namespace ObservationClassifiedSymmetry

variable {O : OnticPacket.{u}} {κ : Type v}

def fiberRel (S : ObservationClassifiedSymmetry O κ)
    (x y : O.Symmetry) : Prop :=
  ClassifierFiberRel S.classifier S.classEquiv x y

def fiberToken (S : ObservationClassifiedSymmetry O κ)
    (x : O.Symmetry) : FiberClassToken O.Symmetry S.fiberRel where
  point := x

def fiberEq (S : ObservationClassifiedSymmetry O κ)
    (x y : O.Symmetry) : Prop :=
  FiberClassEq (r := S.fiberRel) (S.fiberToken x) (S.fiberToken y)

def symmetryRowPoint (S : ObservationClassifiedSymmetry O κ)
    (x : O.Symmetry) : O.Symmetry :=
  match S.classifier x with
  | _ => x

theorem symmetryRowPoint_identity
    (S : ObservationClassifiedSymmetry O κ) (x : O.Symmetry) :
    S.symmetryRowPoint x = x := by
  rfl

theorem preserves_distinction
    (S : ObservationClassifiedSymmetry O κ) (time : O.Time)
    {x y : O.Symmetry} :
    S.distinction x y -> S.distinction (S.observe time x) (S.observe time y) := by
  intro separated
  exact S.distinction_preserved time separated

theorem preserves_classifier_fiber
    (S : ObservationClassifiedSymmetry O κ) (time : O.Time)
    {x y : O.Symmetry} :
    S.fiberRel x y -> S.fiberRel (S.observe time x) (S.observe time y) := by
  intro sameFiber
  exact S.fiber_preserved time sameFiber

end ObservationClassifiedSymmetry

structure ClassifierFiberNoncollapse
    {O : OnticPacket.{u}} {κ : Type v}
    (S : ObservationClassifiedSymmetry O κ) where
  time : O.Time
  left : O.Symmetry
  right : O.Symmetry
  sameFiber : S.fiberRel left right
  distinctionWitness : S.distinction left right
  observedFiberEqRefusesDistinction :
    S.fiberEq (S.observe time left) (S.observe time right) ->
      S.distinction (S.observe time left) (S.observe time right) -> False

namespace ClassifierFiberNoncollapse

variable {O : OnticPacket.{u}} {κ : Type v}
variable {S : ObservationClassifiedSymmetry O κ}

theorem observed_same_fiber (w : ClassifierFiberNoncollapse S) :
    S.fiberRel (S.observe w.time w.left) (S.observe w.time w.right) := by
  exact S.preserves_classifier_fiber w.time w.sameFiber

theorem observed_distinction (w : ClassifierFiberNoncollapse S) :
    S.distinction (S.observe w.time w.left) (S.observe w.time w.right) := by
  exact S.preserves_distinction w.time w.distinctionWitness

theorem rejects_symCollapse (w : ClassifierFiberNoncollapse S) :
    SymCollapse O.Symmetry -> False := by
  intro collapse
  have sameObserved :
      S.fiberRel (S.observe w.time w.left) (S.observe w.time w.right) :=
    observed_same_fiber w
  have separatedObserved :
      S.distinction (S.observe w.time w.left) (S.observe w.time w.right) :=
    observed_distinction w
  have collapsedFiber :
      S.fiberEq (S.observe w.time w.left) (S.observe w.time w.right) :=
    collapse sameObserved
  exact w.observedFiberEqRefusesDistinction collapsedFiber separatedObserved

theorem ontic_symmetry_row_rejection (w : ClassifierFiberNoncollapse S) :
    (SymCollapse O.Symmetry -> False) ∧
      (∃ x : O.Symmetry, ∃ y : O.Symmetry,
        S.fiberRel x y ∧ S.distinction x y) := by
  exact
    ⟨rejects_symCollapse w,
      ⟨w.left, ⟨w.right, ⟨w.sameFiber, w.distinctionWitness⟩⟩⟩⟩

theorem to_nonCollapsePacket (w : ClassifierFiberNoncollapse S)
    (noTime : TimeCollapse O.Time -> False)
    (noDistinction : DistCollapse -> False) :
    NonCollapsePacket O where
  noTime := noTime
  noSymmetry := rejects_symCollapse w
  noDistinction := noDistinction

end ClassifierFiberNoncollapse

theorem classifierFiberNoncollapse_rejects_symCollapse
    {O : OnticPacket.{u}} {κ : Type v}
    {S : ObservationClassifiedSymmetry O κ}
    (w : ClassifierFiberNoncollapse S) :
    SymCollapse O.Symmetry -> False :=
  ClassifierFiberNoncollapse.rejects_symCollapse w

theorem classifierFiberNoncollapse_to_nonCollapsePacket
    {O : OnticPacket.{u}} {κ : Type v}
    {S : ObservationClassifiedSymmetry O κ}
    (w : ClassifierFiberNoncollapse S)
    (noTime : TimeCollapse O.Time -> False)
    (noDistinction : DistCollapse -> False) :
    NonCollapsePacket O :=
  ClassifierFiberNoncollapse.to_nonCollapsePacket w noTime noDistinction

end BEDC.Derived.ObservationClassifiedSymmetryUp
