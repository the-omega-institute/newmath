import BEDC.Derived.RHRoute.FunctionalEquationSymmetry
import BEDC.Derived.RHRoute.FinitePrimeWindow
import BEDC.Derived.RHRoute.RecursiveTower
import BEDC.Derived.NonCollapseInvariantUp

namespace BEDC.Derived.RHRoute.ZeroGenerationInitiality

open BEDC.Derived.RationalUp
open BEDC.Derived.RHRoute.FunctionalEquationSymmetry
open BEDC.Derived.RHRoute.FinitePrimeWindow
open BEDC.Derived.RHRoute.RecursiveTower

universe u v

-- 生成零点签名只记录 pre-RH 构造子；固定半平面见证不作为输入。
inductive ZeroConstructorKind where
  | primeLocal
  | functionalMirror
  | conjugationTransport
  | classifierTransport
  | analyticGlue
  | compatibleLimitSeal
  | ledgerReplay
  | finiteWindowClose
  | recursiveTowerReadback
  | nonCollapseGuard

inductive PreRHConstructor : ZeroConstructorKind -> Prop where
  | primeLocal : PreRHConstructor ZeroConstructorKind.primeLocal
  | functionalMirror : PreRHConstructor ZeroConstructorKind.functionalMirror
  | conjugationTransport : PreRHConstructor ZeroConstructorKind.conjugationTransport
  | classifierTransport : PreRHConstructor ZeroConstructorKind.classifierTransport
  | analyticGlue : PreRHConstructor ZeroConstructorKind.analyticGlue
  | compatibleLimitSeal : PreRHConstructor ZeroConstructorKind.compatibleLimitSeal
  | ledgerReplay : PreRHConstructor ZeroConstructorKind.ledgerReplay
  | finiteWindowClose : PreRHConstructor ZeroConstructorKind.finiteWindowClose
  | recursiveTowerReadback : PreRHConstructor ZeroConstructorKind.recursiveTowerReadback
  | nonCollapseGuard : PreRHConstructor ZeroConstructorKind.nonCollapseGuard

def NoRHCirc (constructors : List ZeroConstructorKind) : Prop :=
  All PreRHConstructor constructors

structure RHFreeZeroSignature where
  constructors : List ZeroConstructorKind
  no_rh_circ : NoRHCirc constructors

def zeroConstructorKindCode : ZeroConstructorKind -> Nat
  | ZeroConstructorKind.primeLocal => 0
  | ZeroConstructorKind.functionalMirror => 1
  | ZeroConstructorKind.conjugationTransport => 2
  | ZeroConstructorKind.classifierTransport => 3
  | ZeroConstructorKind.analyticGlue => 4
  | ZeroConstructorKind.compatibleLimitSeal => 5
  | ZeroConstructorKind.ledgerReplay => 6
  | ZeroConstructorKind.finiteWindowClose => 7
  | ZeroConstructorKind.recursiveTowerReadback => 8
  | ZeroConstructorKind.nonCollapseGuard => 9

def natCodeEq : Nat -> Nat -> Bool
  | 0, 0 => true
  | 0, Nat.succ _ => false
  | Nat.succ _, 0 => false
  | Nat.succ a, Nat.succ b => natCodeEq a b

def countNatCode (needle : Nat) : List Nat -> Nat
  | [] => 0
  | x :: xs =>
      match natCodeEq needle x with
      | true => Nat.succ (countNatCode needle xs)
      | false => countNatCode needle xs

def countConstructorKind (needle : ZeroConstructorKind) :
    (constructors : List ZeroConstructorKind) -> Nat :=
  fun constructors =>
    countNatCode (zeroConstructorKindCode needle)
      (constructors.map zeroConstructorKindCode)

def rhFreeZeroSignatureKinds : List ZeroConstructorKind :=
  [ ZeroConstructorKind.primeLocal,
    ZeroConstructorKind.functionalMirror,
    ZeroConstructorKind.conjugationTransport,
    ZeroConstructorKind.classifierTransport,
    ZeroConstructorKind.analyticGlue,
    ZeroConstructorKind.compatibleLimitSeal,
    ZeroConstructorKind.ledgerReplay,
    ZeroConstructorKind.finiteWindowClose,
    ZeroConstructorKind.recursiveTowerReadback,
    ZeroConstructorKind.nonCollapseGuard ]

theorem rhFreeZeroSignatureKinds_no_rh_circ :
    NoRHCirc rhFreeZeroSignatureKinds := by
  unfold NoRHCirc rhFreeZeroSignatureKinds
  exact
    All.cons PreRHConstructor.primeLocal
      (All.cons PreRHConstructor.functionalMirror
        (All.cons PreRHConstructor.conjugationTransport
          (All.cons PreRHConstructor.classifierTransport
            (All.cons PreRHConstructor.analyticGlue
              (All.cons PreRHConstructor.compatibleLimitSeal
                (All.cons PreRHConstructor.ledgerReplay
                  (All.cons PreRHConstructor.finiteWindowClose
                    (All.cons PreRHConstructor.recursiveTowerReadback
                      (All.cons PreRHConstructor.nonCollapseGuard All.nil)))))))))

def rhFreeZeroSignature : RHFreeZeroSignature where
  constructors := rhFreeZeroSignatureKinds
  no_rh_circ := rhFreeZeroSignatureKinds_no_rh_circ

theorem rhFreeZeroSignature_primeLocal_count :
    countConstructorKind ZeroConstructorKind.primeLocal
      rhFreeZeroSignature.constructors = 1 := by
  rfl

inductive ZeroSigF (signature : RHFreeZeroSignature) (α : Type u) : Type u where
  | primeLocal : (window : PrimeWindow) -> (p : Nat) ->
      window.mem p -> ZeroSigF signature α
  | functionalMirror : α -> ZeroSigF signature α
  | conjugationTransport : α -> ZeroSigF signature α
  | classifierTransport : Nat -> α -> ZeroSigF signature α
  | analyticGlue : α -> α -> ZeroSigF signature α
  | compatibleLimitSeal : Nat -> α -> ZeroSigF signature α
  | ledgerReplay : α -> List TraceEvent -> ZeroSigF signature α
  | finiteWindowClose : PrimeWindow -> α -> ZeroSigF signature α
  | recursiveTowerReadback : TraceEvent -> α -> ZeroSigF signature α
  | nonCollapseGuard : Nat -> α -> ZeroSigF signature α

namespace ZeroSigF

def map {signature : RHFreeZeroSignature} {α : Type u} {β : Type v}
    (f : α -> β) : ZeroSigF signature α -> ZeroSigF signature β
  | ZeroSigF.primeLocal window p member =>
      ZeroSigF.primeLocal window p member
  | ZeroSigF.functionalMirror z =>
      ZeroSigF.functionalMirror (f z)
  | ZeroSigF.conjugationTransport z =>
      ZeroSigF.conjugationTransport (f z)
  | ZeroSigF.classifierTransport tag z =>
      ZeroSigF.classifierTransport tag (f z)
  | ZeroSigF.analyticGlue left right =>
      ZeroSigF.analyticGlue (f left) (f right)
  | ZeroSigF.compatibleLimitSeal fuel z =>
      ZeroSigF.compatibleLimitSeal fuel (f z)
  | ZeroSigF.ledgerReplay z trace =>
      ZeroSigF.ledgerReplay (f z) trace
  | ZeroSigF.finiteWindowClose window z =>
      ZeroSigF.finiteWindowClose window (f z)
  | ZeroSigF.recursiveTowerReadback event z =>
      ZeroSigF.recursiveTowerReadback event (f z)
  | ZeroSigF.nonCollapseGuard budget z =>
      ZeroSigF.nonCollapseGuard budget (f z)

end ZeroSigF

inductive GeneratedZero (signature : RHFreeZeroSignature) : Type where
  | primeLocal : (window : PrimeWindow) -> (p : Nat) ->
      window.mem p -> GeneratedZero signature
  | functionalMirror : GeneratedZero signature -> GeneratedZero signature
  | conjugationTransport : GeneratedZero signature -> GeneratedZero signature
  | classifierTransport : Nat -> GeneratedZero signature -> GeneratedZero signature
  | analyticGlue : GeneratedZero signature -> GeneratedZero signature ->
      GeneratedZero signature
  | compatibleLimitSeal : Nat -> GeneratedZero signature -> GeneratedZero signature
  | ledgerReplay : GeneratedZero signature -> List TraceEvent ->
      GeneratedZero signature
  | finiteWindowClose : PrimeWindow -> GeneratedZero signature ->
      GeneratedZero signature
  | recursiveTowerReadback : TraceEvent -> GeneratedZero signature ->
      GeneratedZero signature
  | nonCollapseGuard : Nat -> GeneratedZero signature -> GeneratedZero signature

namespace GeneratedZero

def inZ {signature : RHFreeZeroSignature} :
    ZeroSigF signature (GeneratedZero signature) -> GeneratedZero signature
  | ZeroSigF.primeLocal window p member =>
      GeneratedZero.primeLocal window p member
  | ZeroSigF.functionalMirror z =>
      GeneratedZero.functionalMirror z
  | ZeroSigF.conjugationTransport z =>
      GeneratedZero.conjugationTransport z
  | ZeroSigF.classifierTransport tag z =>
      GeneratedZero.classifierTransport tag z
  | ZeroSigF.analyticGlue left right =>
      GeneratedZero.analyticGlue left right
  | ZeroSigF.compatibleLimitSeal fuel z =>
      GeneratedZero.compatibleLimitSeal fuel z
  | ZeroSigF.ledgerReplay z trace =>
      GeneratedZero.ledgerReplay z trace
  | ZeroSigF.finiteWindowClose window z =>
      GeneratedZero.finiteWindowClose window z
  | ZeroSigF.recursiveTowerReadback event z =>
      GeneratedZero.recursiveTowerReadback event z
  | ZeroSigF.nonCollapseGuard budget z =>
      GeneratedZero.nonCollapseGuard budget z

end GeneratedZero

abbrev GeneratedZeroCarrier (signature : RHFreeZeroSignature) : Type :=
  GeneratedZero signature

structure ZeroAlgebra (signature : RHFreeZeroSignature) (α : Type u) where
  alg : ZeroSigF signature α -> α

namespace GeneratedZero

def fold {signature : RHFreeZeroSignature} {α : Type u}
    (A : ZeroAlgebra signature α) : GeneratedZero signature -> α
  | GeneratedZero.primeLocal window p member =>
      A.alg (ZeroSigF.primeLocal window p member)
  | GeneratedZero.functionalMirror z =>
      A.alg (ZeroSigF.functionalMirror (fold A z))
  | GeneratedZero.conjugationTransport z =>
      A.alg (ZeroSigF.conjugationTransport (fold A z))
  | GeneratedZero.classifierTransport tag z =>
      A.alg (ZeroSigF.classifierTransport tag (fold A z))
  | GeneratedZero.analyticGlue left right =>
      A.alg (ZeroSigF.analyticGlue (fold A left) (fold A right))
  | GeneratedZero.compatibleLimitSeal fuel z =>
      A.alg (ZeroSigF.compatibleLimitSeal fuel (fold A z))
  | GeneratedZero.ledgerReplay z trace =>
      A.alg (ZeroSigF.ledgerReplay (fold A z) trace)
  | GeneratedZero.finiteWindowClose window z =>
      A.alg (ZeroSigF.finiteWindowClose window (fold A z))
  | GeneratedZero.recursiveTowerReadback event z =>
      A.alg (ZeroSigF.recursiveTowerReadback event (fold A z))
  | GeneratedZero.nonCollapseGuard budget z =>
      A.alg (ZeroSigF.nonCollapseGuard budget (fold A z))

end GeneratedZero

def generatedZeroAlgebra (signature : RHFreeZeroSignature) :
    ZeroAlgebra signature (GeneratedZero signature) where
  alg := GeneratedZero.inZ

def IsZeroAlgebraHom {signature : RHFreeZeroSignature} {α : Type u}
    (A : ZeroAlgebra signature α)
    (f : GeneratedZero signature -> α) : Prop :=
  ∀ op : ZeroSigF signature (GeneratedZero signature),
    f (GeneratedZero.inZ op) = A.alg (ZeroSigF.map f op)

theorem generatedZero_fold_hom {signature : RHFreeZeroSignature} {α : Type u}
    (A : ZeroAlgebra signature α) :
    IsZeroAlgebraHom A (GeneratedZero.fold A) := by
  intro op
  cases op <;> rfl

theorem generatedZero_fold_unique {signature : RHFreeZeroSignature} {α : Type u}
    (A : ZeroAlgebra signature α) (f : GeneratedZero signature -> α)
    (hom : IsZeroAlgebraHom A f) :
    ∀ z : GeneratedZero signature, f z = GeneratedZero.fold A z := by
  intro z
  induction z with
  | primeLocal window p member =>
      exact hom (ZeroSigF.primeLocal window p member)
  | functionalMirror z ih =>
      calc
        f (GeneratedZero.functionalMirror z)
            = A.alg (ZeroSigF.functionalMirror (f z)) :=
              hom (ZeroSigF.functionalMirror z)
        _ = A.alg (ZeroSigF.functionalMirror (GeneratedZero.fold A z)) := by
              rw [ih]
        _ = GeneratedZero.fold A (GeneratedZero.functionalMirror z) := rfl
  | conjugationTransport z ih =>
      calc
        f (GeneratedZero.conjugationTransport z)
            = A.alg (ZeroSigF.conjugationTransport (f z)) :=
              hom (ZeroSigF.conjugationTransport z)
        _ = A.alg (ZeroSigF.conjugationTransport (GeneratedZero.fold A z)) := by
              rw [ih]
        _ = GeneratedZero.fold A (GeneratedZero.conjugationTransport z) := rfl
  | classifierTransport tag z ih =>
      calc
        f (GeneratedZero.classifierTransport tag z)
            = A.alg (ZeroSigF.classifierTransport tag (f z)) :=
              hom (ZeroSigF.classifierTransport tag z)
        _ = A.alg (ZeroSigF.classifierTransport tag (GeneratedZero.fold A z)) := by
              rw [ih]
        _ = GeneratedZero.fold A (GeneratedZero.classifierTransport tag z) := rfl
  | analyticGlue left right ihLeft ihRight =>
      calc
        f (GeneratedZero.analyticGlue left right)
            = A.alg (ZeroSigF.analyticGlue (f left) (f right)) :=
              hom (ZeroSigF.analyticGlue left right)
        _ = A.alg (ZeroSigF.analyticGlue (GeneratedZero.fold A left)
              (GeneratedZero.fold A right)) := by
              rw [ihLeft, ihRight]
        _ = GeneratedZero.fold A (GeneratedZero.analyticGlue left right) := rfl
  | compatibleLimitSeal fuel z ih =>
      calc
        f (GeneratedZero.compatibleLimitSeal fuel z)
            = A.alg (ZeroSigF.compatibleLimitSeal fuel (f z)) :=
              hom (ZeroSigF.compatibleLimitSeal fuel z)
        _ = A.alg (ZeroSigF.compatibleLimitSeal fuel (GeneratedZero.fold A z)) := by
              rw [ih]
        _ = GeneratedZero.fold A (GeneratedZero.compatibleLimitSeal fuel z) := rfl
  | ledgerReplay z trace ih =>
      calc
        f (GeneratedZero.ledgerReplay z trace)
            = A.alg (ZeroSigF.ledgerReplay (f z) trace) :=
              hom (ZeroSigF.ledgerReplay z trace)
        _ = A.alg (ZeroSigF.ledgerReplay (GeneratedZero.fold A z) trace) := by
              rw [ih]
        _ = GeneratedZero.fold A (GeneratedZero.ledgerReplay z trace) := rfl
  | finiteWindowClose window z ih =>
      calc
        f (GeneratedZero.finiteWindowClose window z)
            = A.alg (ZeroSigF.finiteWindowClose window (f z)) :=
              hom (ZeroSigF.finiteWindowClose window z)
        _ = A.alg (ZeroSigF.finiteWindowClose window (GeneratedZero.fold A z)) := by
              rw [ih]
        _ = GeneratedZero.fold A (GeneratedZero.finiteWindowClose window z) := rfl
  | recursiveTowerReadback event z ih =>
      calc
        f (GeneratedZero.recursiveTowerReadback event z)
            = A.alg (ZeroSigF.recursiveTowerReadback event (f z)) :=
              hom (ZeroSigF.recursiveTowerReadback event z)
        _ = A.alg (ZeroSigF.recursiveTowerReadback event (GeneratedZero.fold A z)) := by
              rw [ih]
        _ = GeneratedZero.fold A (GeneratedZero.recursiveTowerReadback event z) := rfl
  | nonCollapseGuard budget z ih =>
      calc
        f (GeneratedZero.nonCollapseGuard budget z)
            = A.alg (ZeroSigF.nonCollapseGuard budget (f z)) :=
              hom (ZeroSigF.nonCollapseGuard budget z)
        _ = A.alg (ZeroSigF.nonCollapseGuard budget (GeneratedZero.fold A z)) := by
              rw [ih]
        _ = GeneratedZero.fold A (GeneratedZero.nonCollapseGuard budget z) := rfl

theorem generatedZero_initiality {signature : RHFreeZeroSignature} {α : Type u}
    (A : ZeroAlgebra signature α) :
    IsZeroAlgebraHom A (GeneratedZero.fold A) ∧
      ∀ f : GeneratedZero signature -> α,
        IsZeroAlgebraHom A f ->
          ∀ z : GeneratedZero signature, f z = GeneratedZero.fold A z := by
  exact And.intro (generatedZero_fold_hom A)
    (fun f hom z => generatedZero_fold_unique A f hom z)

abbrev SourceZeroPoint : Type :=
  RationalComplex

def SourceFixedHalf (point : SourceZeroPoint) : Prop :=
  JFixed point

def GeneratedFixedHalf {signature : RHFreeZeroSignature}
    (epsilon : GeneratedZero signature -> SourceZeroPoint)
    (z : GeneratedZero signature) : Prop :=
  SourceFixedHalf (epsilon z)

structure GeneratedZeroRealization (signature : RHFreeZeroSignature) where
  epsilon : GeneratedZero signature -> SourceZeroPoint

structure FixedHalfSubcarrier {signature : RHFreeZeroSignature}
    (epsilon : GeneratedZero signature -> SourceZeroPoint) where
  zero : GeneratedZero signature
  fixed : GeneratedFixedHalf epsilon zero

def fixedProjection {signature : RHFreeZeroSignature}
    {epsilon : GeneratedZero signature -> SourceZeroPoint}
    (x : FixedHalfSubcarrier epsilon) : GeneratedZero signature :=
  x.zero

structure FixedHalfClosedZeroSignature {signature : RHFreeZeroSignature}
    (epsilon : GeneratedZero signature -> SourceZeroPoint) where
  alg : ZeroSigF signature (FixedHalfSubcarrier epsilon) ->
    FixedHalfSubcarrier epsilon
  projection_commutes :
    ∀ op : ZeroSigF signature (FixedHalfSubcarrier epsilon),
      fixedProjection (alg op) =
        GeneratedZero.inZ (ZeroSigF.map fixedProjection op)

namespace FixedHalfClosedZeroSignature

def toAlgebra {signature : RHFreeZeroSignature}
    {epsilon : GeneratedZero signature -> SourceZeroPoint}
    (closed : FixedHalfClosedZeroSignature epsilon) :
    ZeroAlgebra signature (FixedHalfSubcarrier epsilon) where
  alg := closed.alg

end FixedHalfClosedZeroSignature

def generatedFixedHalfRecursor {signature : RHFreeZeroSignature}
    {epsilon : GeneratedZero signature -> SourceZeroPoint}
    (closed : FixedHalfClosedZeroSignature epsilon) :
    GeneratedZero signature -> FixedHalfSubcarrier epsilon :=
  GeneratedZero.fold closed.toAlgebra

theorem generatedFixedHalfRecursor_projection
    {signature : RHFreeZeroSignature}
    {epsilon : GeneratedZero signature -> SourceZeroPoint}
    (closed : FixedHalfClosedZeroSignature epsilon) :
    ∀ z : GeneratedZero signature,
      fixedProjection (generatedFixedHalfRecursor closed z) = z := by
  intro z
  induction z with
  | primeLocal window p member =>
      exact closed.projection_commutes (ZeroSigF.primeLocal window p member)
  | functionalMirror z ih =>
      change
        fixedProjection
            (closed.alg
              (ZeroSigF.functionalMirror (generatedFixedHalfRecursor closed z))) =
          GeneratedZero.functionalMirror z
      have projected :=
        closed.projection_commutes
          (ZeroSigF.functionalMirror (generatedFixedHalfRecursor closed z))
      change
        fixedProjection
            (closed.alg
              (ZeroSigF.functionalMirror (generatedFixedHalfRecursor closed z))) =
          GeneratedZero.functionalMirror
            (fixedProjection (generatedFixedHalfRecursor closed z)) at projected
      rw [projected, ih]
  | conjugationTransport z ih =>
      change
        fixedProjection
            (closed.alg
              (ZeroSigF.conjugationTransport (generatedFixedHalfRecursor closed z))) =
          GeneratedZero.conjugationTransport z
      have projected :=
        closed.projection_commutes
          (ZeroSigF.conjugationTransport (generatedFixedHalfRecursor closed z))
      change
        fixedProjection
            (closed.alg
              (ZeroSigF.conjugationTransport (generatedFixedHalfRecursor closed z))) =
          GeneratedZero.conjugationTransport
            (fixedProjection (generatedFixedHalfRecursor closed z)) at projected
      rw [projected, ih]
  | classifierTransport tag z ih =>
      change
        fixedProjection
            (closed.alg
              (ZeroSigF.classifierTransport tag (generatedFixedHalfRecursor closed z))) =
          GeneratedZero.classifierTransport tag z
      have projected :=
        closed.projection_commutes
          (ZeroSigF.classifierTransport tag (generatedFixedHalfRecursor closed z))
      change
        fixedProjection
            (closed.alg
              (ZeroSigF.classifierTransport tag (generatedFixedHalfRecursor closed z))) =
          GeneratedZero.classifierTransport tag
            (fixedProjection (generatedFixedHalfRecursor closed z)) at projected
      rw [projected, ih]
  | analyticGlue left right ihLeft ihRight =>
      change
        fixedProjection
            (closed.alg
              (ZeroSigF.analyticGlue (generatedFixedHalfRecursor closed left)
                (generatedFixedHalfRecursor closed right))) =
          GeneratedZero.analyticGlue left right
      have projected :=
        closed.projection_commutes
          (ZeroSigF.analyticGlue (generatedFixedHalfRecursor closed left)
            (generatedFixedHalfRecursor closed right))
      change
        fixedProjection
            (closed.alg
              (ZeroSigF.analyticGlue (generatedFixedHalfRecursor closed left)
                (generatedFixedHalfRecursor closed right))) =
          GeneratedZero.analyticGlue
            (fixedProjection (generatedFixedHalfRecursor closed left))
            (fixedProjection (generatedFixedHalfRecursor closed right)) at projected
      rw [projected, ihLeft, ihRight]
  | compatibleLimitSeal fuel z ih =>
      change
        fixedProjection
            (closed.alg
              (ZeroSigF.compatibleLimitSeal fuel (generatedFixedHalfRecursor closed z))) =
          GeneratedZero.compatibleLimitSeal fuel z
      have projected :=
        closed.projection_commutes
          (ZeroSigF.compatibleLimitSeal fuel (generatedFixedHalfRecursor closed z))
      change
        fixedProjection
            (closed.alg
              (ZeroSigF.compatibleLimitSeal fuel (generatedFixedHalfRecursor closed z))) =
          GeneratedZero.compatibleLimitSeal fuel
            (fixedProjection (generatedFixedHalfRecursor closed z)) at projected
      rw [projected, ih]
  | ledgerReplay z trace ih =>
      change
        fixedProjection
            (closed.alg
              (ZeroSigF.ledgerReplay (generatedFixedHalfRecursor closed z) trace)) =
          GeneratedZero.ledgerReplay z trace
      have projected :=
        closed.projection_commutes
          (ZeroSigF.ledgerReplay (generatedFixedHalfRecursor closed z) trace)
      change
        fixedProjection
            (closed.alg
              (ZeroSigF.ledgerReplay (generatedFixedHalfRecursor closed z) trace)) =
          GeneratedZero.ledgerReplay
            (fixedProjection (generatedFixedHalfRecursor closed z)) trace at projected
      rw [projected, ih]
  | finiteWindowClose window z ih =>
      change
        fixedProjection
            (closed.alg
              (ZeroSigF.finiteWindowClose window (generatedFixedHalfRecursor closed z))) =
          GeneratedZero.finiteWindowClose window z
      have projected :=
        closed.projection_commutes
          (ZeroSigF.finiteWindowClose window (generatedFixedHalfRecursor closed z))
      change
        fixedProjection
            (closed.alg
              (ZeroSigF.finiteWindowClose window (generatedFixedHalfRecursor closed z))) =
          GeneratedZero.finiteWindowClose window
            (fixedProjection (generatedFixedHalfRecursor closed z)) at projected
      rw [projected, ih]
  | recursiveTowerReadback event z ih =>
      change
        fixedProjection
            (closed.alg
              (ZeroSigF.recursiveTowerReadback event
                (generatedFixedHalfRecursor closed z))) =
          GeneratedZero.recursiveTowerReadback event z
      have projected :=
        closed.projection_commutes
          (ZeroSigF.recursiveTowerReadback event
            (generatedFixedHalfRecursor closed z))
      change
        fixedProjection
            (closed.alg
              (ZeroSigF.recursiveTowerReadback event
                (generatedFixedHalfRecursor closed z))) =
          GeneratedZero.recursiveTowerReadback event
            (fixedProjection (generatedFixedHalfRecursor closed z)) at projected
      rw [projected, ih]
  | nonCollapseGuard budget z ih =>
      change
        fixedProjection
            (closed.alg
              (ZeroSigF.nonCollapseGuard budget (generatedFixedHalfRecursor closed z))) =
          GeneratedZero.nonCollapseGuard budget z
      have projected :=
        closed.projection_commutes
          (ZeroSigF.nonCollapseGuard budget (generatedFixedHalfRecursor closed z))
      change
        fixedProjection
            (closed.alg
              (ZeroSigF.nonCollapseGuard budget (generatedFixedHalfRecursor closed z))) =
          GeneratedZero.nonCollapseGuard budget
            (fixedProjection (generatedFixedHalfRecursor closed z)) at projected
      rw [projected, ih]

def generatedFixedHalfWitness {signature : RHFreeZeroSignature}
    {epsilon : GeneratedZero signature -> SourceZeroPoint}
    (closed : FixedHalfClosedZeroSignature epsilon)
    (z : GeneratedZero signature) : GeneratedFixedHalf epsilon z := by
  have base :
      GeneratedFixedHalf epsilon
        (fixedProjection (generatedFixedHalfRecursor closed z)) :=
    (generatedFixedHalfRecursor closed z).fixed
  have projected :
      fixedProjection (generatedFixedHalfRecursor closed z) = z :=
    generatedFixedHalfRecursor_projection closed z
  rw [projected] at base
  exact base

theorem generatedFixedHalf_J_fixed {signature : RHFreeZeroSignature}
    {epsilon : GeneratedZero signature -> SourceZeroPoint}
    (closed : FixedHalfClosedZeroSignature epsilon)
    (z : GeneratedZero signature) :
    JFixed (epsilon z) :=
  generatedFixedHalfWitness closed z

theorem generatedFixedHalf_criticalLine {signature : RHFreeZeroSignature}
    {epsilon : GeneratedZero signature -> SourceZeroPoint}
    (closed : FixedHalfClosedZeroSignature epsilon)
    (z : GeneratedZero signature) :
    CriticalLine (epsilon z) :=
  (criticalLine_J_fixed_iff (epsilon z)).mp
    (generatedFixedHalfWitness closed z)

theorem ReEqHalf_transport {z w : SourceZeroPoint} :
    ComplexEq z w -> ReEqHalf z -> ReEqHalf w := by
  intro same half
  have above : RatEq w.reAboveHalf z.reAboveHalf :=
    RatEq_symm same.left
  have toBelow : RatEq w.reAboveHalf z.reBelowHalf :=
    RatEq_trans w.reAboveHalf z.reAboveHalf z.reBelowHalf above half
  exact RatEq_trans w.reAboveHalf z.reBelowHalf w.reBelowHalf toBelow
    same.right.left

theorem JFixed_transport {z w : SourceZeroPoint} :
    ComplexEq z w -> JFixed z -> JFixed w := by
  intro same fixed
  exact (J_fixed_iff_re_half w).mpr
    (ReEqHalf_transport same ((J_fixed_iff_re_half z).mp fixed))

inductive ZeroLedgerRow where
  | primeLocalFiber
  | dirichletRow
  | eulerRow
  | laplaceRow
  | analyticContinuation
  | archimedeanCompletion
  | functionalEquation
  | zeroLedger
  | provenance

structure CriticalStripZeroPacket where
  point : SourceZeroPoint
  window : PrimeWindow
  ledger : List ZeroLedgerRow

structure ZeroCover {signature : RHFreeZeroSignature}
    (epsilon : GeneratedZero signature -> SourceZeroPoint)
    (packet : CriticalStripZeroPacket) where
  zero : GeneratedZero signature
  same_source : ComplexEq (epsilon zero) packet.point

structure ZeroPresentationCompleteness {signature : RHFreeZeroSignature}
    (epsilon : GeneratedZero signature -> SourceZeroPoint) where
  covers : (packet : CriticalStripZeroPacket) -> ZeroCover epsilon packet

structure RHSection where
  fixed : (packet : CriticalStripZeroPacket) -> SourceFixedHalf packet.point
  critical_line : (packet : CriticalStripZeroPacket) -> CriticalLine packet.point

theorem rh_conditional_initiality_route_section
    (signature : RHFreeZeroSignature)
    (epsilon : GeneratedZero signature -> SourceZeroPoint)
    (complete : ZeroPresentationCompleteness epsilon)
    (closed : FixedHalfClosedZeroSignature epsilon) :
    RHSection := by
  exact {
    fixed := fun packet =>
      let cover := complete.covers packet
      JFixed_transport cover.same_source
        (generatedFixedHalfWitness closed cover.zero)
    critical_line := fun packet =>
      (criticalLine_J_fixed_iff packet.point).mp
        (let cover := complete.covers packet
         JFixed_transport cover.same_source
          (generatedFixedHalfWitness closed cover.zero))
  }

inductive ZetaRecoveryRow where
  | primeLocalFibers
  | dirichletRow
  | eulerRow
  | laplaceRow
  | analyticContinuation
  | archimedeanCompletion
  | functionalEquation
  | zeroLedger

def zetaRecoveryRowCode : ZetaRecoveryRow -> Nat
  | ZetaRecoveryRow.primeLocalFibers => 0
  | ZetaRecoveryRow.dirichletRow => 1
  | ZetaRecoveryRow.eulerRow => 2
  | ZetaRecoveryRow.laplaceRow => 3
  | ZetaRecoveryRow.analyticContinuation => 4
  | ZetaRecoveryRow.archimedeanCompletion => 5
  | ZetaRecoveryRow.functionalEquation => 6
  | ZetaRecoveryRow.zeroLedger => 7

def countZetaRecoveryRow (row : ZetaRecoveryRow)
    (rows : List ZetaRecoveryRow) : Nat :=
  countNatCode (zetaRecoveryRowCode row)
    (rows.map zetaRecoveryRowCode)

structure MultiplicativeSelfSimilarZetaPacket where
  rows : List ZetaRecoveryRow
  row_count : ZetaRecoveryRow -> Nat
  tower_trace : List TraceEvent

def canonicalZetaRecoveryRows : List ZetaRecoveryRow :=
  [ ZetaRecoveryRow.primeLocalFibers,
    ZetaRecoveryRow.dirichletRow,
    ZetaRecoveryRow.eulerRow,
    ZetaRecoveryRow.laplaceRow,
    ZetaRecoveryRow.analyticContinuation,
    ZetaRecoveryRow.archimedeanCompletion,
    ZetaRecoveryRow.functionalEquation,
    ZetaRecoveryRow.zeroLedger ]

def multiplicativeSelfSimilarZetaPacket :
    MultiplicativeSelfSimilarZetaPacket where
  rows := canonicalZetaRecoveryRows
  row_count := fun row => countZetaRecoveryRow row canonicalZetaRecoveryRows
  tower_trace := [TraceEvent.seed 0]

theorem multiplicativeSelfSimilarZetaPacket_row_count_sound
    (row : ZetaRecoveryRow) :
    multiplicativeSelfSimilarZetaPacket.row_count row =
      countZetaRecoveryRow row multiplicativeSelfSimilarZetaPacket.rows := by
  rfl

theorem multiplicativeSelfSimilarZetaPacket_zeroLedger_count :
    multiplicativeSelfSimilarZetaPacket.row_count ZetaRecoveryRow.zeroLedger = 1 := by
  rfl

abbrev NonCollapseGuardWitness :=
  BEDC.Derived.NonCollapseInvariantUp.BoxStreamNonCollapseWitness

end BEDC.Derived.RHRoute.ZeroGenerationInitiality
