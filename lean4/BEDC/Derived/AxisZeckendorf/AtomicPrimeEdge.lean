import BEDC.Derived.AxisZeckendorf.Zeckendorf
import BEDC.Derived.ZeckendorfUp
import BEDC.Derived.PrimeUp.PrimeShape

namespace BEDC.Derived.AxisZeckendorf.AtomicPrimeEdge

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.PrimeUp

inductive RecursiveOp where
  | id
  | step
  | composite (left right : RecursiveOp)

def opId : RecursiveOp := RecursiveOp.id

def stepOp : RecursiveOp := RecursiveOp.step

def composeOp (left right : RecursiveOp) : RecursiveOp :=
  RecursiveOp.composite left right

def opWidth : RecursiveOp -> Nat
  | RecursiveOp.id => 0
  | RecursiveOp.step => 1
  | RecursiveOp.composite left right => opWidth left + opWidth right

structure RecursiveEdge where
  source : Nat
  target : Nat

def edgeAt (index : Nat) : RecursiveEdge :=
  { source := index, target := index + 1 }

def EdgeRealizes (op : RecursiveOp) (edge : RecursiveEdge) : Prop :=
  edge.target = edge.source + opWidth op

def AtomicOp (op : RecursiveOp) : Prop :=
  ∀ left right : RecursiveOp,
    op = composeOp left right -> left = opId ∨ right = opId

def EdgeSourceZeckendorf (edge : RecursiveEdge) : List Nat :=
  BEDC.Derived.ZeckendorfUp.zeckendorf edge.source

def EdgeTargetZeckendorf (edge : RecursiveEdge) : List Nat :=
  BEDC.Derived.ZeckendorfUp.zeckendorf edge.target

def EdgeSourceFibonacci (edge : RecursiveEdge) : Nat :=
  BEDC.Derived.ZeckendorfUp.fibonacciTerm edge.source

def EdgeTargetFibonacci (edge : RecursiveEdge) : Nat :=
  BEDC.Derived.ZeckendorfUp.fibonacciTerm edge.target

-- 素数行使用 PrimeUp 的 unary carrier；Nat 侧只负责有限索引读出。
def unaryOfNat : Nat -> BHist
  | 0 => BHist.Empty
  | n + 1 => BHist.e1 (unaryOfNat n)

theorem unaryOfNat_unary (n : Nat) :
    UnaryHistory (unaryOfNat n) := by
  induction n with
  | zero =>
      exact unary_empty
  | succ n ih =>
      exact unary_e1_closed ih

theorem edgeAt_realizes_step (index : Nat) :
    EdgeRealizes stepOp (edgeAt index) := by
  rfl

theorem stepOp_atomic : AtomicOp stepOp := by
  intro left right h
  cases h

structure PrimeEdge where
  edge : RecursiveEdge
  op : RecursiveOp
  realizes : EdgeRealizes op edge
  atomic : AtomicOp op
  primeMark : BHist
  prime : NatPrime primeMark

def primeEdgeAt (index : Nat) (mark : BHist) (markPrime : NatPrime mark) :
    PrimeEdge :=
  { edge := edgeAt index
    op := stepOp
    realizes := edgeAt_realizes_step index
    atomic := stepOp_atomic
    primeMark := mark
    prime := markPrime }

def primeTwoMark : BHist :=
  BHist.e1 (BHist.e1 BHist.Empty)

theorem primeTwoMark_prime :
    NatPrime primeTwoMark :=
  NatPrime_first_pair.left

def atomicPrimeEdgeZero : PrimeEdge :=
  primeEdgeAt 0 primeTwoMark primeTwoMark_prime

theorem primeEdge_no_nontrivial_intermediate
    (edge : PrimeEdge) (left right : RecursiveOp) :
    edge.op = composeOp left right -> left = opId ∨ right = opId := by
  intro factorization
  exact edge.atomic left right factorization

theorem edge_source_zeckendorf_readback (edge : RecursiveEdge) :
    BEDC.Derived.ZeckendorfUp.zeckendorfValue
        (EdgeSourceZeckendorf edge) = edge.source := by
  exact BEDC.Derived.ZeckendorfUp.zeckendorf_sum_restore edge.source

theorem edge_target_zeckendorf_readback (edge : RecursiveEdge) :
    BEDC.Derived.ZeckendorfUp.zeckendorfValue
        (EdgeTargetZeckendorf edge) = edge.target := by
  exact BEDC.Derived.ZeckendorfUp.zeckendorf_sum_restore edge.target

theorem primeEdge_zeckendorf_fibonacci_prime_readback (edge : PrimeEdge) :
    NatPrime edge.primeMark ∧
      BEDC.Derived.ZeckendorfUp.zeckendorfValue
          (EdgeSourceZeckendorf edge.edge) = edge.edge.source ∧
      BEDC.Derived.ZeckendorfUp.zeckendorfValue
          (EdgeTargetZeckendorf edge.edge) = edge.edge.target ∧
      EdgeSourceFibonacci edge.edge =
          BEDC.Derived.ZeckendorfUp.fibonacciTerm edge.edge.source ∧
      EdgeTargetFibonacci edge.edge =
          BEDC.Derived.ZeckendorfUp.fibonacciTerm edge.edge.target := by
  exact And.intro edge.prime
    (And.intro (edge_source_zeckendorf_readback edge.edge)
      (And.intro (edge_target_zeckendorf_readback edge.edge)
        (And.intro rfl rfl)))

def enumerateRecursiveEdges : Nat -> List RecursiveEdge
  | 0 => []
  | fuel + 1 => edgeAt fuel :: enumerateRecursiveEdges fuel

theorem enumerateRecursiveEdges_length (fuel : Nat) :
    (enumerateRecursiveEdges fuel).length = fuel := by
  induction fuel with
  | zero =>
      rfl
  | succ fuel ih =>
      rw [enumerateRecursiveEdges, List.length_cons, ih]

def enumeratePrimeEdges
    (fuel : Nat) (mark : BHist) (markPrime : NatPrime mark) :
    List PrimeEdge :=
  match fuel with
  | 0 => []
  | fuel + 1 => primeEdgeAt fuel mark markPrime ::
      enumeratePrimeEdges fuel mark markPrime

theorem enumeratePrimeEdges_length
    (fuel : Nat) (mark : BHist) (markPrime : NatPrime mark) :
    (enumeratePrimeEdges fuel mark markPrime).length = fuel := by
  induction fuel with
  | zero =>
      rfl
  | succ fuel ih =>
      rw [enumeratePrimeEdges, List.length_cons, ih]

def natEqBool : Nat -> Nat -> Bool
  | 0, 0 => true
  | 0, Nat.succ _ => false
  | Nat.succ _, 0 => false
  | Nat.succ left, Nat.succ right => natEqBool left right

theorem natEqBool_refl (n : Nat) :
    natEqBool n n = true := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      exact ih

theorem natEqBool_sound {left right : Nat} :
    natEqBool left right = true -> left = right := by
  induction left generalizing right with
  | zero =>
      cases right with
      | zero =>
          intro _h
          rfl
      | succ right =>
          intro h
          cases h
  | succ left ih =>
      cases right with
      | zero =>
          intro h
          cases h
      | succ right =>
          intro h
          exact congrArg Nat.succ (ih h)

theorem natEqBool_complete {left right : Nat} :
    left = right -> natEqBool left right = true := by
  intro same
  cases same
  exact natEqBool_refl left

def edgeEqBool (left right : RecursiveEdge) : Bool :=
  match natEqBool left.source right.source with
  | true =>
    match natEqBool left.target right.target with
    | true =>
      true
    | false =>
      false
  | false =>
    false

theorem edgeEqBool_refl (edge : RecursiveEdge) :
    edgeEqBool edge edge = true := by
  cases edge with
  | mk source target =>
      unfold edgeEqBool
      rw [natEqBool_refl source, natEqBool_refl target]

theorem edgeEqBool_sound {left right : RecursiveEdge} :
    edgeEqBool left right = true -> left = right := by
  cases left with
  | mk leftSource leftTarget =>
      cases right with
      | mk rightSource rightTarget =>
          unfold edgeEqBool
          cases sourceCheck : natEqBool leftSource rightSource with
          | false =>
              intro h
              cases h
          | true =>
              cases targetCheck : natEqBool leftTarget rightTarget with
              | false =>
                  intro h
                  cases h
              | true =>
                  intro _h
                  have sameSource : leftSource = rightSource :=
                    natEqBool_sound sourceCheck
                  have sameTarget : leftTarget = rightTarget :=
                    natEqBool_sound targetCheck
                  cases sameSource
                  cases sameTarget
                  rfl

theorem edgeEqBool_complete {left right : RecursiveEdge} :
    left = right -> edgeEqBool left right = true := by
  intro same
  cases same
  exact edgeEqBool_refl left

def PrimeEdgeMemberProp (candidate : RecursiveEdge) :
    List PrimeEdge -> Prop
  | [] => False
  | edge :: rest => candidate = edge.edge ∨ PrimeEdgeMemberProp candidate rest

def primeEdgeMemberBool (candidate : RecursiveEdge) :
    List PrimeEdge -> Bool
  | [] => false
  | edge :: rest =>
      match edgeEqBool candidate edge.edge with
      | true => true
      | false => primeEdgeMemberBool candidate rest

theorem primeEdgeMemberBool_sound {candidate : RecursiveEdge}
    {edges : List PrimeEdge} :
    primeEdgeMemberBool candidate edges = true ->
      PrimeEdgeMemberProp candidate edges := by
  induction edges with
  | nil =>
      intro h
      cases h
  | cons edge rest ih =>
      change
        (match edgeEqBool candidate edge.edge with
        | true => true
        | false => primeEdgeMemberBool candidate rest) = true ->
          candidate = edge.edge ∨ PrimeEdgeMemberProp candidate rest
      cases eqCheck : edgeEqBool candidate edge.edge with
      | false =>
          intro h
          exact Or.inr (ih h)
      | true =>
          intro _h
          exact Or.inl (edgeEqBool_sound eqCheck)

theorem primeEdgeMemberBool_complete {candidate : RecursiveEdge}
    {edges : List PrimeEdge} :
    PrimeEdgeMemberProp candidate edges ->
      primeEdgeMemberBool candidate edges = true := by
  induction edges with
  | nil =>
      intro h
      cases h
  | cons edge rest ih =>
      change
        candidate = edge.edge ∨ PrimeEdgeMemberProp candidate rest ->
          (match edgeEqBool candidate edge.edge with
          | true => true
          | false => primeEdgeMemberBool candidate rest) = true
      intro member
      cases member with
      | inl headSame =>
          cases headSame
          have headAccepted : edgeEqBool edge.edge edge.edge = true :=
            edgeEqBool_refl edge.edge
          rw [headAccepted]
      | inr tailMember =>
          cases eqCheck : edgeEqBool candidate edge.edge with
          | false =>
              exact ih tailMember
          | true =>
              rfl

theorem primeEdgeMemberBool_exact {candidate : RecursiveEdge}
    {edges : List PrimeEdge} :
    primeEdgeMemberBool candidate edges = true ↔
      PrimeEdgeMemberProp candidate edges := by
  constructor
  · exact primeEdgeMemberBool_sound
  · exact primeEdgeMemberBool_complete

theorem primeEdgeMemberProp_has_prime {candidate : RecursiveEdge}
    {edges : List PrimeEdge} :
    PrimeEdgeMemberProp candidate edges ->
      ∃ mark : BHist, NatPrime mark := by
  induction edges with
  | nil =>
      intro h
      cases h
  | cons edge rest ih =>
      unfold PrimeEdgeMemberProp
      intro member
      cases member with
      | inl _headSame =>
          exact Exists.intro edge.primeMark edge.prime
      | inr tailMember =>
          exact ih tailMember

theorem primeEdgeMemberBool_has_prime {candidate : RecursiveEdge}
    {edges : List PrimeEdge} :
    primeEdgeMemberBool candidate edges = true ->
      ∃ mark : BHist, NatPrime mark := by
  intro accepted
  exact primeEdgeMemberProp_has_prime
    (primeEdgeMemberBool_sound accepted)

def primeEdgeInFiniteEnumeration
    (candidate : RecursiveEdge) (fuel : Nat)
    (mark : BHist) (markPrime : NatPrime mark) : Bool :=
  primeEdgeMemberBool candidate (enumeratePrimeEdges fuel mark markPrime)

theorem primeEdgeInFiniteEnumeration_accepts_top
    (fuel : Nat) (mark : BHist) (markPrime : NatPrime mark) :
    primeEdgeInFiniteEnumeration (edgeAt fuel) (fuel + 1) mark markPrime = true := by
  unfold primeEdgeInFiniteEnumeration enumeratePrimeEdges primeEdgeMemberBool
  have hHead :
      edgeEqBool (edgeAt fuel) (primeEdgeAt fuel mark markPrime).edge = true := by
    change edgeEqBool (edgeAt fuel) (edgeAt fuel) = true
    exact edgeEqBool_refl (edgeAt fuel)
  rw [hHead]

theorem atomicPrimeEdgeZero_readback :
    NatPrime atomicPrimeEdgeZero.primeMark ∧
      EdgeRealizes stepOp atomicPrimeEdgeZero.edge ∧
      BEDC.Derived.ZeckendorfUp.zeckendorfValue
          (EdgeSourceZeckendorf atomicPrimeEdgeZero.edge) =
        atomicPrimeEdgeZero.edge.source ∧
      BEDC.Derived.ZeckendorfUp.zeckendorfValue
          (EdgeTargetZeckendorf atomicPrimeEdgeZero.edge) =
        atomicPrimeEdgeZero.edge.target := by
  exact And.intro atomicPrimeEdgeZero.prime
    (And.intro atomicPrimeEdgeZero.realizes
      (And.intro (edge_source_zeckendorf_readback atomicPrimeEdgeZero.edge)
        (edge_target_zeckendorf_readback atomicPrimeEdgeZero.edge)))

end BEDC.Derived.AxisZeckendorf.AtomicPrimeEdge
