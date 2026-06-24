import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SubstitutionContextAuditUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SubstitutionContextAuditUp : Type where
  | mk
      (context shift substitute closedComposition generatorClosure binderSeal handoff transport
        route provenance name : BHist) :
      SubstitutionContextAuditUp
  deriving DecidableEq

def substitutionContextAuditEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: substitutionContextAuditEncodeBHist h
  | BHist.e1 h => BMark.b1 :: substitutionContextAuditEncodeBHist h

def substitutionContextAuditDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (substitutionContextAuditDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (substitutionContextAuditDecodeBHist tail)

private theorem substitutionContextAudit_decode_encode :
    forall h : BHist,
      substitutionContextAuditDecodeBHist (substitutionContextAuditEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def substitutionContextAuditFields : SubstitutionContextAuditUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SubstitutionContextAuditUp.mk context shift substitute closedComposition generatorClosure
      binderSeal handoff transport route provenance name =>
      [context, shift, substitute, closedComposition, generatorClosure, binderSeal, handoff,
        transport, route, provenance, name]

def substitutionContextAuditToEventFlow : SubstitutionContextAuditUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (substitutionContextAuditFields x).map substitutionContextAuditEncodeBHist

def substitutionContextAuditEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => substitutionContextAuditEventAt index rest

def substitutionContextAuditFromEventFlow :
    EventFlow -> Option SubstitutionContextAuditUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      some
        (SubstitutionContextAuditUp.mk
          (substitutionContextAuditDecodeBHist (substitutionContextAuditEventAt 0 flow))
          (substitutionContextAuditDecodeBHist (substitutionContextAuditEventAt 1 flow))
          (substitutionContextAuditDecodeBHist (substitutionContextAuditEventAt 2 flow))
          (substitutionContextAuditDecodeBHist (substitutionContextAuditEventAt 3 flow))
          (substitutionContextAuditDecodeBHist (substitutionContextAuditEventAt 4 flow))
          (substitutionContextAuditDecodeBHist (substitutionContextAuditEventAt 5 flow))
          (substitutionContextAuditDecodeBHist (substitutionContextAuditEventAt 6 flow))
          (substitutionContextAuditDecodeBHist (substitutionContextAuditEventAt 7 flow))
          (substitutionContextAuditDecodeBHist (substitutionContextAuditEventAt 8 flow))
          (substitutionContextAuditDecodeBHist (substitutionContextAuditEventAt 9 flow))
          (substitutionContextAuditDecodeBHist (substitutionContextAuditEventAt 10 flow)))

private theorem substitutionContextAudit_round_trip :
    forall x : SubstitutionContextAuditUp,
      substitutionContextAuditFromEventFlow
        (substitutionContextAuditToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk context shift substitute closedComposition generatorClosure binderSeal handoff transport
      route provenance name =>
      change
        some
          (SubstitutionContextAuditUp.mk
            (substitutionContextAuditDecodeBHist (substitutionContextAuditEncodeBHist context))
            (substitutionContextAuditDecodeBHist (substitutionContextAuditEncodeBHist shift))
            (substitutionContextAuditDecodeBHist
              (substitutionContextAuditEncodeBHist substitute))
            (substitutionContextAuditDecodeBHist
              (substitutionContextAuditEncodeBHist closedComposition))
            (substitutionContextAuditDecodeBHist
              (substitutionContextAuditEncodeBHist generatorClosure))
            (substitutionContextAuditDecodeBHist
              (substitutionContextAuditEncodeBHist binderSeal))
            (substitutionContextAuditDecodeBHist (substitutionContextAuditEncodeBHist handoff))
            (substitutionContextAuditDecodeBHist
              (substitutionContextAuditEncodeBHist transport))
            (substitutionContextAuditDecodeBHist (substitutionContextAuditEncodeBHist route))
            (substitutionContextAuditDecodeBHist
              (substitutionContextAuditEncodeBHist provenance))
            (substitutionContextAuditDecodeBHist (substitutionContextAuditEncodeBHist name))) =
          some
            (SubstitutionContextAuditUp.mk context shift substitute closedComposition
              generatorClosure binderSeal handoff transport route provenance name)
      rw [substitutionContextAudit_decode_encode context,
        substitutionContextAudit_decode_encode shift,
        substitutionContextAudit_decode_encode substitute,
        substitutionContextAudit_decode_encode closedComposition,
        substitutionContextAudit_decode_encode generatorClosure,
        substitutionContextAudit_decode_encode binderSeal,
        substitutionContextAudit_decode_encode handoff,
        substitutionContextAudit_decode_encode transport,
        substitutionContextAudit_decode_encode route,
        substitutionContextAudit_decode_encode provenance,
        substitutionContextAudit_decode_encode name]

private theorem substitutionContextAuditToEventFlow_injective
    {x y : SubstitutionContextAuditUp} :
    substitutionContextAuditToEventFlow x =
      substitutionContextAuditToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      substitutionContextAuditFromEventFlow (substitutionContextAuditToEventFlow x) =
        substitutionContextAuditFromEventFlow (substitutionContextAuditToEventFlow y) :=
    congrArg substitutionContextAuditFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (substitutionContextAudit_round_trip x).symm
      (Eq.trans hread (substitutionContextAudit_round_trip y)))

instance substitutionContextAuditBHistCarrier :
    BHistCarrier SubstitutionContextAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := substitutionContextAuditToEventFlow
  fromEventFlow := substitutionContextAuditFromEventFlow

instance substitutionContextAuditChapterTasteGate :
    ChapterTasteGate SubstitutionContextAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change substitutionContextAuditFromEventFlow
      (substitutionContextAuditToEventFlow x) = some x
    exact substitutionContextAudit_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (substitutionContextAuditToEventFlow_injective heq)

theorem SubstitutionContextAuditTasteGate_single_carrier_alignment :
    (forall h : BHist,
      substitutionContextAuditDecodeBHist (substitutionContextAuditEncodeBHist h) = h) /\
      (forall x : SubstitutionContextAuditUp,
        substitutionContextAuditFromEventFlow
          (substitutionContextAuditToEventFlow x) = some x) /\
      (forall x y : SubstitutionContextAuditUp,
        substitutionContextAuditToEventFlow x =
          substitutionContextAuditToEventFlow y -> x = y) /\
      substitutionContextAuditEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨substitutionContextAudit_decode_encode,
      substitutionContextAudit_round_trip,
      (fun _ _ heq => substitutionContextAuditToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.SubstitutionContextAuditUp
