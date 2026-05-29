import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ContextFreePumpingLemmaUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ContextFreePumpingLemmaUp : Type where
  | mk (G W D A E I Y H C R Q N : BHist) : ContextFreePumpingLemmaUp
  deriving DecidableEq

def contextFreePumpingLemmaEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: contextFreePumpingLemmaEncodeBHist h
  | BHist.e1 h => BMark.b1 :: contextFreePumpingLemmaEncodeBHist h

def contextFreePumpingLemmaDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (contextFreePumpingLemmaDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (contextFreePumpingLemmaDecodeBHist tail)

private theorem ContextFreePumpingLemmaTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      contextFreePumpingLemmaDecodeBHist
          (contextFreePumpingLemmaEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def contextFreePumpingLemmaFields : ContextFreePumpingLemmaUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ContextFreePumpingLemmaUp.mk G W D A E I Y H C R Q N =>
      [G, W, D, A, E, I, Y, H, C, R, Q, N]

def contextFreePumpingLemmaToEventFlow : ContextFreePumpingLemmaUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (contextFreePumpingLemmaFields x).map contextFreePumpingLemmaEncodeBHist

private def contextFreePumpingLemmaEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => contextFreePumpingLemmaEventAt index rest

def contextFreePumpingLemmaFromEventFlow
    (ef : EventFlow) : Option ContextFreePumpingLemmaUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ContextFreePumpingLemmaUp.mk
      (contextFreePumpingLemmaDecodeBHist (contextFreePumpingLemmaEventAt 0 ef))
      (contextFreePumpingLemmaDecodeBHist (contextFreePumpingLemmaEventAt 1 ef))
      (contextFreePumpingLemmaDecodeBHist (contextFreePumpingLemmaEventAt 2 ef))
      (contextFreePumpingLemmaDecodeBHist (contextFreePumpingLemmaEventAt 3 ef))
      (contextFreePumpingLemmaDecodeBHist (contextFreePumpingLemmaEventAt 4 ef))
      (contextFreePumpingLemmaDecodeBHist (contextFreePumpingLemmaEventAt 5 ef))
      (contextFreePumpingLemmaDecodeBHist (contextFreePumpingLemmaEventAt 6 ef))
      (contextFreePumpingLemmaDecodeBHist (contextFreePumpingLemmaEventAt 7 ef))
      (contextFreePumpingLemmaDecodeBHist (contextFreePumpingLemmaEventAt 8 ef))
      (contextFreePumpingLemmaDecodeBHist (contextFreePumpingLemmaEventAt 9 ef))
      (contextFreePumpingLemmaDecodeBHist (contextFreePumpingLemmaEventAt 10 ef))
      (contextFreePumpingLemmaDecodeBHist (contextFreePumpingLemmaEventAt 11 ef)))

private theorem ContextFreePumpingLemmaTasteGate_single_carrier_alignment_round_trip
    (x : ContextFreePumpingLemmaUp) :
    contextFreePumpingLemmaFromEventFlow (contextFreePumpingLemmaToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk G W D A E I Y H C R Q N =>
      change
        some
          (ContextFreePumpingLemmaUp.mk
            (contextFreePumpingLemmaDecodeBHist (contextFreePumpingLemmaEncodeBHist G))
            (contextFreePumpingLemmaDecodeBHist (contextFreePumpingLemmaEncodeBHist W))
            (contextFreePumpingLemmaDecodeBHist (contextFreePumpingLemmaEncodeBHist D))
            (contextFreePumpingLemmaDecodeBHist (contextFreePumpingLemmaEncodeBHist A))
            (contextFreePumpingLemmaDecodeBHist (contextFreePumpingLemmaEncodeBHist E))
            (contextFreePumpingLemmaDecodeBHist (contextFreePumpingLemmaEncodeBHist I))
            (contextFreePumpingLemmaDecodeBHist (contextFreePumpingLemmaEncodeBHist Y))
            (contextFreePumpingLemmaDecodeBHist (contextFreePumpingLemmaEncodeBHist H))
            (contextFreePumpingLemmaDecodeBHist (contextFreePumpingLemmaEncodeBHist C))
            (contextFreePumpingLemmaDecodeBHist (contextFreePumpingLemmaEncodeBHist R))
            (contextFreePumpingLemmaDecodeBHist (contextFreePumpingLemmaEncodeBHist Q))
            (contextFreePumpingLemmaDecodeBHist (contextFreePumpingLemmaEncodeBHist N))) =
          some (ContextFreePumpingLemmaUp.mk G W D A E I Y H C R Q N)
      rw [ContextFreePumpingLemmaTasteGate_single_carrier_alignment_decode_encode G,
        ContextFreePumpingLemmaTasteGate_single_carrier_alignment_decode_encode W,
        ContextFreePumpingLemmaTasteGate_single_carrier_alignment_decode_encode D,
        ContextFreePumpingLemmaTasteGate_single_carrier_alignment_decode_encode A,
        ContextFreePumpingLemmaTasteGate_single_carrier_alignment_decode_encode E,
        ContextFreePumpingLemmaTasteGate_single_carrier_alignment_decode_encode I,
        ContextFreePumpingLemmaTasteGate_single_carrier_alignment_decode_encode Y,
        ContextFreePumpingLemmaTasteGate_single_carrier_alignment_decode_encode H,
        ContextFreePumpingLemmaTasteGate_single_carrier_alignment_decode_encode C,
        ContextFreePumpingLemmaTasteGate_single_carrier_alignment_decode_encode R,
        ContextFreePumpingLemmaTasteGate_single_carrier_alignment_decode_encode Q,
        ContextFreePumpingLemmaTasteGate_single_carrier_alignment_decode_encode N]

private theorem ContextFreePumpingLemmaTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ContextFreePumpingLemmaUp} :
    contextFreePumpingLemmaToEventFlow x = contextFreePumpingLemmaToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      contextFreePumpingLemmaFromEventFlow (contextFreePumpingLemmaToEventFlow x) =
        contextFreePumpingLemmaFromEventFlow (contextFreePumpingLemmaToEventFlow y) :=
    congrArg contextFreePumpingLemmaFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ContextFreePumpingLemmaTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ContextFreePumpingLemmaTasteGate_single_carrier_alignment_round_trip y)))

instance contextFreePumpingLemmaBHistCarrier : BHistCarrier ContextFreePumpingLemmaUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := contextFreePumpingLemmaToEventFlow
  fromEventFlow := contextFreePumpingLemmaFromEventFlow

instance contextFreePumpingLemmaChapterTasteGate :
    ChapterTasteGate ContextFreePumpingLemmaUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change contextFreePumpingLemmaFromEventFlow (contextFreePumpingLemmaToEventFlow x) = some x
    exact ContextFreePumpingLemmaTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (ContextFreePumpingLemmaTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem ContextFreePumpingLemmaTasteGate_single_carrier_alignment :
    (∀ h : BHist, contextFreePumpingLemmaDecodeBHist
      (contextFreePumpingLemmaEncodeBHist h) = h) ∧
      (∀ x : ContextFreePumpingLemmaUp,
        contextFreePumpingLemmaFromEventFlow
          (contextFreePumpingLemmaToEventFlow x) = some x) ∧
        (∀ x y : ContextFreePumpingLemmaUp,
          contextFreePumpingLemmaToEventFlow x =
            contextFreePumpingLemmaToEventFlow y → x = y) ∧
          contextFreePumpingLemmaEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨ContextFreePumpingLemmaTasteGate_single_carrier_alignment_decode_encode,
      ContextFreePumpingLemmaTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        ContextFreePumpingLemmaTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.ContextFreePumpingLemmaUp
