import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.GroundCompilerEventFlowAuditRouteUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive GroundCompilerEventFlowAuditRouteUp : Type where
  | mk (E C L G A B H K P N : BHist) : GroundCompilerEventFlowAuditRouteUp
  deriving DecidableEq

def groundCompilerEventFlowAuditRouteEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: groundCompilerEventFlowAuditRouteEncodeBHist h
  | BHist.e1 h => BMark.b1 :: groundCompilerEventFlowAuditRouteEncodeBHist h

def groundCompilerEventFlowAuditRouteDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (groundCompilerEventFlowAuditRouteDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (groundCompilerEventFlowAuditRouteDecodeBHist tail)

private theorem GroundCompilerEventFlowAuditRouteTasteGate_decode_encode :
    ∀ h : BHist,
      groundCompilerEventFlowAuditRouteDecodeBHist
        (groundCompilerEventFlowAuditRouteEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def groundCompilerEventFlowAuditRouteFields :
    GroundCompilerEventFlowAuditRouteUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | GroundCompilerEventFlowAuditRouteUp.mk E C L G A B H K P N =>
      [E, C, L, G, A, B, H, K, P, N]

def groundCompilerEventFlowAuditRouteToEventFlow :
    GroundCompilerEventFlowAuditRouteUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (groundCompilerEventFlowAuditRouteFields x).map
        groundCompilerEventFlowAuditRouteEncodeBHist

private def groundCompilerEventFlowAuditRouteEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => groundCompilerEventFlowAuditRouteEventAtDefault index rest

def groundCompilerEventFlowAuditRouteFromEventFlow :
    EventFlow → Option GroundCompilerEventFlowAuditRouteUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      some
        (GroundCompilerEventFlowAuditRouteUp.mk
          (groundCompilerEventFlowAuditRouteDecodeBHist
            (groundCompilerEventFlowAuditRouteEventAtDefault 0 flow))
          (groundCompilerEventFlowAuditRouteDecodeBHist
            (groundCompilerEventFlowAuditRouteEventAtDefault 1 flow))
          (groundCompilerEventFlowAuditRouteDecodeBHist
            (groundCompilerEventFlowAuditRouteEventAtDefault 2 flow))
          (groundCompilerEventFlowAuditRouteDecodeBHist
            (groundCompilerEventFlowAuditRouteEventAtDefault 3 flow))
          (groundCompilerEventFlowAuditRouteDecodeBHist
            (groundCompilerEventFlowAuditRouteEventAtDefault 4 flow))
          (groundCompilerEventFlowAuditRouteDecodeBHist
            (groundCompilerEventFlowAuditRouteEventAtDefault 5 flow))
          (groundCompilerEventFlowAuditRouteDecodeBHist
            (groundCompilerEventFlowAuditRouteEventAtDefault 6 flow))
          (groundCompilerEventFlowAuditRouteDecodeBHist
            (groundCompilerEventFlowAuditRouteEventAtDefault 7 flow))
          (groundCompilerEventFlowAuditRouteDecodeBHist
            (groundCompilerEventFlowAuditRouteEventAtDefault 8 flow))
          (groundCompilerEventFlowAuditRouteDecodeBHist
            (groundCompilerEventFlowAuditRouteEventAtDefault 9 flow)))

private theorem GroundCompilerEventFlowAuditRouteTasteGate_round_trip
    (x : GroundCompilerEventFlowAuditRouteUp) :
    groundCompilerEventFlowAuditRouteFromEventFlow
      (groundCompilerEventFlowAuditRouteToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk E C L G A B H K P N =>
      change
        some
          (GroundCompilerEventFlowAuditRouteUp.mk
            (groundCompilerEventFlowAuditRouteDecodeBHist
              (groundCompilerEventFlowAuditRouteEncodeBHist E))
            (groundCompilerEventFlowAuditRouteDecodeBHist
              (groundCompilerEventFlowAuditRouteEncodeBHist C))
            (groundCompilerEventFlowAuditRouteDecodeBHist
              (groundCompilerEventFlowAuditRouteEncodeBHist L))
            (groundCompilerEventFlowAuditRouteDecodeBHist
              (groundCompilerEventFlowAuditRouteEncodeBHist G))
            (groundCompilerEventFlowAuditRouteDecodeBHist
              (groundCompilerEventFlowAuditRouteEncodeBHist A))
            (groundCompilerEventFlowAuditRouteDecodeBHist
              (groundCompilerEventFlowAuditRouteEncodeBHist B))
            (groundCompilerEventFlowAuditRouteDecodeBHist
              (groundCompilerEventFlowAuditRouteEncodeBHist H))
            (groundCompilerEventFlowAuditRouteDecodeBHist
              (groundCompilerEventFlowAuditRouteEncodeBHist K))
            (groundCompilerEventFlowAuditRouteDecodeBHist
              (groundCompilerEventFlowAuditRouteEncodeBHist P))
            (groundCompilerEventFlowAuditRouteDecodeBHist
              (groundCompilerEventFlowAuditRouteEncodeBHist N))) =
          some (GroundCompilerEventFlowAuditRouteUp.mk E C L G A B H K P N)
      rw [GroundCompilerEventFlowAuditRouteTasteGate_decode_encode E,
        GroundCompilerEventFlowAuditRouteTasteGate_decode_encode C,
        GroundCompilerEventFlowAuditRouteTasteGate_decode_encode L,
        GroundCompilerEventFlowAuditRouteTasteGate_decode_encode G,
        GroundCompilerEventFlowAuditRouteTasteGate_decode_encode A,
        GroundCompilerEventFlowAuditRouteTasteGate_decode_encode B,
        GroundCompilerEventFlowAuditRouteTasteGate_decode_encode H,
        GroundCompilerEventFlowAuditRouteTasteGate_decode_encode K,
        GroundCompilerEventFlowAuditRouteTasteGate_decode_encode P,
        GroundCompilerEventFlowAuditRouteTasteGate_decode_encode N]

private theorem GroundCompilerEventFlowAuditRouteTasteGate_toEventFlow_injective
    {x y : GroundCompilerEventFlowAuditRouteUp} :
    groundCompilerEventFlowAuditRouteToEventFlow x =
      groundCompilerEventFlowAuditRouteToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      groundCompilerEventFlowAuditRouteFromEventFlow
          (groundCompilerEventFlowAuditRouteToEventFlow x) =
        groundCompilerEventFlowAuditRouteFromEventFlow
          (groundCompilerEventFlowAuditRouteToEventFlow y) :=
    congrArg groundCompilerEventFlowAuditRouteFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (GroundCompilerEventFlowAuditRouteTasteGate_round_trip x).symm
      (Eq.trans hread (GroundCompilerEventFlowAuditRouteTasteGate_round_trip y)))

instance groundCompilerEventFlowAuditRouteBHistCarrier :
    BHistCarrier GroundCompilerEventFlowAuditRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := groundCompilerEventFlowAuditRouteToEventFlow
  fromEventFlow := groundCompilerEventFlowAuditRouteFromEventFlow

instance groundCompilerEventFlowAuditRouteChapterTasteGate :
    ChapterTasteGate GroundCompilerEventFlowAuditRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      groundCompilerEventFlowAuditRouteFromEventFlow
        (groundCompilerEventFlowAuditRouteToEventFlow x) = some x
    exact GroundCompilerEventFlowAuditRouteTasteGate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (GroundCompilerEventFlowAuditRouteTasteGate_toEventFlow_injective heq)

theorem GroundCompilerEventFlowAuditRouteTasteGate_single_carrier_alignment :
    (forall h : BHist,
      groundCompilerEventFlowAuditRouteDecodeBHist
        (groundCompilerEventFlowAuditRouteEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier GroundCompilerEventFlowAuditRouteUp) ∧
        Nonempty (ChapterTasteGate GroundCompilerEventFlowAuditRouteUp) ∧
          groundCompilerEventFlowAuditRouteEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact GroundCompilerEventFlowAuditRouteTasteGate_decode_encode
  · constructor
    · exact
        ⟨{
          toEventFlow := groundCompilerEventFlowAuditRouteToEventFlow
          fromEventFlow := groundCompilerEventFlowAuditRouteFromEventFlow
        }⟩
    · constructor
      · exact
          ⟨{
            round_trip := by
              intro x
              change
                groundCompilerEventFlowAuditRouteFromEventFlow
                  (groundCompilerEventFlowAuditRouteToEventFlow x) = some x
              exact GroundCompilerEventFlowAuditRouteTasteGate_round_trip x
            layer_separation := by
              intro x y hxy heq
              exact hxy (GroundCompilerEventFlowAuditRouteTasteGate_toEventFlow_injective heq)
          }⟩
      · rfl

end BEDC.Derived.GroundCompilerEventFlowAuditRouteUp
