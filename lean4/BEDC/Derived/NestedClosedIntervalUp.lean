import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

structure NestedClosedIntervalUp where
  intervalRows : BHist
  dyadicLedger : BHist
  streamWindow : BHist
  regularReadback : BHist
  realHandoff : BHist
  hsameTransport : BHist
  contReplay : BHist
  packageProvenance : BHist
  localName : BHist

namespace NestedClosedIntervalUp

def nestedClosedIntervalEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: nestedClosedIntervalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: nestedClosedIntervalEncodeBHist h

def nestedClosedIntervalDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (nestedClosedIntervalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (nestedClosedIntervalDecodeBHist tail)

private theorem NestedClosedIntervalTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, nestedClosedIntervalDecodeBHist (nestedClosedIntervalEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def nestedClosedIntervalFields : NestedClosedIntervalUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | NestedClosedIntervalUp.mk intervalRows dyadicLedger streamWindow regularReadback
      realHandoff hsameTransport contReplay packageProvenance localName =>
      [intervalRows, dyadicLedger, streamWindow, regularReadback, realHandoff,
        hsameTransport, contReplay, packageProvenance, localName]

def nestedClosedIntervalToEventFlow : NestedClosedIntervalUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (nestedClosedIntervalFields x).map nestedClosedIntervalEncodeBHist

def nestedClosedIntervalEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => nestedClosedIntervalEventAt index rest

def nestedClosedIntervalFromEventFlow : EventFlow -> Option NestedClosedIntervalUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      some
        (NestedClosedIntervalUp.mk
          (nestedClosedIntervalDecodeBHist (nestedClosedIntervalEventAt 0 flow))
          (nestedClosedIntervalDecodeBHist (nestedClosedIntervalEventAt 1 flow))
          (nestedClosedIntervalDecodeBHist (nestedClosedIntervalEventAt 2 flow))
          (nestedClosedIntervalDecodeBHist (nestedClosedIntervalEventAt 3 flow))
          (nestedClosedIntervalDecodeBHist (nestedClosedIntervalEventAt 4 flow))
          (nestedClosedIntervalDecodeBHist (nestedClosedIntervalEventAt 5 flow))
          (nestedClosedIntervalDecodeBHist (nestedClosedIntervalEventAt 6 flow))
          (nestedClosedIntervalDecodeBHist (nestedClosedIntervalEventAt 7 flow))
          (nestedClosedIntervalDecodeBHist (nestedClosedIntervalEventAt 8 flow)))

private theorem NestedClosedIntervalTasteGate_single_carrier_alignment_round_trip :
    ∀ x : NestedClosedIntervalUp,
      nestedClosedIntervalFromEventFlow (nestedClosedIntervalToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk intervalRows dyadicLedger streamWindow regularReadback realHandoff hsameTransport
      contReplay packageProvenance localName =>
      change
        some
          (NestedClosedIntervalUp.mk
            (nestedClosedIntervalDecodeBHist (nestedClosedIntervalEncodeBHist intervalRows))
            (nestedClosedIntervalDecodeBHist (nestedClosedIntervalEncodeBHist dyadicLedger))
            (nestedClosedIntervalDecodeBHist (nestedClosedIntervalEncodeBHist streamWindow))
            (nestedClosedIntervalDecodeBHist (nestedClosedIntervalEncodeBHist regularReadback))
            (nestedClosedIntervalDecodeBHist (nestedClosedIntervalEncodeBHist realHandoff))
            (nestedClosedIntervalDecodeBHist (nestedClosedIntervalEncodeBHist hsameTransport))
            (nestedClosedIntervalDecodeBHist (nestedClosedIntervalEncodeBHist contReplay))
            (nestedClosedIntervalDecodeBHist (nestedClosedIntervalEncodeBHist packageProvenance))
            (nestedClosedIntervalDecodeBHist (nestedClosedIntervalEncodeBHist localName))) =
          some
            (NestedClosedIntervalUp.mk intervalRows dyadicLedger streamWindow regularReadback
              realHandoff hsameTransport contReplay packageProvenance localName)
      rw [NestedClosedIntervalTasteGate_single_carrier_alignment_decode intervalRows,
        NestedClosedIntervalTasteGate_single_carrier_alignment_decode dyadicLedger,
        NestedClosedIntervalTasteGate_single_carrier_alignment_decode streamWindow,
        NestedClosedIntervalTasteGate_single_carrier_alignment_decode regularReadback,
        NestedClosedIntervalTasteGate_single_carrier_alignment_decode realHandoff,
        NestedClosedIntervalTasteGate_single_carrier_alignment_decode hsameTransport,
        NestedClosedIntervalTasteGate_single_carrier_alignment_decode contReplay,
        NestedClosedIntervalTasteGate_single_carrier_alignment_decode packageProvenance,
        NestedClosedIntervalTasteGate_single_carrier_alignment_decode localName]

private theorem nestedClosedIntervalToEventFlow_injective {x y : NestedClosedIntervalUp} :
    nestedClosedIntervalToEventFlow x = nestedClosedIntervalToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      nestedClosedIntervalFromEventFlow (nestedClosedIntervalToEventFlow x) =
        nestedClosedIntervalFromEventFlow (nestedClosedIntervalToEventFlow y) :=
    congrArg nestedClosedIntervalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (NestedClosedIntervalTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (NestedClosedIntervalTasteGate_single_carrier_alignment_round_trip y)))

instance nestedClosedIntervalBHistCarrier : BHistCarrier NestedClosedIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := nestedClosedIntervalToEventFlow
  fromEventFlow := nestedClosedIntervalFromEventFlow

instance nestedClosedIntervalChapterTasteGate : ChapterTasteGate NestedClosedIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change nestedClosedIntervalFromEventFlow (nestedClosedIntervalToEventFlow x) = some x
    exact NestedClosedIntervalTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (nestedClosedIntervalToEventFlow_injective heq)

theorem NestedClosedIntervalTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier NestedClosedIntervalUp) ∧
      Nonempty (ChapterTasteGate NestedClosedIntervalUp) ∧
        (∀ h : BHist, nestedClosedIntervalDecodeBHist (nestedClosedIntervalEncodeBHist h) = h) ∧
          (∀ x : NestedClosedIntervalUp,
            nestedClosedIntervalFromEventFlow (nestedClosedIntervalToEventFlow x) = some x) ∧
            nestedClosedIntervalEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨nestedClosedIntervalBHistCarrier⟩, ⟨nestedClosedIntervalChapterTasteGate⟩,
      NestedClosedIntervalTasteGate_single_carrier_alignment_decode,
      NestedClosedIntervalTasteGate_single_carrier_alignment_round_trip, rfl⟩

theorem NestedClosedIntervalCarrier_seed_boundary
    {I D S R E H C P N intervalDyadic dyadicStream streamReadback readbackReal : BHist} :
    Cont I D intervalDyadic ->
      Cont intervalDyadic S dyadicStream ->
        Cont dyadicStream R streamReadback ->
          Cont streamReadback E readbackReal ->
            UnaryHistory I ->
              UnaryHistory D ->
                UnaryHistory S ->
                  UnaryHistory R ->
                    UnaryHistory E ->
                      UnaryHistory intervalDyadic ∧ UnaryHistory dyadicStream ∧
                        UnaryHistory streamReadback ∧ UnaryHistory readbackReal ∧
                          Cont I D intervalDyadic ∧
                            Cont intervalDyadic S dyadicStream ∧
                              Cont dyadicStream R streamReadback ∧
                                Cont streamReadback E readbackReal := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro intervalRoute streamRoute readbackRoute realRoute unaryI unaryD unaryS unaryR unaryE
  have unaryIntervalDyadic : UnaryHistory intervalDyadic :=
    unary_cont_closed unaryI unaryD intervalRoute
  have unaryDyadicStream : UnaryHistory dyadicStream :=
    unary_cont_closed unaryIntervalDyadic unaryS streamRoute
  have unaryStreamReadback : UnaryHistory streamReadback :=
    unary_cont_closed unaryDyadicStream unaryR readbackRoute
  have unaryReadbackReal : UnaryHistory readbackReal :=
    unary_cont_closed unaryStreamReadback unaryE realRoute
  exact
    ⟨unaryIntervalDyadic, unaryDyadicStream, unaryStreamReadback, unaryReadbackReal,
      intervalRoute, streamRoute, readbackRoute, realRoute⟩

end NestedClosedIntervalUp

end BEDC.Derived
