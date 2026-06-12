import BEDC.Derived.LocatedIntervalFanBarrierUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedIntervalFanBarrierUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def locatedIntervalFanBarrierEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedIntervalFanBarrierEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedIntervalFanBarrierEncodeBHist h

def locatedIntervalFanBarrierDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedIntervalFanBarrierDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedIntervalFanBarrierDecodeBHist tail)

private theorem locatedIntervalFanBarrierDecodeEncode :
    ∀ h : BHist,
      locatedIntervalFanBarrierDecodeBHist
        (locatedIntervalFanBarrierEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def locatedIntervalFanBarrierFields :
    _root_.BEDC.Derived.LocatedIntervalFanBarrierUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | _root_.BEDC.Derived.LocatedIntervalFanBarrierUp.mk I K F D S Q E H C P N =>
      [I, K, F, D, S, Q, E, H, C, P, N]

def locatedIntervalFanBarrierToEventFlow :
    _root_.BEDC.Derived.LocatedIntervalFanBarrierUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (locatedIntervalFanBarrierFields x).map locatedIntervalFanBarrierEncodeBHist

private def locatedIntervalFanBarrierEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => locatedIntervalFanBarrierEventAtDefault index rest

def locatedIntervalFanBarrierFromEventFlow :
    EventFlow → Option _root_.BEDC.Derived.LocatedIntervalFanBarrierUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (_root_.BEDC.Derived.LocatedIntervalFanBarrierUp.mk
          (locatedIntervalFanBarrierDecodeBHist
            (locatedIntervalFanBarrierEventAtDefault 0 ef))
          (locatedIntervalFanBarrierDecodeBHist
            (locatedIntervalFanBarrierEventAtDefault 1 ef))
          (locatedIntervalFanBarrierDecodeBHist
            (locatedIntervalFanBarrierEventAtDefault 2 ef))
          (locatedIntervalFanBarrierDecodeBHist
            (locatedIntervalFanBarrierEventAtDefault 3 ef))
          (locatedIntervalFanBarrierDecodeBHist
            (locatedIntervalFanBarrierEventAtDefault 4 ef))
          (locatedIntervalFanBarrierDecodeBHist
            (locatedIntervalFanBarrierEventAtDefault 5 ef))
          (locatedIntervalFanBarrierDecodeBHist
            (locatedIntervalFanBarrierEventAtDefault 6 ef))
          (locatedIntervalFanBarrierDecodeBHist
            (locatedIntervalFanBarrierEventAtDefault 7 ef))
          (locatedIntervalFanBarrierDecodeBHist
            (locatedIntervalFanBarrierEventAtDefault 8 ef))
          (locatedIntervalFanBarrierDecodeBHist
            (locatedIntervalFanBarrierEventAtDefault 9 ef))
          (locatedIntervalFanBarrierDecodeBHist
            (locatedIntervalFanBarrierEventAtDefault 10 ef)))

private theorem locatedIntervalFanBarrierRoundTrip :
    ∀ x : _root_.BEDC.Derived.LocatedIntervalFanBarrierUp,
      locatedIntervalFanBarrierFromEventFlow
          (locatedIntervalFanBarrierToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I K F D S Q E H C P N =>
      change
        some
            (_root_.BEDC.Derived.LocatedIntervalFanBarrierUp.mk
              (locatedIntervalFanBarrierDecodeBHist
                (locatedIntervalFanBarrierEncodeBHist I))
              (locatedIntervalFanBarrierDecodeBHist
                (locatedIntervalFanBarrierEncodeBHist K))
              (locatedIntervalFanBarrierDecodeBHist
                (locatedIntervalFanBarrierEncodeBHist F))
              (locatedIntervalFanBarrierDecodeBHist
                (locatedIntervalFanBarrierEncodeBHist D))
              (locatedIntervalFanBarrierDecodeBHist
                (locatedIntervalFanBarrierEncodeBHist S))
              (locatedIntervalFanBarrierDecodeBHist
                (locatedIntervalFanBarrierEncodeBHist Q))
              (locatedIntervalFanBarrierDecodeBHist
                (locatedIntervalFanBarrierEncodeBHist E))
              (locatedIntervalFanBarrierDecodeBHist
                (locatedIntervalFanBarrierEncodeBHist H))
              (locatedIntervalFanBarrierDecodeBHist
                (locatedIntervalFanBarrierEncodeBHist C))
              (locatedIntervalFanBarrierDecodeBHist
                (locatedIntervalFanBarrierEncodeBHist P))
              (locatedIntervalFanBarrierDecodeBHist
                (locatedIntervalFanBarrierEncodeBHist N))) =
          some (_root_.BEDC.Derived.LocatedIntervalFanBarrierUp.mk I K F D S Q E H C P N)
      rw [locatedIntervalFanBarrierDecodeEncode I, locatedIntervalFanBarrierDecodeEncode K,
        locatedIntervalFanBarrierDecodeEncode F, locatedIntervalFanBarrierDecodeEncode D,
        locatedIntervalFanBarrierDecodeEncode S, locatedIntervalFanBarrierDecodeEncode Q,
        locatedIntervalFanBarrierDecodeEncode E, locatedIntervalFanBarrierDecodeEncode H,
        locatedIntervalFanBarrierDecodeEncode C, locatedIntervalFanBarrierDecodeEncode P,
        locatedIntervalFanBarrierDecodeEncode N]

private theorem locatedIntervalFanBarrierToEventFlow_injective
    {x y : _root_.BEDC.Derived.LocatedIntervalFanBarrierUp} :
    locatedIntervalFanBarrierToEventFlow x =
      locatedIntervalFanBarrierToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedIntervalFanBarrierFromEventFlow
          (locatedIntervalFanBarrierToEventFlow x) =
        locatedIntervalFanBarrierFromEventFlow
          (locatedIntervalFanBarrierToEventFlow y) :=
    congrArg locatedIntervalFanBarrierFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (locatedIntervalFanBarrierRoundTrip x).symm
      (Eq.trans hread (locatedIntervalFanBarrierRoundTrip y)))

instance locatedIntervalFanBarrierBHistCarrier :
    BHistCarrier _root_.BEDC.Derived.LocatedIntervalFanBarrierUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedIntervalFanBarrierToEventFlow
  fromEventFlow := locatedIntervalFanBarrierFromEventFlow

instance locatedIntervalFanBarrierChapterTasteGate :
    ChapterTasteGate _root_.BEDC.Derived.LocatedIntervalFanBarrierUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      locatedIntervalFanBarrierFromEventFlow
          (locatedIntervalFanBarrierToEventFlow x) =
        some x
    exact locatedIntervalFanBarrierRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (locatedIntervalFanBarrierToEventFlow_injective heq)

def taste_gate :
    ChapterTasteGate _root_.BEDC.Derived.LocatedIntervalFanBarrierUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locatedIntervalFanBarrierChapterTasteGate

theorem LocatedIntervalFanBarrierFiniteCoverHandoff
    (x : _root_.BEDC.Derived.LocatedIntervalFanBarrierUp) :
    (exists I K F D S Q E H C P N : BHist,
      x = _root_.BEDC.Derived.LocatedIntervalFanBarrierUp.mk I K F D S Q E H C P N) ∧
      ChapterTasteGate _root_.BEDC.Derived.LocatedIntervalFanBarrierUp := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · cases x with
    | mk I K F D S Q E H C P N =>
        exact ⟨I, K, F, D, S, Q, E, H, C, P, N, rfl⟩
  · exact locatedIntervalFanBarrierChapterTasteGate

end BEDC.Derived.LocatedIntervalFanBarrierUp
