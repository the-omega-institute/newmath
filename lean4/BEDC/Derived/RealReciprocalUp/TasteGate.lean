import BEDC.Derived.RealReciprocalUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealReciprocalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def realReciprocalEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realReciprocalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realReciprocalEncodeBHist h

def realReciprocalDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realReciprocalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realReciprocalDecodeBHist tail)

private theorem RealReciprocalTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, realReciprocalDecodeBHist (realReciprocalEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realReciprocalFields : _root_.BEDC.Derived.RealReciprocalUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | _root_.BEDC.Derived.RealReciprocalUp.mk X A B Q D E H C P N =>
      [X, A, B, Q, D, E, H, C, P, N]

def realReciprocalToEventFlow : _root_.BEDC.Derived.RealReciprocalUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (realReciprocalFields x).map realReciprocalEncodeBHist

private def realReciprocalEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realReciprocalEventAt index rest

def realReciprocalFromEventFlow :
    EventFlow → Option _root_.BEDC.Derived.RealReciprocalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (_root_.BEDC.Derived.RealReciprocalUp.mk
        (realReciprocalDecodeBHist (realReciprocalEventAt 0 ef))
        (realReciprocalDecodeBHist (realReciprocalEventAt 1 ef))
        (realReciprocalDecodeBHist (realReciprocalEventAt 2 ef))
        (realReciprocalDecodeBHist (realReciprocalEventAt 3 ef))
        (realReciprocalDecodeBHist (realReciprocalEventAt 4 ef))
        (realReciprocalDecodeBHist (realReciprocalEventAt 5 ef))
        (realReciprocalDecodeBHist (realReciprocalEventAt 6 ef))
        (realReciprocalDecodeBHist (realReciprocalEventAt 7 ef))
        (realReciprocalDecodeBHist (realReciprocalEventAt 8 ef))
        (realReciprocalDecodeBHist (realReciprocalEventAt 9 ef)))

private theorem RealReciprocalTasteGate_single_carrier_alignment_round_trip
    (x : _root_.BEDC.Derived.RealReciprocalUp) :
    realReciprocalFromEventFlow (realReciprocalToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X A B Q D E H C P N =>
      change
        some
          (_root_.BEDC.Derived.RealReciprocalUp.mk
            (realReciprocalDecodeBHist (realReciprocalEncodeBHist X))
            (realReciprocalDecodeBHist (realReciprocalEncodeBHist A))
            (realReciprocalDecodeBHist (realReciprocalEncodeBHist B))
            (realReciprocalDecodeBHist (realReciprocalEncodeBHist Q))
            (realReciprocalDecodeBHist (realReciprocalEncodeBHist D))
            (realReciprocalDecodeBHist (realReciprocalEncodeBHist E))
            (realReciprocalDecodeBHist (realReciprocalEncodeBHist H))
            (realReciprocalDecodeBHist (realReciprocalEncodeBHist C))
            (realReciprocalDecodeBHist (realReciprocalEncodeBHist P))
            (realReciprocalDecodeBHist (realReciprocalEncodeBHist N))) =
          some (_root_.BEDC.Derived.RealReciprocalUp.mk X A B Q D E H C P N)
      rw [
        RealReciprocalTasteGate_single_carrier_alignment_decode X,
        RealReciprocalTasteGate_single_carrier_alignment_decode A,
        RealReciprocalTasteGate_single_carrier_alignment_decode B,
        RealReciprocalTasteGate_single_carrier_alignment_decode Q,
        RealReciprocalTasteGate_single_carrier_alignment_decode D,
        RealReciprocalTasteGate_single_carrier_alignment_decode E,
        RealReciprocalTasteGate_single_carrier_alignment_decode H,
        RealReciprocalTasteGate_single_carrier_alignment_decode C,
        RealReciprocalTasteGate_single_carrier_alignment_decode P,
        RealReciprocalTasteGate_single_carrier_alignment_decode N]

private theorem RealReciprocalTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RealReciprocalUp} :
    realReciprocalToEventFlow x = realReciprocalToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realReciprocalFromEventFlow (realReciprocalToEventFlow x) =
        realReciprocalFromEventFlow (realReciprocalToEventFlow y) :=
    congrArg realReciprocalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RealReciprocalTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RealReciprocalTasteGate_single_carrier_alignment_round_trip y)))

instance realReciprocalBHistCarrier :
    BHistCarrier _root_.BEDC.Derived.RealReciprocalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realReciprocalToEventFlow
  fromEventFlow := realReciprocalFromEventFlow

instance realReciprocalChapterTasteGate :
    ChapterTasteGate _root_.BEDC.Derived.RealReciprocalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realReciprocalFromEventFlow (realReciprocalToEventFlow x) = some x
    exact RealReciprocalTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RealReciprocalTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def RealReciprocalTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate _root_.BEDC.Derived.RealReciprocalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realReciprocalChapterTasteGate

theorem RealReciprocalTasteGate_single_carrier_alignment :
    (∀ h : BHist, realReciprocalDecodeBHist (realReciprocalEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier RealReciprocalUp) ∧
        Nonempty (ChapterTasteGate RealReciprocalUp) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨RealReciprocalTasteGate_single_carrier_alignment_decode,
      ⟨realReciprocalBHistCarrier⟩, ⟨realReciprocalChapterTasteGate⟩⟩

end BEDC.Derived.RealReciprocalUp
