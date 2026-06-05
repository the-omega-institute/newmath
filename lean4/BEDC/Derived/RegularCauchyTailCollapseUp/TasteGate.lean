import BEDC.Derived.RegularCauchyTailCollapseUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyTailCollapseUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def regularCauchyTailCollapseEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyTailCollapseEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyTailCollapseEncodeBHist h

def regularCauchyTailCollapseDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyTailCollapseDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyTailCollapseDecodeBHist tail)

private theorem RegularCauchyTailCollapseTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      regularCauchyTailCollapseDecodeBHist
        (regularCauchyTailCollapseEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyTailCollapseFields :
    _root_.BEDC.Derived.RegularCauchyTailCollapseUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | _root_.BEDC.Derived.RegularCauchyTailCollapseUp.mk R S D W Q U E H C P N =>
      [R, S, D, W, Q, U, E, H, C, P, N]

def regularCauchyTailCollapseToEventFlow :
    _root_.BEDC.Derived.RegularCauchyTailCollapseUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (regularCauchyTailCollapseFields x).map regularCauchyTailCollapseEncodeBHist

private def regularCauchyTailCollapseEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyTailCollapseEventAt index rest

def regularCauchyTailCollapseFromEventFlow :
    EventFlow → Option _root_.BEDC.Derived.RegularCauchyTailCollapseUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (_root_.BEDC.Derived.RegularCauchyTailCollapseUp.mk
        (regularCauchyTailCollapseDecodeBHist (regularCauchyTailCollapseEventAt 0 ef))
        (regularCauchyTailCollapseDecodeBHist (regularCauchyTailCollapseEventAt 1 ef))
        (regularCauchyTailCollapseDecodeBHist (regularCauchyTailCollapseEventAt 2 ef))
        (regularCauchyTailCollapseDecodeBHist (regularCauchyTailCollapseEventAt 3 ef))
        (regularCauchyTailCollapseDecodeBHist (regularCauchyTailCollapseEventAt 4 ef))
        (regularCauchyTailCollapseDecodeBHist (regularCauchyTailCollapseEventAt 5 ef))
        (regularCauchyTailCollapseDecodeBHist (regularCauchyTailCollapseEventAt 6 ef))
        (regularCauchyTailCollapseDecodeBHist (regularCauchyTailCollapseEventAt 7 ef))
        (regularCauchyTailCollapseDecodeBHist (regularCauchyTailCollapseEventAt 8 ef))
        (regularCauchyTailCollapseDecodeBHist (regularCauchyTailCollapseEventAt 9 ef))
        (regularCauchyTailCollapseDecodeBHist (regularCauchyTailCollapseEventAt 10 ef)))

private theorem RegularCauchyTailCollapseTasteGate_single_carrier_alignment_round_trip
    (x : _root_.BEDC.Derived.RegularCauchyTailCollapseUp) :
    regularCauchyTailCollapseFromEventFlow
      (regularCauchyTailCollapseToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk R S D W Q U E H C P N =>
      change
        some
          (_root_.BEDC.Derived.RegularCauchyTailCollapseUp.mk
            (regularCauchyTailCollapseDecodeBHist
              (regularCauchyTailCollapseEncodeBHist R))
            (regularCauchyTailCollapseDecodeBHist
              (regularCauchyTailCollapseEncodeBHist S))
            (regularCauchyTailCollapseDecodeBHist
              (regularCauchyTailCollapseEncodeBHist D))
            (regularCauchyTailCollapseDecodeBHist
              (regularCauchyTailCollapseEncodeBHist W))
            (regularCauchyTailCollapseDecodeBHist
              (regularCauchyTailCollapseEncodeBHist Q))
            (regularCauchyTailCollapseDecodeBHist
              (regularCauchyTailCollapseEncodeBHist U))
            (regularCauchyTailCollapseDecodeBHist
              (regularCauchyTailCollapseEncodeBHist E))
            (regularCauchyTailCollapseDecodeBHist
              (regularCauchyTailCollapseEncodeBHist H))
            (regularCauchyTailCollapseDecodeBHist
              (regularCauchyTailCollapseEncodeBHist C))
            (regularCauchyTailCollapseDecodeBHist
              (regularCauchyTailCollapseEncodeBHist P))
            (regularCauchyTailCollapseDecodeBHist
              (regularCauchyTailCollapseEncodeBHist N))) =
          some (_root_.BEDC.Derived.RegularCauchyTailCollapseUp.mk R S D W Q U E H C P N)
      rw [
        RegularCauchyTailCollapseTasteGate_single_carrier_alignment_decode R,
        RegularCauchyTailCollapseTasteGate_single_carrier_alignment_decode S,
        RegularCauchyTailCollapseTasteGate_single_carrier_alignment_decode D,
        RegularCauchyTailCollapseTasteGate_single_carrier_alignment_decode W,
        RegularCauchyTailCollapseTasteGate_single_carrier_alignment_decode Q,
        RegularCauchyTailCollapseTasteGate_single_carrier_alignment_decode U,
        RegularCauchyTailCollapseTasteGate_single_carrier_alignment_decode E,
        RegularCauchyTailCollapseTasteGate_single_carrier_alignment_decode H,
        RegularCauchyTailCollapseTasteGate_single_carrier_alignment_decode C,
        RegularCauchyTailCollapseTasteGate_single_carrier_alignment_decode P,
        RegularCauchyTailCollapseTasteGate_single_carrier_alignment_decode N]

private theorem RegularCauchyTailCollapseTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : _root_.BEDC.Derived.RegularCauchyTailCollapseUp} :
    regularCauchyTailCollapseToEventFlow x =
        regularCauchyTailCollapseToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyTailCollapseFromEventFlow
          (regularCauchyTailCollapseToEventFlow x) =
        regularCauchyTailCollapseFromEventFlow
          (regularCauchyTailCollapseToEventFlow y) :=
    congrArg regularCauchyTailCollapseFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularCauchyTailCollapseTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularCauchyTailCollapseTasteGate_single_carrier_alignment_round_trip y)))

instance regularCauchyTailCollapseBHistCarrier :
    BHistCarrier _root_.BEDC.Derived.RegularCauchyTailCollapseUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyTailCollapseToEventFlow
  fromEventFlow := regularCauchyTailCollapseFromEventFlow

instance regularCauchyTailCollapseChapterTasteGate :
    ChapterTasteGate _root_.BEDC.Derived.RegularCauchyTailCollapseUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyTailCollapseFromEventFlow
        (regularCauchyTailCollapseToEventFlow x) = some x
    exact RegularCauchyTailCollapseTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RegularCauchyTailCollapseTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

def RegularCauchyTailCollapseTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate _root_.BEDC.Derived.RegularCauchyTailCollapseUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyTailCollapseChapterTasteGate

theorem RegularCauchyTailCollapseTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyTailCollapseDecodeBHist
        (regularCauchyTailCollapseEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier _root_.BEDC.Derived.RegularCauchyTailCollapseUp) ∧
        Nonempty (ChapterTasteGate _root_.BEDC.Derived.RegularCauchyTailCollapseUp) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨RegularCauchyTailCollapseTasteGate_single_carrier_alignment_decode,
      ⟨regularCauchyTailCollapseBHistCarrier⟩,
      ⟨regularCauchyTailCollapseChapterTasteGate⟩⟩

end BEDC.Derived.RegularCauchyTailCollapseUp
