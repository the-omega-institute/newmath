import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicToleranceScaleUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicToleranceScaleUp : Type where
  | mk (s d w r m e h c p n : BHist) : DyadicToleranceScaleUp
  deriving DecidableEq

def dyadicToleranceScaleEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicToleranceScaleEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicToleranceScaleEncodeBHist h

def dyadicToleranceScaleDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicToleranceScaleDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicToleranceScaleDecodeBHist tail)

private theorem DyadicToleranceScaleTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, dyadicToleranceScaleDecodeBHist (dyadicToleranceScaleEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dyadicToleranceScaleFields : DyadicToleranceScaleUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicToleranceScaleUp.mk s d w r m e h c p n => [s, d, w, r, m, e, h, c, p, n]

def dyadicToleranceScaleToEventFlow : DyadicToleranceScaleUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (dyadicToleranceScaleFields x).map dyadicToleranceScaleEncodeBHist

private def dyadicToleranceScaleEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => dyadicToleranceScaleEventAtDefault index rest

def dyadicToleranceScaleFromEventFlow (ef : EventFlow) : Option DyadicToleranceScaleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DyadicToleranceScaleUp.mk
      (dyadicToleranceScaleDecodeBHist (dyadicToleranceScaleEventAtDefault 0 ef))
      (dyadicToleranceScaleDecodeBHist (dyadicToleranceScaleEventAtDefault 1 ef))
      (dyadicToleranceScaleDecodeBHist (dyadicToleranceScaleEventAtDefault 2 ef))
      (dyadicToleranceScaleDecodeBHist (dyadicToleranceScaleEventAtDefault 3 ef))
      (dyadicToleranceScaleDecodeBHist (dyadicToleranceScaleEventAtDefault 4 ef))
      (dyadicToleranceScaleDecodeBHist (dyadicToleranceScaleEventAtDefault 5 ef))
      (dyadicToleranceScaleDecodeBHist (dyadicToleranceScaleEventAtDefault 6 ef))
      (dyadicToleranceScaleDecodeBHist (dyadicToleranceScaleEventAtDefault 7 ef))
      (dyadicToleranceScaleDecodeBHist (dyadicToleranceScaleEventAtDefault 8 ef))
      (dyadicToleranceScaleDecodeBHist (dyadicToleranceScaleEventAtDefault 9 ef)))

private theorem DyadicToleranceScaleTasteGate_single_carrier_alignment_round_trip :
    ∀ x : DyadicToleranceScaleUp,
      dyadicToleranceScaleFromEventFlow (dyadicToleranceScaleToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk s d w r m e h c p n =>
      change
        some
          (DyadicToleranceScaleUp.mk
            (dyadicToleranceScaleDecodeBHist (dyadicToleranceScaleEncodeBHist s))
            (dyadicToleranceScaleDecodeBHist (dyadicToleranceScaleEncodeBHist d))
            (dyadicToleranceScaleDecodeBHist (dyadicToleranceScaleEncodeBHist w))
            (dyadicToleranceScaleDecodeBHist (dyadicToleranceScaleEncodeBHist r))
            (dyadicToleranceScaleDecodeBHist (dyadicToleranceScaleEncodeBHist m))
            (dyadicToleranceScaleDecodeBHist (dyadicToleranceScaleEncodeBHist e))
            (dyadicToleranceScaleDecodeBHist (dyadicToleranceScaleEncodeBHist h))
            (dyadicToleranceScaleDecodeBHist (dyadicToleranceScaleEncodeBHist c))
            (dyadicToleranceScaleDecodeBHist (dyadicToleranceScaleEncodeBHist p))
            (dyadicToleranceScaleDecodeBHist (dyadicToleranceScaleEncodeBHist n))) =
          some (DyadicToleranceScaleUp.mk s d w r m e h c p n)
      rw [DyadicToleranceScaleTasteGate_single_carrier_alignment_decode s,
        DyadicToleranceScaleTasteGate_single_carrier_alignment_decode d,
        DyadicToleranceScaleTasteGate_single_carrier_alignment_decode w,
        DyadicToleranceScaleTasteGate_single_carrier_alignment_decode r,
        DyadicToleranceScaleTasteGate_single_carrier_alignment_decode m,
        DyadicToleranceScaleTasteGate_single_carrier_alignment_decode e,
        DyadicToleranceScaleTasteGate_single_carrier_alignment_decode h,
        DyadicToleranceScaleTasteGate_single_carrier_alignment_decode c,
        DyadicToleranceScaleTasteGate_single_carrier_alignment_decode p,
        DyadicToleranceScaleTasteGate_single_carrier_alignment_decode n]

private theorem DyadicToleranceScaleTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DyadicToleranceScaleUp} :
    dyadicToleranceScaleToEventFlow x = dyadicToleranceScaleToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicToleranceScaleFromEventFlow (dyadicToleranceScaleToEventFlow x) =
        dyadicToleranceScaleFromEventFlow (dyadicToleranceScaleToEventFlow y) :=
    congrArg dyadicToleranceScaleFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (DyadicToleranceScaleTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (DyadicToleranceScaleTasteGate_single_carrier_alignment_round_trip y)))

private theorem DyadicToleranceScaleTasteGate_single_carrier_alignment_fields :
    ∀ x y : DyadicToleranceScaleUp, dyadicToleranceScaleFields x = dyadicToleranceScaleFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk s1 d1 w1 r1 m1 e1 h1 c1 p1 n1 =>
      cases y with
      | mk s2 d2 w2 r2 m2 e2 h2 c2 p2 n2 =>
          cases hfields
          rfl

instance dyadicToleranceScaleBHistCarrier : BHistCarrier DyadicToleranceScaleUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicToleranceScaleToEventFlow
  fromEventFlow := dyadicToleranceScaleFromEventFlow

instance dyadicToleranceScaleChapterTasteGate : ChapterTasteGate DyadicToleranceScaleUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dyadicToleranceScaleFromEventFlow (dyadicToleranceScaleToEventFlow x) = some x
    exact DyadicToleranceScaleTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DyadicToleranceScaleTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance dyadicToleranceScaleFieldFaithful : FieldFaithful DyadicToleranceScaleUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := dyadicToleranceScaleFields
  field_faithful := DyadicToleranceScaleTasteGate_single_carrier_alignment_fields

instance dyadicToleranceScaleNontrivial : Nontrivial DyadicToleranceScaleUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DyadicToleranceScaleUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DyadicToleranceScaleUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate DyadicToleranceScaleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dyadicToleranceScaleChapterTasteGate

theorem DyadicToleranceScaleTasteGate_single_carrier_alignment :
    (∀ h : BHist, dyadicToleranceScaleDecodeBHist (dyadicToleranceScaleEncodeBHist h) = h) ∧
      (∀ x : DyadicToleranceScaleUp,
        dyadicToleranceScaleFromEventFlow (dyadicToleranceScaleToEventFlow x) = some x) ∧
        (∀ x y : DyadicToleranceScaleUp,
          dyadicToleranceScaleToEventFlow x = dyadicToleranceScaleToEventFlow y → x = y) ∧
          dyadicToleranceScaleEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨DyadicToleranceScaleTasteGate_single_carrier_alignment_decode,
      DyadicToleranceScaleTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => DyadicToleranceScaleTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.DyadicToleranceScaleUp
