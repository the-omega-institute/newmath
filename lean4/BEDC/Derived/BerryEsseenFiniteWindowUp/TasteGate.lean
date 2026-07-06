import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BerryEsseenFiniteWindowUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BerryEsseenFiniteWindowUp : Type where
  | mk (C L D R E G H K P N : BHist) : BerryEsseenFiniteWindowUp
  deriving DecidableEq

def berryEsseenFiniteWindowEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: berryEsseenFiniteWindowEncodeBHist h
  | BHist.e1 h => BMark.b1 :: berryEsseenFiniteWindowEncodeBHist h

def berryEsseenFiniteWindowDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (berryEsseenFiniteWindowDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (berryEsseenFiniteWindowDecodeBHist tail)

private theorem berryEsseenFiniteWindow_decode_encode_bhist :
    ∀ h : BHist,
      berryEsseenFiniteWindowDecodeBHist
        (berryEsseenFiniteWindowEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def berryEsseenFiniteWindowFields :
    BerryEsseenFiniteWindowUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BerryEsseenFiniteWindowUp.mk C L D R E G H K P N =>
      [C, L, D, R, E, G, H, K, P, N]

def berryEsseenFiniteWindowToEventFlow :
    BerryEsseenFiniteWindowUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (berryEsseenFiniteWindowFields x).map berryEsseenFiniteWindowEncodeBHist

private def berryEsseenFiniteWindowEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => berryEsseenFiniteWindowEventAtDefault index rest

def berryEsseenFiniteWindowFromEventFlow :
    EventFlow → Option BerryEsseenFiniteWindowUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (BerryEsseenFiniteWindowUp.mk
        (berryEsseenFiniteWindowDecodeBHist (berryEsseenFiniteWindowEventAtDefault 0 ef))
        (berryEsseenFiniteWindowDecodeBHist (berryEsseenFiniteWindowEventAtDefault 1 ef))
        (berryEsseenFiniteWindowDecodeBHist (berryEsseenFiniteWindowEventAtDefault 2 ef))
        (berryEsseenFiniteWindowDecodeBHist (berryEsseenFiniteWindowEventAtDefault 3 ef))
        (berryEsseenFiniteWindowDecodeBHist (berryEsseenFiniteWindowEventAtDefault 4 ef))
        (berryEsseenFiniteWindowDecodeBHist (berryEsseenFiniteWindowEventAtDefault 5 ef))
        (berryEsseenFiniteWindowDecodeBHist (berryEsseenFiniteWindowEventAtDefault 6 ef))
        (berryEsseenFiniteWindowDecodeBHist (berryEsseenFiniteWindowEventAtDefault 7 ef))
        (berryEsseenFiniteWindowDecodeBHist (berryEsseenFiniteWindowEventAtDefault 8 ef))
        (berryEsseenFiniteWindowDecodeBHist (berryEsseenFiniteWindowEventAtDefault 9 ef)))

private theorem berryEsseenFiniteWindow_round_trip :
    ∀ x : BerryEsseenFiniteWindowUp,
      berryEsseenFiniteWindowFromEventFlow
        (berryEsseenFiniteWindowToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk C L D R E G H K P N =>
      change
        some
          (BerryEsseenFiniteWindowUp.mk
            (berryEsseenFiniteWindowDecodeBHist (berryEsseenFiniteWindowEncodeBHist C))
            (berryEsseenFiniteWindowDecodeBHist (berryEsseenFiniteWindowEncodeBHist L))
            (berryEsseenFiniteWindowDecodeBHist (berryEsseenFiniteWindowEncodeBHist D))
            (berryEsseenFiniteWindowDecodeBHist (berryEsseenFiniteWindowEncodeBHist R))
            (berryEsseenFiniteWindowDecodeBHist (berryEsseenFiniteWindowEncodeBHist E))
            (berryEsseenFiniteWindowDecodeBHist (berryEsseenFiniteWindowEncodeBHist G))
            (berryEsseenFiniteWindowDecodeBHist (berryEsseenFiniteWindowEncodeBHist H))
            (berryEsseenFiniteWindowDecodeBHist (berryEsseenFiniteWindowEncodeBHist K))
            (berryEsseenFiniteWindowDecodeBHist (berryEsseenFiniteWindowEncodeBHist P))
            (berryEsseenFiniteWindowDecodeBHist (berryEsseenFiniteWindowEncodeBHist N))) =
          some (BerryEsseenFiniteWindowUp.mk C L D R E G H K P N)
      rw [berryEsseenFiniteWindow_decode_encode_bhist C,
        berryEsseenFiniteWindow_decode_encode_bhist L,
        berryEsseenFiniteWindow_decode_encode_bhist D,
        berryEsseenFiniteWindow_decode_encode_bhist R,
        berryEsseenFiniteWindow_decode_encode_bhist E,
        berryEsseenFiniteWindow_decode_encode_bhist G,
        berryEsseenFiniteWindow_decode_encode_bhist H,
        berryEsseenFiniteWindow_decode_encode_bhist K,
        berryEsseenFiniteWindow_decode_encode_bhist P,
        berryEsseenFiniteWindow_decode_encode_bhist N]

private theorem berryEsseenFiniteWindowToEventFlow_injective
    {x y : BerryEsseenFiniteWindowUp} :
    berryEsseenFiniteWindowToEventFlow x =
      berryEsseenFiniteWindowToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      berryEsseenFiniteWindowFromEventFlow
          (berryEsseenFiniteWindowToEventFlow x) =
        berryEsseenFiniteWindowFromEventFlow
          (berryEsseenFiniteWindowToEventFlow y) :=
    congrArg berryEsseenFiniteWindowFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (berryEsseenFiniteWindow_round_trip x).symm
      (Eq.trans hread (berryEsseenFiniteWindow_round_trip y)))

private theorem berryEsseenFiniteWindow_fields_faithful :
    ∀ x y : BerryEsseenFiniteWindowUp,
      berryEsseenFiniteWindowFields x = berryEsseenFiniteWindowFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk C1 L1 D1 R1 E1 G1 H1 K1 P1 N1 =>
      cases y with
      | mk C2 L2 D2 R2 E2 G2 H2 K2 P2 N2 =>
          cases hfields
          rfl

instance berryEsseenFiniteWindowBHistCarrier :
    BHistCarrier BerryEsseenFiniteWindowUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := berryEsseenFiniteWindowToEventFlow
  fromEventFlow := berryEsseenFiniteWindowFromEventFlow

instance berryEsseenFiniteWindowChapterTasteGate :
    ChapterTasteGate BerryEsseenFiniteWindowUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      berryEsseenFiniteWindowFromEventFlow
        (berryEsseenFiniteWindowToEventFlow x) = some x
    exact berryEsseenFiniteWindow_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (berryEsseenFiniteWindowToEventFlow_injective heq)

instance berryEsseenFiniteWindowFieldFaithful :
    FieldFaithful BerryEsseenFiniteWindowUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := berryEsseenFiniteWindowFields
  field_faithful := berryEsseenFiniteWindow_fields_faithful

instance berryEsseenFiniteWindowNontrivial :
    Nontrivial BerryEsseenFiniteWindowUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BerryEsseenFiniteWindowUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BerryEsseenFiniteWindowUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BerryEsseenFiniteWindowUp :=
  -- BEDC touchpoint anchor: BHist BMark
  berryEsseenFiniteWindowChapterTasteGate

theorem BerryEsseenFiniteWindowTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      berryEsseenFiniteWindowDecodeBHist (berryEsseenFiniteWindowEncodeBHist h) = h) ∧
      (∀ x : BerryEsseenFiniteWindowUp,
        berryEsseenFiniteWindowFromEventFlow
          (berryEsseenFiniteWindowToEventFlow x) = some x) ∧
        (∀ x y : BerryEsseenFiniteWindowUp,
          berryEsseenFiniteWindowToEventFlow x =
            berryEsseenFiniteWindowToEventFlow y → x = y) ∧
          berryEsseenFiniteWindowEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  exact
    ⟨berryEsseenFiniteWindow_decode_encode_bhist,
      berryEsseenFiniteWindow_round_trip,
      (fun _ _ heq => berryEsseenFiniteWindowToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.BerryEsseenFiniteWindowUp
