import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MooreSmithCauchyNetFilterBridgeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MooreSmithCauchyNetFilterBridgeUp : Type where
  | mk (D T F K U M S R Y E H C P N : BHist) :
      MooreSmithCauchyNetFilterBridgeUp
  deriving DecidableEq

def mooreSmithCauchyNetFilterBridgeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: mooreSmithCauchyNetFilterBridgeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: mooreSmithCauchyNetFilterBridgeEncodeBHist h

def mooreSmithCauchyNetFilterBridgeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (mooreSmithCauchyNetFilterBridgeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (mooreSmithCauchyNetFilterBridgeDecodeBHist tail)

private theorem MooreSmithCauchyNetFilterBridgeTasteGate_decode_encode :
    ∀ h : BHist,
      mooreSmithCauchyNetFilterBridgeDecodeBHist
        (mooreSmithCauchyNetFilterBridgeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def mooreSmithCauchyNetFilterBridgeFields :
    MooreSmithCauchyNetFilterBridgeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MooreSmithCauchyNetFilterBridgeUp.mk D T F K U M S R Y E H C P N =>
      [D, T, F, K, U, M, S, R, Y, E, H, C, P, N]

def mooreSmithCauchyNetFilterBridgeToEventFlow :
    MooreSmithCauchyNetFilterBridgeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (mooreSmithCauchyNetFilterBridgeFields x).map
        mooreSmithCauchyNetFilterBridgeEncodeBHist

private def mooreSmithCauchyNetFilterBridgeEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      mooreSmithCauchyNetFilterBridgeEventAtDefault index rest

def mooreSmithCauchyNetFilterBridgeFromEventFlow :
    EventFlow → Option MooreSmithCauchyNetFilterBridgeUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (MooreSmithCauchyNetFilterBridgeUp.mk
          (mooreSmithCauchyNetFilterBridgeDecodeBHist
            (mooreSmithCauchyNetFilterBridgeEventAtDefault 0 ef))
          (mooreSmithCauchyNetFilterBridgeDecodeBHist
            (mooreSmithCauchyNetFilterBridgeEventAtDefault 1 ef))
          (mooreSmithCauchyNetFilterBridgeDecodeBHist
            (mooreSmithCauchyNetFilterBridgeEventAtDefault 2 ef))
          (mooreSmithCauchyNetFilterBridgeDecodeBHist
            (mooreSmithCauchyNetFilterBridgeEventAtDefault 3 ef))
          (mooreSmithCauchyNetFilterBridgeDecodeBHist
            (mooreSmithCauchyNetFilterBridgeEventAtDefault 4 ef))
          (mooreSmithCauchyNetFilterBridgeDecodeBHist
            (mooreSmithCauchyNetFilterBridgeEventAtDefault 5 ef))
          (mooreSmithCauchyNetFilterBridgeDecodeBHist
            (mooreSmithCauchyNetFilterBridgeEventAtDefault 6 ef))
          (mooreSmithCauchyNetFilterBridgeDecodeBHist
            (mooreSmithCauchyNetFilterBridgeEventAtDefault 7 ef))
          (mooreSmithCauchyNetFilterBridgeDecodeBHist
            (mooreSmithCauchyNetFilterBridgeEventAtDefault 8 ef))
          (mooreSmithCauchyNetFilterBridgeDecodeBHist
            (mooreSmithCauchyNetFilterBridgeEventAtDefault 9 ef))
          (mooreSmithCauchyNetFilterBridgeDecodeBHist
            (mooreSmithCauchyNetFilterBridgeEventAtDefault 10 ef))
          (mooreSmithCauchyNetFilterBridgeDecodeBHist
            (mooreSmithCauchyNetFilterBridgeEventAtDefault 11 ef))
          (mooreSmithCauchyNetFilterBridgeDecodeBHist
            (mooreSmithCauchyNetFilterBridgeEventAtDefault 12 ef))
          (mooreSmithCauchyNetFilterBridgeDecodeBHist
            (mooreSmithCauchyNetFilterBridgeEventAtDefault 13 ef)))

private theorem MooreSmithCauchyNetFilterBridgeTasteGate_round_trip
    (x : MooreSmithCauchyNetFilterBridgeUp) :
    mooreSmithCauchyNetFilterBridgeFromEventFlow
      (mooreSmithCauchyNetFilterBridgeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk D T F K U M S R Y E H C P N =>
      change
        some
          (MooreSmithCauchyNetFilterBridgeUp.mk
            (mooreSmithCauchyNetFilterBridgeDecodeBHist
              (mooreSmithCauchyNetFilterBridgeEncodeBHist D))
            (mooreSmithCauchyNetFilterBridgeDecodeBHist
              (mooreSmithCauchyNetFilterBridgeEncodeBHist T))
            (mooreSmithCauchyNetFilterBridgeDecodeBHist
              (mooreSmithCauchyNetFilterBridgeEncodeBHist F))
            (mooreSmithCauchyNetFilterBridgeDecodeBHist
              (mooreSmithCauchyNetFilterBridgeEncodeBHist K))
            (mooreSmithCauchyNetFilterBridgeDecodeBHist
              (mooreSmithCauchyNetFilterBridgeEncodeBHist U))
            (mooreSmithCauchyNetFilterBridgeDecodeBHist
              (mooreSmithCauchyNetFilterBridgeEncodeBHist M))
            (mooreSmithCauchyNetFilterBridgeDecodeBHist
              (mooreSmithCauchyNetFilterBridgeEncodeBHist S))
            (mooreSmithCauchyNetFilterBridgeDecodeBHist
              (mooreSmithCauchyNetFilterBridgeEncodeBHist R))
            (mooreSmithCauchyNetFilterBridgeDecodeBHist
              (mooreSmithCauchyNetFilterBridgeEncodeBHist Y))
            (mooreSmithCauchyNetFilterBridgeDecodeBHist
              (mooreSmithCauchyNetFilterBridgeEncodeBHist E))
            (mooreSmithCauchyNetFilterBridgeDecodeBHist
              (mooreSmithCauchyNetFilterBridgeEncodeBHist H))
            (mooreSmithCauchyNetFilterBridgeDecodeBHist
              (mooreSmithCauchyNetFilterBridgeEncodeBHist C))
            (mooreSmithCauchyNetFilterBridgeDecodeBHist
              (mooreSmithCauchyNetFilterBridgeEncodeBHist P))
            (mooreSmithCauchyNetFilterBridgeDecodeBHist
              (mooreSmithCauchyNetFilterBridgeEncodeBHist N))) =
          some (MooreSmithCauchyNetFilterBridgeUp.mk D T F K U M S R Y E H C P N)
      rw [MooreSmithCauchyNetFilterBridgeTasteGate_decode_encode D,
        MooreSmithCauchyNetFilterBridgeTasteGate_decode_encode T,
        MooreSmithCauchyNetFilterBridgeTasteGate_decode_encode F,
        MooreSmithCauchyNetFilterBridgeTasteGate_decode_encode K,
        MooreSmithCauchyNetFilterBridgeTasteGate_decode_encode U,
        MooreSmithCauchyNetFilterBridgeTasteGate_decode_encode M,
        MooreSmithCauchyNetFilterBridgeTasteGate_decode_encode S,
        MooreSmithCauchyNetFilterBridgeTasteGate_decode_encode R,
        MooreSmithCauchyNetFilterBridgeTasteGate_decode_encode Y,
        MooreSmithCauchyNetFilterBridgeTasteGate_decode_encode E,
        MooreSmithCauchyNetFilterBridgeTasteGate_decode_encode H,
        MooreSmithCauchyNetFilterBridgeTasteGate_decode_encode C,
        MooreSmithCauchyNetFilterBridgeTasteGate_decode_encode P,
        MooreSmithCauchyNetFilterBridgeTasteGate_decode_encode N]

private theorem MooreSmithCauchyNetFilterBridgeTasteGate_toEventFlow_injective
    {x y : MooreSmithCauchyNetFilterBridgeUp} :
    mooreSmithCauchyNetFilterBridgeToEventFlow x =
      mooreSmithCauchyNetFilterBridgeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      mooreSmithCauchyNetFilterBridgeFromEventFlow
          (mooreSmithCauchyNetFilterBridgeToEventFlow x) =
        mooreSmithCauchyNetFilterBridgeFromEventFlow
          (mooreSmithCauchyNetFilterBridgeToEventFlow y) :=
    congrArg mooreSmithCauchyNetFilterBridgeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (MooreSmithCauchyNetFilterBridgeTasteGate_round_trip x).symm
      (Eq.trans hread (MooreSmithCauchyNetFilterBridgeTasteGate_round_trip y)))

private theorem MooreSmithCauchyNetFilterBridgeTasteGate_fields_faithful :
    ∀ x y : MooreSmithCauchyNetFilterBridgeUp,
      mooreSmithCauchyNetFilterBridgeFields x =
        mooreSmithCauchyNetFilterBridgeFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk D1 T1 F1 K1 U1 M1 S1 R1 Y1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk D2 T2 F2 K2 U2 M2 S2 R2 Y2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance mooreSmithCauchyNetFilterBridgeBHistCarrier :
    BHistCarrier MooreSmithCauchyNetFilterBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := mooreSmithCauchyNetFilterBridgeToEventFlow
  fromEventFlow := mooreSmithCauchyNetFilterBridgeFromEventFlow

instance mooreSmithCauchyNetFilterBridgeChapterTasteGate :
    ChapterTasteGate MooreSmithCauchyNetFilterBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := MooreSmithCauchyNetFilterBridgeTasteGate_round_trip
  layer_separation := by
    intro x y hxy heq
    exact hxy (MooreSmithCauchyNetFilterBridgeTasteGate_toEventFlow_injective heq)

instance mooreSmithCauchyNetFilterBridgeFieldFaithful :
    FieldFaithful MooreSmithCauchyNetFilterBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := mooreSmithCauchyNetFilterBridgeFields
  field_faithful := MooreSmithCauchyNetFilterBridgeTasteGate_fields_faithful

instance mooreSmithCauchyNetFilterBridgeNontrivial :
    Nontrivial MooreSmithCauchyNetFilterBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MooreSmithCauchyNetFilterBridgeUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MooreSmithCauchyNetFilterBridgeUp.mk (BHist.e1 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate MooreSmithCauchyNetFilterBridgeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  mooreSmithCauchyNetFilterBridgeChapterTasteGate

theorem MooreSmithCauchyNetFilterBridgeTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate MooreSmithCauchyNetFilterBridgeUp) ∧
      Nonempty (FieldFaithful MooreSmithCauchyNetFilterBridgeUp) ∧
        Nonempty (Nontrivial MooreSmithCauchyNetFilterBridgeUp) ∧
          (∀ h : BHist,
            mooreSmithCauchyNetFilterBridgeDecodeBHist
              (mooreSmithCauchyNetFilterBridgeEncodeBHist h) = h) ∧
            (∀ x : MooreSmithCauchyNetFilterBridgeUp,
              mooreSmithCauchyNetFilterBridgeFromEventFlow
                (mooreSmithCauchyNetFilterBridgeToEventFlow x) = some x) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨mooreSmithCauchyNetFilterBridgeChapterTasteGate⟩,
      ⟨mooreSmithCauchyNetFilterBridgeFieldFaithful⟩,
      ⟨mooreSmithCauchyNetFilterBridgeNontrivial⟩,
      MooreSmithCauchyNetFilterBridgeTasteGate_decode_encode,
      MooreSmithCauchyNetFilterBridgeTasteGate_round_trip⟩

end BEDC.Derived.MooreSmithCauchyNetFilterBridgeUp
