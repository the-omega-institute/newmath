import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyNetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyNetUp : Type where
  | mk (D S R W T L H C P N : BHist) : CauchyNetUp

def cauchyNetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyNetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyNetEncodeBHist h

def cauchyNetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyNetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyNetDecodeBHist tail)

private theorem cauchyNet_decode_encode_bhist :
    ∀ h : BHist,
      cauchyNetDecodeBHist (cauchyNetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cauchyNetFields :
    CauchyNetUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyNetUp.mk D S R W T L H C P N => [D, S, R, W, T, L, H, C, P, N]

def cauchyNetToEventFlow :
    CauchyNetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyNetUp.mk D S R W T L H C P N =>
      [cauchyNetEncodeBHist D,
        cauchyNetEncodeBHist S,
        cauchyNetEncodeBHist R,
        cauchyNetEncodeBHist W,
        cauchyNetEncodeBHist T,
        cauchyNetEncodeBHist L,
        cauchyNetEncodeBHist H,
        cauchyNetEncodeBHist C,
        cauchyNetEncodeBHist P,
        cauchyNetEncodeBHist N]

def cauchyNetFromEventFlow :
    EventFlow → Option CauchyNetUp
  -- BEDC touchpoint anchor: BHist BMark
  | D :: S :: R :: W :: T :: L :: H :: C :: P :: N :: [] =>
      some
        (CauchyNetUp.mk
          (cauchyNetDecodeBHist D)
          (cauchyNetDecodeBHist S)
          (cauchyNetDecodeBHist R)
          (cauchyNetDecodeBHist W)
          (cauchyNetDecodeBHist T)
          (cauchyNetDecodeBHist L)
          (cauchyNetDecodeBHist H)
          (cauchyNetDecodeBHist C)
          (cauchyNetDecodeBHist P)
          (cauchyNetDecodeBHist N))
  | _ => none

private theorem cauchyNet_round_trip :
    ∀ x : CauchyNetUp,
      cauchyNetFromEventFlow (cauchyNetToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D S R W T L H C P N =>
      change
        some
            (CauchyNetUp.mk
              (cauchyNetDecodeBHist (cauchyNetEncodeBHist D))
              (cauchyNetDecodeBHist (cauchyNetEncodeBHist S))
              (cauchyNetDecodeBHist (cauchyNetEncodeBHist R))
              (cauchyNetDecodeBHist (cauchyNetEncodeBHist W))
              (cauchyNetDecodeBHist (cauchyNetEncodeBHist T))
              (cauchyNetDecodeBHist (cauchyNetEncodeBHist L))
              (cauchyNetDecodeBHist (cauchyNetEncodeBHist H))
              (cauchyNetDecodeBHist (cauchyNetEncodeBHist C))
              (cauchyNetDecodeBHist (cauchyNetEncodeBHist P))
              (cauchyNetDecodeBHist (cauchyNetEncodeBHist N))) =
          some (CauchyNetUp.mk D S R W T L H C P N)
      rw [cauchyNet_decode_encode_bhist D,
        cauchyNet_decode_encode_bhist S,
        cauchyNet_decode_encode_bhist R,
        cauchyNet_decode_encode_bhist W,
        cauchyNet_decode_encode_bhist T,
        cauchyNet_decode_encode_bhist L,
        cauchyNet_decode_encode_bhist H,
        cauchyNet_decode_encode_bhist C,
        cauchyNet_decode_encode_bhist P,
        cauchyNet_decode_encode_bhist N]

private theorem cauchyNetToEventFlow_injective
    {x y : CauchyNetUp}
    (h : cauchyNetToEventFlow x = cauchyNetToEventFlow y) :
    x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  have hread :
      cauchyNetFromEventFlow (cauchyNetToEventFlow x) =
        cauchyNetFromEventFlow (cauchyNetToEventFlow y) :=
    congrArg cauchyNetFromEventFlow h
  exact Option.some.inj
    (Eq.trans (cauchyNet_round_trip x).symm
      (Eq.trans hread (cauchyNet_round_trip y)))

private theorem cauchyNet_fields_faithful :
    ∀ x y : CauchyNetUp, cauchyNetFields x = cauchyNetFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk D S R W T L H C P N =>
      cases y with
      | mk D' S' R' W' T' L' H' C' P' N' =>
          cases hfields
          rfl

instance cauchyNetBHistCarrier : BHistCarrier CauchyNetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyNetToEventFlow
  fromEventFlow := cauchyNetFromEventFlow

instance cauchyNetChapterTasteGate : ChapterTasteGate CauchyNetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyNetFromEventFlow (cauchyNetToEventFlow x) = some x
    exact cauchyNet_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyNetToEventFlow_injective heq)

def taste_gate : ChapterTasteGate CauchyNetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyNetChapterTasteGate

theorem CauchyNetTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchyNetDecodeBHist (cauchyNetEncodeBHist h) = h) ∧
      (∀ x y : CauchyNetUp, cauchyNetFields x = cauchyNetFields y → x = y) ∧
          cauchyNetFields
              (CauchyNetUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty) =
            [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
              BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] ∧
            cauchyNetEncodeBHist BHist.Empty = ([] : RawEvent) ∧
              cauchyNetEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] ∧
                cauchyNetEncodeBHist (BHist.e1 BHist.Empty) = [BMark.b1] := by
  -- BEDC touchpoint anchor: BHist BMark
  exact ⟨cauchyNet_decode_encode_bhist,
    cauchyNet_fields_faithful,
    rfl, rfl, rfl, rfl⟩

end BEDC.Derived.CauchyNetUp
