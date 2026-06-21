import BEDC.Derived.StoneRepresentationBooleanAlgebraUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def stoneRepresentationBooleanAlgebraEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: stoneRepresentationBooleanAlgebraEncodeBHist h
  | BHist.e1 h => BMark.b1 :: stoneRepresentationBooleanAlgebraEncodeBHist h

def stoneRepresentationBooleanAlgebraDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (stoneRepresentationBooleanAlgebraDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (stoneRepresentationBooleanAlgebraDecodeBHist tail)

private theorem StoneRepresentationBooleanAlgebraTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      stoneRepresentationBooleanAlgebraDecodeBHist
        (stoneRepresentationBooleanAlgebraEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def stoneRepresentationBooleanAlgebraFields :
    StoneRepresentationBooleanAlgebraUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | StoneRepresentationBooleanAlgebraUp.mk B U T L M H C P N =>
      [B, U, T, L, M, H, C, P, N]

def stoneRepresentationBooleanAlgebraToEventFlow :
    StoneRepresentationBooleanAlgebraUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (stoneRepresentationBooleanAlgebraFields x).map
        stoneRepresentationBooleanAlgebraEncodeBHist

def stoneRepresentationBooleanAlgebraFromEventFlow :
    EventFlow → Option StoneRepresentationBooleanAlgebraUp
  -- BEDC touchpoint anchor: BHist BMark
  | B :: restB =>
      match restB with
      | U :: restU =>
          match restU with
          | T :: restT =>
              match restT with
              | L :: restL =>
                  match restL with
                  | M :: restM =>
                      match restM with
                      | H :: restH =>
                          match restH with
                          | C :: restC =>
                              match restC with
                              | P :: restP =>
                                  match restP with
                                  | N :: restN =>
                                      match restN with
                                      | [] =>
                                          some
                                            (StoneRepresentationBooleanAlgebraUp.mk
                                              (stoneRepresentationBooleanAlgebraDecodeBHist B)
                                              (stoneRepresentationBooleanAlgebraDecodeBHist U)
                                              (stoneRepresentationBooleanAlgebraDecodeBHist T)
                                              (stoneRepresentationBooleanAlgebraDecodeBHist L)
                                              (stoneRepresentationBooleanAlgebraDecodeBHist M)
                                              (stoneRepresentationBooleanAlgebraDecodeBHist H)
                                              (stoneRepresentationBooleanAlgebraDecodeBHist C)
                                              (stoneRepresentationBooleanAlgebraDecodeBHist P)
                                              (stoneRepresentationBooleanAlgebraDecodeBHist N))
                                      | _ :: _ => none
                                  | [] => none
                              | [] => none
                          | [] => none
                      | [] => none
                  | [] => none
              | [] => none
          | [] => none
      | [] => none
  | [] => none

private theorem StoneRepresentationBooleanAlgebraTasteGate_single_carrier_alignment_round_trip :
    ∀ x : StoneRepresentationBooleanAlgebraUp,
      stoneRepresentationBooleanAlgebraFromEventFlow
        (stoneRepresentationBooleanAlgebraToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B U T L M H C P N =>
      change
        some
          (BEDC.Derived.StoneRepresentationBooleanAlgebraUp.mk
            (stoneRepresentationBooleanAlgebraDecodeBHist
              (stoneRepresentationBooleanAlgebraEncodeBHist B))
            (stoneRepresentationBooleanAlgebraDecodeBHist
              (stoneRepresentationBooleanAlgebraEncodeBHist U))
            (stoneRepresentationBooleanAlgebraDecodeBHist
              (stoneRepresentationBooleanAlgebraEncodeBHist T))
            (stoneRepresentationBooleanAlgebraDecodeBHist
              (stoneRepresentationBooleanAlgebraEncodeBHist L))
            (stoneRepresentationBooleanAlgebraDecodeBHist
              (stoneRepresentationBooleanAlgebraEncodeBHist M))
            (stoneRepresentationBooleanAlgebraDecodeBHist
              (stoneRepresentationBooleanAlgebraEncodeBHist H))
            (stoneRepresentationBooleanAlgebraDecodeBHist
              (stoneRepresentationBooleanAlgebraEncodeBHist C))
            (stoneRepresentationBooleanAlgebraDecodeBHist
              (stoneRepresentationBooleanAlgebraEncodeBHist P))
            (stoneRepresentationBooleanAlgebraDecodeBHist
              (stoneRepresentationBooleanAlgebraEncodeBHist N))) =
        some (StoneRepresentationBooleanAlgebraUp.mk B U T L M H C P N)
      rw [StoneRepresentationBooleanAlgebraTasteGate_single_carrier_alignment_decode_encode B,
        StoneRepresentationBooleanAlgebraTasteGate_single_carrier_alignment_decode_encode U,
        StoneRepresentationBooleanAlgebraTasteGate_single_carrier_alignment_decode_encode T,
        StoneRepresentationBooleanAlgebraTasteGate_single_carrier_alignment_decode_encode L,
        StoneRepresentationBooleanAlgebraTasteGate_single_carrier_alignment_decode_encode M,
        StoneRepresentationBooleanAlgebraTasteGate_single_carrier_alignment_decode_encode H,
        StoneRepresentationBooleanAlgebraTasteGate_single_carrier_alignment_decode_encode C,
        StoneRepresentationBooleanAlgebraTasteGate_single_carrier_alignment_decode_encode P,
        StoneRepresentationBooleanAlgebraTasteGate_single_carrier_alignment_decode_encode N]

private theorem StoneRepresentationBooleanAlgebraTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : StoneRepresentationBooleanAlgebraUp} :
    stoneRepresentationBooleanAlgebraToEventFlow x =
      stoneRepresentationBooleanAlgebraToEventFlow y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      stoneRepresentationBooleanAlgebraFromEventFlow
          (stoneRepresentationBooleanAlgebraToEventFlow x) =
        stoneRepresentationBooleanAlgebraFromEventFlow
          (stoneRepresentationBooleanAlgebraToEventFlow y) :=
    congrArg stoneRepresentationBooleanAlgebraFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (StoneRepresentationBooleanAlgebraTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (StoneRepresentationBooleanAlgebraTasteGate_single_carrier_alignment_round_trip y)))

instance stoneRepresentationBooleanAlgebraBHistCarrier :
    BHistCarrier StoneRepresentationBooleanAlgebraUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := stoneRepresentationBooleanAlgebraToEventFlow
  fromEventFlow := stoneRepresentationBooleanAlgebraFromEventFlow

instance stoneRepresentationBooleanAlgebraChapterTasteGate :
    ChapterTasteGate StoneRepresentationBooleanAlgebraUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      stoneRepresentationBooleanAlgebraFromEventFlow
        (stoneRepresentationBooleanAlgebraToEventFlow x) = some x
    exact StoneRepresentationBooleanAlgebraTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (StoneRepresentationBooleanAlgebraTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

def taste_gate :
    ChapterTasteGate StoneRepresentationBooleanAlgebraUp :=
  -- BEDC touchpoint anchor: BHist BMark
  stoneRepresentationBooleanAlgebraChapterTasteGate

theorem StoneRepresentationBooleanAlgebraUp.StoneRepresentationBooleanAlgebraTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      stoneRepresentationBooleanAlgebraDecodeBHist
        (stoneRepresentationBooleanAlgebraEncodeBHist h) = h) ∧
      (∀ x : StoneRepresentationBooleanAlgebraUp,
        stoneRepresentationBooleanAlgebraFromEventFlow
          (stoneRepresentationBooleanAlgebraToEventFlow x) = some x) ∧
      (∀ x y : StoneRepresentationBooleanAlgebraUp,
        stoneRepresentationBooleanAlgebraToEventFlow x =
          stoneRepresentationBooleanAlgebraToEventFlow y → x = y) ∧
      stoneRepresentationBooleanAlgebraEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨StoneRepresentationBooleanAlgebraTasteGate_single_carrier_alignment_decode_encode,
      StoneRepresentationBooleanAlgebraTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        StoneRepresentationBooleanAlgebraTasteGate_single_carrier_alignment_toEventFlow_injective
          heq),
      rfl⟩

end BEDC.Derived
