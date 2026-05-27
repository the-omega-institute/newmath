import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SqueezeTheoremUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SqueezeTheoremUp : Type where
  | mk (L M U W D Q E H C P N : BHist) : SqueezeTheoremUp

def squeezeTheoremEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: squeezeTheoremEncodeBHist h
  | BHist.e1 h => BMark.b1 :: squeezeTheoremEncodeBHist h

def squeezeTheoremDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (squeezeTheoremDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (squeezeTheoremDecodeBHist tail)

private theorem SqueezeTheoremTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist, squeezeTheoremDecodeBHist (squeezeTheoremEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def squeezeTheoremFields : SqueezeTheoremUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SqueezeTheoremUp.mk L M U W D Q E H C P N => [L, M, U, W, D, Q, E, H, C, P, N]

def squeezeTheoremToEventFlow : SqueezeTheoremUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (squeezeTheoremFields x).map squeezeTheoremEncodeBHist

def squeezeTheoremFromEventFlow : EventFlow -> Option SqueezeTheoremUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | L :: rest0 =>
      match rest0 with
      | [] => none
      | M :: rest1 =>
          match rest1 with
          | [] => none
          | U :: rest2 =>
              match rest2 with
              | [] => none
              | W :: rest3 =>
                  match rest3 with
                  | [] => none
                  | D :: rest4 =>
                      match rest4 with
                      | [] => none
                      | Q :: rest5 =>
                          match rest5 with
                          | [] => none
                          | E :: rest6 =>
                              match rest6 with
                              | [] => none
                              | H :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | C :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | P :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | N :: rest10 =>
                                              match rest10 with
                                              | [] =>
                                                  some
                                                    (SqueezeTheoremUp.mk
                                                      (squeezeTheoremDecodeBHist L)
                                                      (squeezeTheoremDecodeBHist M)
                                                      (squeezeTheoremDecodeBHist U)
                                                      (squeezeTheoremDecodeBHist W)
                                                      (squeezeTheoremDecodeBHist D)
                                                      (squeezeTheoremDecodeBHist Q)
                                                      (squeezeTheoremDecodeBHist E)
                                                      (squeezeTheoremDecodeBHist H)
                                                      (squeezeTheoremDecodeBHist C)
                                                      (squeezeTheoremDecodeBHist P)
                                                      (squeezeTheoremDecodeBHist N))
                                              | _ :: _ => none

private theorem SqueezeTheoremTasteGate_single_carrier_alignment_round_trip :
    forall x : SqueezeTheoremUp,
      squeezeTheoremFromEventFlow (squeezeTheoremToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L M U W D Q E H C P N =>
      change
        some
          (SqueezeTheoremUp.mk
            (squeezeTheoremDecodeBHist (squeezeTheoremEncodeBHist L))
            (squeezeTheoremDecodeBHist (squeezeTheoremEncodeBHist M))
            (squeezeTheoremDecodeBHist (squeezeTheoremEncodeBHist U))
            (squeezeTheoremDecodeBHist (squeezeTheoremEncodeBHist W))
            (squeezeTheoremDecodeBHist (squeezeTheoremEncodeBHist D))
            (squeezeTheoremDecodeBHist (squeezeTheoremEncodeBHist Q))
            (squeezeTheoremDecodeBHist (squeezeTheoremEncodeBHist E))
            (squeezeTheoremDecodeBHist (squeezeTheoremEncodeBHist H))
            (squeezeTheoremDecodeBHist (squeezeTheoremEncodeBHist C))
            (squeezeTheoremDecodeBHist (squeezeTheoremEncodeBHist P))
            (squeezeTheoremDecodeBHist (squeezeTheoremEncodeBHist N))) =
          some (SqueezeTheoremUp.mk L M U W D Q E H C P N)
      rw [SqueezeTheoremTasteGate_single_carrier_alignment_decode_encode L,
        SqueezeTheoremTasteGate_single_carrier_alignment_decode_encode M,
        SqueezeTheoremTasteGate_single_carrier_alignment_decode_encode U,
        SqueezeTheoremTasteGate_single_carrier_alignment_decode_encode W,
        SqueezeTheoremTasteGate_single_carrier_alignment_decode_encode D,
        SqueezeTheoremTasteGate_single_carrier_alignment_decode_encode Q,
        SqueezeTheoremTasteGate_single_carrier_alignment_decode_encode E,
        SqueezeTheoremTasteGate_single_carrier_alignment_decode_encode H,
        SqueezeTheoremTasteGate_single_carrier_alignment_decode_encode C,
        SqueezeTheoremTasteGate_single_carrier_alignment_decode_encode P,
        SqueezeTheoremTasteGate_single_carrier_alignment_decode_encode N]

private theorem SqueezeTheoremTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : SqueezeTheoremUp} :
    squeezeTheoremToEventFlow x = squeezeTheoremToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      squeezeTheoremFromEventFlow (squeezeTheoremToEventFlow x) =
        squeezeTheoremFromEventFlow (squeezeTheoremToEventFlow y) :=
    congrArg squeezeTheoremFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (SqueezeTheoremTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (SqueezeTheoremTasteGate_single_carrier_alignment_round_trip y)))

private theorem SqueezeTheoremTasteGate_single_carrier_alignment_fields_faithful :
    forall x y : SqueezeTheoremUp, squeezeTheoremFields x = squeezeTheoremFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk L1 M1 U1 W1 D1 Q1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk L2 M2 U2 W2 D2 Q2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance squeezeTheoremBHistCarrier : BHistCarrier SqueezeTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := squeezeTheoremToEventFlow
  fromEventFlow := squeezeTheoremFromEventFlow

instance squeezeTheoremChapterTasteGate : ChapterTasteGate SqueezeTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change squeezeTheoremFromEventFlow (squeezeTheoremToEventFlow x) = some x
    exact SqueezeTheoremTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (SqueezeTheoremTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance squeezeTheoremFieldFaithful : FieldFaithful SqueezeTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := squeezeTheoremFields
  field_faithful := SqueezeTheoremTasteGate_single_carrier_alignment_fields_faithful

def taste_gate : ChapterTasteGate SqueezeTheoremUp :=
  -- BEDC touchpoint anchor: BHist BMark
  squeezeTheoremChapterTasteGate

theorem SqueezeTheoremTasteGate_single_carrier_alignment :
    (forall h : BHist, squeezeTheoremDecodeBHist (squeezeTheoremEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier SqueezeTheoremUp) ∧
        Nonempty (ChapterTasteGate SqueezeTheoremUp) ∧
          Nonempty (FieldFaithful SqueezeTheoremUp) ∧
            squeezeTheoremEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  exact
    ⟨SqueezeTheoremTasteGate_single_carrier_alignment_decode_encode,
      ⟨squeezeTheoremBHistCarrier⟩,
      ⟨squeezeTheoremChapterTasteGate⟩,
      ⟨squeezeTheoremFieldFaithful⟩,
      rfl⟩

end BEDC.Derived.SqueezeTheoremUp
