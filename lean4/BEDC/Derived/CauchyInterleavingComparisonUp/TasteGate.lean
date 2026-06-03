import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyInterleavingComparisonUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyInterleavingComparisonUp : Type where
  | mk (S E O D T W Q H C P N : BHist) : CauchyInterleavingComparisonUp
  deriving DecidableEq

def cauchyInterleavingComparisonEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyInterleavingComparisonEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyInterleavingComparisonEncodeBHist h

def cauchyInterleavingComparisonDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyInterleavingComparisonDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyInterleavingComparisonDecodeBHist tail)

private theorem CauchyInterleavingComparisonTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      cauchyInterleavingComparisonDecodeBHist
        (cauchyInterleavingComparisonEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cauchyInterleavingComparisonFields :
    CauchyInterleavingComparisonUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyInterleavingComparisonUp.mk S E O D T W Q H C P N =>
      [S, E, O, D, T, W, Q, H, C, P, N]

def cauchyInterleavingComparisonToEventFlow :
    CauchyInterleavingComparisonUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (cauchyInterleavingComparisonFields x).map
        cauchyInterleavingComparisonEncodeBHist

def cauchyInterleavingComparisonFromEventFlow :
    EventFlow -> Option CauchyInterleavingComparisonUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | S :: rest0 =>
      match rest0 with
      | [] => none
      | E :: rest1 =>
          match rest1 with
          | [] => none
          | O :: rest2 =>
              match rest2 with
              | [] => none
              | D :: rest3 =>
                  match rest3 with
                  | [] => none
                  | T :: rest4 =>
                      match rest4 with
                      | [] => none
                      | W :: rest5 =>
                          match rest5 with
                          | [] => none
                          | Q :: rest6 =>
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
                                                    (CauchyInterleavingComparisonUp.mk
                                                      (cauchyInterleavingComparisonDecodeBHist S)
                                                      (cauchyInterleavingComparisonDecodeBHist E)
                                                      (cauchyInterleavingComparisonDecodeBHist O)
                                                      (cauchyInterleavingComparisonDecodeBHist D)
                                                      (cauchyInterleavingComparisonDecodeBHist T)
                                                      (cauchyInterleavingComparisonDecodeBHist W)
                                                      (cauchyInterleavingComparisonDecodeBHist Q)
                                                      (cauchyInterleavingComparisonDecodeBHist H)
                                                      (cauchyInterleavingComparisonDecodeBHist C)
                                                      (cauchyInterleavingComparisonDecodeBHist P)
                                                      (cauchyInterleavingComparisonDecodeBHist N))
                                              | _ :: _ => none

private theorem CauchyInterleavingComparisonTasteGate_single_carrier_alignment_round_trip :
    forall x : CauchyInterleavingComparisonUp,
      cauchyInterleavingComparisonFromEventFlow
          (cauchyInterleavingComparisonToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S E O D T W Q H C P N =>
      change
        some
          (CauchyInterleavingComparisonUp.mk
            (cauchyInterleavingComparisonDecodeBHist
              (cauchyInterleavingComparisonEncodeBHist S))
            (cauchyInterleavingComparisonDecodeBHist
              (cauchyInterleavingComparisonEncodeBHist E))
            (cauchyInterleavingComparisonDecodeBHist
              (cauchyInterleavingComparisonEncodeBHist O))
            (cauchyInterleavingComparisonDecodeBHist
              (cauchyInterleavingComparisonEncodeBHist D))
            (cauchyInterleavingComparisonDecodeBHist
              (cauchyInterleavingComparisonEncodeBHist T))
            (cauchyInterleavingComparisonDecodeBHist
              (cauchyInterleavingComparisonEncodeBHist W))
            (cauchyInterleavingComparisonDecodeBHist
              (cauchyInterleavingComparisonEncodeBHist Q))
            (cauchyInterleavingComparisonDecodeBHist
              (cauchyInterleavingComparisonEncodeBHist H))
            (cauchyInterleavingComparisonDecodeBHist
              (cauchyInterleavingComparisonEncodeBHist C))
            (cauchyInterleavingComparisonDecodeBHist
              (cauchyInterleavingComparisonEncodeBHist P))
            (cauchyInterleavingComparisonDecodeBHist
              (cauchyInterleavingComparisonEncodeBHist N))) =
          some (CauchyInterleavingComparisonUp.mk S E O D T W Q H C P N)
      rw [CauchyInterleavingComparisonTasteGate_single_carrier_alignment_decode_encode S,
        CauchyInterleavingComparisonTasteGate_single_carrier_alignment_decode_encode E,
        CauchyInterleavingComparisonTasteGate_single_carrier_alignment_decode_encode O,
        CauchyInterleavingComparisonTasteGate_single_carrier_alignment_decode_encode D,
        CauchyInterleavingComparisonTasteGate_single_carrier_alignment_decode_encode T,
        CauchyInterleavingComparisonTasteGate_single_carrier_alignment_decode_encode W,
        CauchyInterleavingComparisonTasteGate_single_carrier_alignment_decode_encode Q,
        CauchyInterleavingComparisonTasteGate_single_carrier_alignment_decode_encode H,
        CauchyInterleavingComparisonTasteGate_single_carrier_alignment_decode_encode C,
        CauchyInterleavingComparisonTasteGate_single_carrier_alignment_decode_encode P,
        CauchyInterleavingComparisonTasteGate_single_carrier_alignment_decode_encode N]

private theorem CauchyInterleavingComparisonTasteGate_single_carrier_alignment_injective
    {x y : CauchyInterleavingComparisonUp} :
    cauchyInterleavingComparisonToEventFlow x =
      cauchyInterleavingComparisonToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyInterleavingComparisonFromEventFlow
          (cauchyInterleavingComparisonToEventFlow x) =
        cauchyInterleavingComparisonFromEventFlow
          (cauchyInterleavingComparisonToEventFlow y) :=
    congrArg cauchyInterleavingComparisonFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyInterleavingComparisonTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyInterleavingComparisonTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyInterleavingComparisonBHistCarrier :
    BHistCarrier CauchyInterleavingComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyInterleavingComparisonToEventFlow
  fromEventFlow := cauchyInterleavingComparisonFromEventFlow

instance cauchyInterleavingComparisonChapterTasteGate :
    ChapterTasteGate CauchyInterleavingComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyInterleavingComparisonFromEventFlow
          (cauchyInterleavingComparisonToEventFlow x) =
        some x
    exact CauchyInterleavingComparisonTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchyInterleavingComparisonTasteGate_single_carrier_alignment_injective heq)

def taste_gate : ChapterTasteGate CauchyInterleavingComparisonUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyInterleavingComparisonChapterTasteGate

theorem CauchyInterleavingComparisonTasteGate_single_carrier_alignment :
    (forall h : BHist,
      cauchyInterleavingComparisonDecodeBHist
        (cauchyInterleavingComparisonEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier CauchyInterleavingComparisonUp) ∧
        Nonempty (ChapterTasteGate CauchyInterleavingComparisonUp) ∧
          cauchyInterleavingComparisonEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact CauchyInterleavingComparisonTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact ⟨cauchyInterleavingComparisonBHistCarrier⟩
    · constructor
      · exact ⟨cauchyInterleavingComparisonChapterTasteGate⟩
      · rfl

end BEDC.Derived.CauchyInterleavingComparisonUp
