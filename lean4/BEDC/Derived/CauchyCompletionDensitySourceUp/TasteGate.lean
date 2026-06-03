import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCompletionDensitySourceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCompletionDensitySourceUp : Type where
  | mk (U M J R W Q S H C P N : BHist) : CauchyCompletionDensitySourceUp
  deriving DecidableEq

def cauchyCompletionDensitySourceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCompletionDensitySourceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCompletionDensitySourceEncodeBHist h

def cauchyCompletionDensitySourceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCompletionDensitySourceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCompletionDensitySourceDecodeBHist tail)

private theorem CauchyCompletionDensitySourceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      cauchyCompletionDensitySourceDecodeBHist
        (cauchyCompletionDensitySourceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cauchyCompletionDensitySourceToEventFlow :
    CauchyCompletionDensitySourceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCompletionDensitySourceUp.mk U M J R W Q S H C P N =>
      [cauchyCompletionDensitySourceEncodeBHist U,
        cauchyCompletionDensitySourceEncodeBHist M,
        cauchyCompletionDensitySourceEncodeBHist J,
        cauchyCompletionDensitySourceEncodeBHist R,
        cauchyCompletionDensitySourceEncodeBHist W,
        cauchyCompletionDensitySourceEncodeBHist Q,
        cauchyCompletionDensitySourceEncodeBHist S,
        cauchyCompletionDensitySourceEncodeBHist H,
        cauchyCompletionDensitySourceEncodeBHist C,
        cauchyCompletionDensitySourceEncodeBHist P,
        cauchyCompletionDensitySourceEncodeBHist N]

def cauchyCompletionDensitySourceFromEventFlow :
    EventFlow → Option CauchyCompletionDensitySourceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | U :: rest0 =>
      match rest0 with
      | [] => none
      | M :: rest1 =>
          match rest1 with
          | [] => none
          | J :: rest2 =>
              match rest2 with
              | [] => none
              | R :: rest3 =>
                  match rest3 with
                  | [] => none
                  | W :: rest4 =>
                      match rest4 with
                      | [] => none
                      | Q :: rest5 =>
                          match rest5 with
                          | [] => none
                          | S :: rest6 =>
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
                                                    (CauchyCompletionDensitySourceUp.mk
                                                      (cauchyCompletionDensitySourceDecodeBHist U)
                                                      (cauchyCompletionDensitySourceDecodeBHist M)
                                                      (cauchyCompletionDensitySourceDecodeBHist J)
                                                      (cauchyCompletionDensitySourceDecodeBHist R)
                                                      (cauchyCompletionDensitySourceDecodeBHist W)
                                                      (cauchyCompletionDensitySourceDecodeBHist Q)
                                                      (cauchyCompletionDensitySourceDecodeBHist S)
                                                      (cauchyCompletionDensitySourceDecodeBHist H)
                                                      (cauchyCompletionDensitySourceDecodeBHist C)
                                                      (cauchyCompletionDensitySourceDecodeBHist P)
                                                      (cauchyCompletionDensitySourceDecodeBHist N))
                                              | _ :: _ => none

private theorem CauchyCompletionDensitySourceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyCompletionDensitySourceUp,
      cauchyCompletionDensitySourceFromEventFlow
        (cauchyCompletionDensitySourceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk U M J R W Q S H C P N =>
      change
        some
          (CauchyCompletionDensitySourceUp.mk
            (cauchyCompletionDensitySourceDecodeBHist
              (cauchyCompletionDensitySourceEncodeBHist U))
            (cauchyCompletionDensitySourceDecodeBHist
              (cauchyCompletionDensitySourceEncodeBHist M))
            (cauchyCompletionDensitySourceDecodeBHist
              (cauchyCompletionDensitySourceEncodeBHist J))
            (cauchyCompletionDensitySourceDecodeBHist
              (cauchyCompletionDensitySourceEncodeBHist R))
            (cauchyCompletionDensitySourceDecodeBHist
              (cauchyCompletionDensitySourceEncodeBHist W))
            (cauchyCompletionDensitySourceDecodeBHist
              (cauchyCompletionDensitySourceEncodeBHist Q))
            (cauchyCompletionDensitySourceDecodeBHist
              (cauchyCompletionDensitySourceEncodeBHist S))
            (cauchyCompletionDensitySourceDecodeBHist
              (cauchyCompletionDensitySourceEncodeBHist H))
            (cauchyCompletionDensitySourceDecodeBHist
              (cauchyCompletionDensitySourceEncodeBHist C))
            (cauchyCompletionDensitySourceDecodeBHist
              (cauchyCompletionDensitySourceEncodeBHist P))
            (cauchyCompletionDensitySourceDecodeBHist
              (cauchyCompletionDensitySourceEncodeBHist N))) =
          some (CauchyCompletionDensitySourceUp.mk U M J R W Q S H C P N)
      rw [CauchyCompletionDensitySourceTasteGate_single_carrier_alignment_decode_encode U,
        CauchyCompletionDensitySourceTasteGate_single_carrier_alignment_decode_encode M,
        CauchyCompletionDensitySourceTasteGate_single_carrier_alignment_decode_encode J,
        CauchyCompletionDensitySourceTasteGate_single_carrier_alignment_decode_encode R,
        CauchyCompletionDensitySourceTasteGate_single_carrier_alignment_decode_encode W,
        CauchyCompletionDensitySourceTasteGate_single_carrier_alignment_decode_encode Q,
        CauchyCompletionDensitySourceTasteGate_single_carrier_alignment_decode_encode S,
        CauchyCompletionDensitySourceTasteGate_single_carrier_alignment_decode_encode H,
        CauchyCompletionDensitySourceTasteGate_single_carrier_alignment_decode_encode C,
        CauchyCompletionDensitySourceTasteGate_single_carrier_alignment_decode_encode P,
        CauchyCompletionDensitySourceTasteGate_single_carrier_alignment_decode_encode N]

private theorem CauchyCompletionDensitySourceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyCompletionDensitySourceUp} :
    cauchyCompletionDensitySourceToEventFlow x =
      cauchyCompletionDensitySourceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyCompletionDensitySourceFromEventFlow
          (cauchyCompletionDensitySourceToEventFlow x) =
        cauchyCompletionDensitySourceFromEventFlow
          (cauchyCompletionDensitySourceToEventFlow y) :=
    congrArg cauchyCompletionDensitySourceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyCompletionDensitySourceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyCompletionDensitySourceTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyCompletionDensitySourceBHistCarrier :
    BHistCarrier CauchyCompletionDensitySourceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCompletionDensitySourceToEventFlow
  fromEventFlow := cauchyCompletionDensitySourceFromEventFlow

instance cauchyCompletionDensitySourceChapterTasteGate :
    ChapterTasteGate CauchyCompletionDensitySourceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyCompletionDensitySourceFromEventFlow
        (cauchyCompletionDensitySourceToEventFlow x) = some x
    exact CauchyCompletionDensitySourceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchyCompletionDensitySourceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate CauchyCompletionDensitySourceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyCompletionDensitySourceChapterTasteGate

theorem CauchyCompletionDensitySourceTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchyCompletionDensitySourceDecodeBHist
      (cauchyCompletionDensitySourceEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier CauchyCompletionDensitySourceUp) ∧
        Nonempty (ChapterTasteGate CauchyCompletionDensitySourceUp) ∧
          cauchyCompletionDensitySourceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CauchyCompletionDensitySourceTasteGate_single_carrier_alignment_decode_encode,
      ⟨cauchyCompletionDensitySourceBHistCarrier⟩,
      ⟨cauchyCompletionDensitySourceChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.CauchyCompletionDensitySourceUp
