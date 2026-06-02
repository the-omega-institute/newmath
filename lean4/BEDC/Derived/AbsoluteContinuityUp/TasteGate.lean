import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AbsoluteContinuityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AbsoluteContinuityUp : Type where
  | mk (I Pi E Delta X D R V H C P N : BHist) : AbsoluteContinuityUp

def absoluteContinuityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: absoluteContinuityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: absoluteContinuityEncodeBHist h

def absoluteContinuityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (absoluteContinuityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (absoluteContinuityDecodeBHist tail)

private theorem AbsoluteContinuityTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      absoluteContinuityDecodeBHist (absoluteContinuityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def absoluteContinuityToEventFlow :
    AbsoluteContinuityUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | AbsoluteContinuityUp.mk I Pi E Delta X D R V H C P N =>
      [[BMark.b0, BMark.b1, BMark.b1],
        absoluteContinuityEncodeBHist I,
        absoluteContinuityEncodeBHist Pi,
        absoluteContinuityEncodeBHist E,
        absoluteContinuityEncodeBHist Delta,
        absoluteContinuityEncodeBHist X,
        absoluteContinuityEncodeBHist D,
        absoluteContinuityEncodeBHist R,
        absoluteContinuityEncodeBHist V,
        absoluteContinuityEncodeBHist H,
        absoluteContinuityEncodeBHist C,
        absoluteContinuityEncodeBHist P,
        absoluteContinuityEncodeBHist N]

def absoluteContinuityFromEventFlow : EventFlow → Option AbsoluteContinuityUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag :: rest0 =>
      match rest0 with
      | [] => none
      | I :: rest1 =>
          match rest1 with
          | [] => none
          | Pi :: rest2 =>
              match rest2 with
              | [] => none
              | E :: rest3 =>
                  match rest3 with
                  | [] => none
                  | Delta :: rest4 =>
                      match rest4 with
                      | [] => none
                      | X :: rest5 =>
                          match rest5 with
                          | [] => none
                          | D :: rest6 =>
                              match rest6 with
                              | [] => none
                              | R :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | V :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | H :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | C :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | P :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | N :: rest12 =>
                                                      match rest12 with
                                                      | [] =>
                                                          some
                                                            (AbsoluteContinuityUp.mk
                                                              (absoluteContinuityDecodeBHist I)
                                                              (absoluteContinuityDecodeBHist Pi)
                                                              (absoluteContinuityDecodeBHist E)
                                                              (absoluteContinuityDecodeBHist Delta)
                                                              (absoluteContinuityDecodeBHist X)
                                                              (absoluteContinuityDecodeBHist D)
                                                              (absoluteContinuityDecodeBHist R)
                                                              (absoluteContinuityDecodeBHist V)
                                                              (absoluteContinuityDecodeBHist H)
                                                              (absoluteContinuityDecodeBHist C)
                                                              (absoluteContinuityDecodeBHist P)
                                                              (absoluteContinuityDecodeBHist N))
                                                      | _ :: _ => none

private theorem AbsoluteContinuityTasteGate_single_carrier_alignment_round_trip
    (x : AbsoluteContinuityUp) :
    absoluteContinuityFromEventFlow (absoluteContinuityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk I Pi E Delta X D R V H C P N =>
      change
        some
            (AbsoluteContinuityUp.mk
              (absoluteContinuityDecodeBHist (absoluteContinuityEncodeBHist I))
              (absoluteContinuityDecodeBHist (absoluteContinuityEncodeBHist Pi))
              (absoluteContinuityDecodeBHist (absoluteContinuityEncodeBHist E))
              (absoluteContinuityDecodeBHist (absoluteContinuityEncodeBHist Delta))
              (absoluteContinuityDecodeBHist (absoluteContinuityEncodeBHist X))
              (absoluteContinuityDecodeBHist (absoluteContinuityEncodeBHist D))
              (absoluteContinuityDecodeBHist (absoluteContinuityEncodeBHist R))
              (absoluteContinuityDecodeBHist (absoluteContinuityEncodeBHist V))
              (absoluteContinuityDecodeBHist (absoluteContinuityEncodeBHist H))
              (absoluteContinuityDecodeBHist (absoluteContinuityEncodeBHist C))
              (absoluteContinuityDecodeBHist (absoluteContinuityEncodeBHist P))
              (absoluteContinuityDecodeBHist (absoluteContinuityEncodeBHist N))) =
          some (AbsoluteContinuityUp.mk I Pi E Delta X D R V H C P N)
      rw [AbsoluteContinuityTasteGate_single_carrier_alignment_decode I,
        AbsoluteContinuityTasteGate_single_carrier_alignment_decode Pi,
        AbsoluteContinuityTasteGate_single_carrier_alignment_decode E,
        AbsoluteContinuityTasteGate_single_carrier_alignment_decode Delta,
        AbsoluteContinuityTasteGate_single_carrier_alignment_decode X,
        AbsoluteContinuityTasteGate_single_carrier_alignment_decode D,
        AbsoluteContinuityTasteGate_single_carrier_alignment_decode R,
        AbsoluteContinuityTasteGate_single_carrier_alignment_decode V,
        AbsoluteContinuityTasteGate_single_carrier_alignment_decode H,
        AbsoluteContinuityTasteGate_single_carrier_alignment_decode C,
        AbsoluteContinuityTasteGate_single_carrier_alignment_decode P,
        AbsoluteContinuityTasteGate_single_carrier_alignment_decode N]

private theorem AbsoluteContinuityTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : AbsoluteContinuityUp} :
    absoluteContinuityToEventFlow x = absoluteContinuityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      absoluteContinuityFromEventFlow (absoluteContinuityToEventFlow x) =
        absoluteContinuityFromEventFlow (absoluteContinuityToEventFlow y) :=
    congrArg absoluteContinuityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (AbsoluteContinuityTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (AbsoluteContinuityTasteGate_single_carrier_alignment_round_trip y)))

instance absoluteContinuityBHistCarrier :
    BHistCarrier AbsoluteContinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := absoluteContinuityToEventFlow
  fromEventFlow := absoluteContinuityFromEventFlow

instance absoluteContinuityChapterTasteGate :
    ChapterTasteGate AbsoluteContinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change absoluteContinuityFromEventFlow (absoluteContinuityToEventFlow x) = some x
    exact AbsoluteContinuityTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (AbsoluteContinuityTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem AbsoluteContinuityTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier AbsoluteContinuityUp) ∧
      Nonempty (ChapterTasteGate AbsoluteContinuityUp) ∧
        (∀ h : BHist, absoluteContinuityDecodeBHist (absoluteContinuityEncodeBHist h) = h) ∧
          (∀ x : AbsoluteContinuityUp,
            absoluteContinuityFromEventFlow (absoluteContinuityToEventFlow x) = some x) ∧
            (∀ x y : AbsoluteContinuityUp,
              absoluteContinuityToEventFlow x = absoluteContinuityToEventFlow y → x = y) ∧
              absoluteContinuityEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨⟨absoluteContinuityBHistCarrier⟩,
      ⟨absoluteContinuityChapterTasteGate⟩,
      AbsoluteContinuityTasteGate_single_carrier_alignment_decode,
      AbsoluteContinuityTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        AbsoluteContinuityTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.AbsoluteContinuityUp
