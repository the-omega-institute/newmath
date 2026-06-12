import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCriterionForSeriesUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCriterionForSeriesUp : Type where
  | mk (A L W D R E T H C P N : BHist) : CauchyCriterionForSeriesUp
  deriving DecidableEq

def cauchyCriterionForSeriesEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCriterionForSeriesEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCriterionForSeriesEncodeBHist h

def cauchyCriterionForSeriesDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCriterionForSeriesDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCriterionForSeriesDecodeBHist tail)

private theorem CauchyCriterionForSeriesTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      cauchyCriterionForSeriesDecodeBHist (cauchyCriterionForSeriesEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyCriterionForSeriesToEventFlow : CauchyCriterionForSeriesUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCriterionForSeriesUp.mk A L W D R E T H C P N =>
      [cauchyCriterionForSeriesEncodeBHist A,
        cauchyCriterionForSeriesEncodeBHist L,
        cauchyCriterionForSeriesEncodeBHist W,
        cauchyCriterionForSeriesEncodeBHist D,
        cauchyCriterionForSeriesEncodeBHist R,
        cauchyCriterionForSeriesEncodeBHist E,
        cauchyCriterionForSeriesEncodeBHist T,
        cauchyCriterionForSeriesEncodeBHist H,
        cauchyCriterionForSeriesEncodeBHist C,
        cauchyCriterionForSeriesEncodeBHist P,
        cauchyCriterionForSeriesEncodeBHist N]

def cauchyCriterionForSeriesFromEventFlow : EventFlow → Option CauchyCriterionForSeriesUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | A :: rest0 =>
      match rest0 with
      | [] => none
      | L :: rest1 =>
          match rest1 with
          | [] => none
          | W :: rest2 =>
              match rest2 with
              | [] => none
              | D :: rest3 =>
                  match rest3 with
                  | [] => none
                  | R :: rest4 =>
                      match rest4 with
                      | [] => none
                      | E :: rest5 =>
                          match rest5 with
                          | [] => none
                          | T :: rest6 =>
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
                                                    (CauchyCriterionForSeriesUp.mk
                                                      (cauchyCriterionForSeriesDecodeBHist A)
                                                      (cauchyCriterionForSeriesDecodeBHist L)
                                                      (cauchyCriterionForSeriesDecodeBHist W)
                                                      (cauchyCriterionForSeriesDecodeBHist D)
                                                      (cauchyCriterionForSeriesDecodeBHist R)
                                                      (cauchyCriterionForSeriesDecodeBHist E)
                                                      (cauchyCriterionForSeriesDecodeBHist T)
                                                      (cauchyCriterionForSeriesDecodeBHist H)
                                                      (cauchyCriterionForSeriesDecodeBHist C)
                                                      (cauchyCriterionForSeriesDecodeBHist P)
                                                      (cauchyCriterionForSeriesDecodeBHist N))
                                              | _ :: _ => none

private theorem CauchyCriterionForSeriesTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyCriterionForSeriesUp,
      cauchyCriterionForSeriesFromEventFlow (cauchyCriterionForSeriesToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A L W D R E T H C P N =>
      change
        some
          (CauchyCriterionForSeriesUp.mk
            (cauchyCriterionForSeriesDecodeBHist (cauchyCriterionForSeriesEncodeBHist A))
            (cauchyCriterionForSeriesDecodeBHist (cauchyCriterionForSeriesEncodeBHist L))
            (cauchyCriterionForSeriesDecodeBHist (cauchyCriterionForSeriesEncodeBHist W))
            (cauchyCriterionForSeriesDecodeBHist (cauchyCriterionForSeriesEncodeBHist D))
            (cauchyCriterionForSeriesDecodeBHist (cauchyCriterionForSeriesEncodeBHist R))
            (cauchyCriterionForSeriesDecodeBHist (cauchyCriterionForSeriesEncodeBHist E))
            (cauchyCriterionForSeriesDecodeBHist (cauchyCriterionForSeriesEncodeBHist T))
            (cauchyCriterionForSeriesDecodeBHist (cauchyCriterionForSeriesEncodeBHist H))
            (cauchyCriterionForSeriesDecodeBHist (cauchyCriterionForSeriesEncodeBHist C))
            (cauchyCriterionForSeriesDecodeBHist (cauchyCriterionForSeriesEncodeBHist P))
            (cauchyCriterionForSeriesDecodeBHist (cauchyCriterionForSeriesEncodeBHist N))) =
          some (CauchyCriterionForSeriesUp.mk A L W D R E T H C P N)
      rw [CauchyCriterionForSeriesTasteGate_single_carrier_alignment_decode A,
        CauchyCriterionForSeriesTasteGate_single_carrier_alignment_decode L,
        CauchyCriterionForSeriesTasteGate_single_carrier_alignment_decode W,
        CauchyCriterionForSeriesTasteGate_single_carrier_alignment_decode D,
        CauchyCriterionForSeriesTasteGate_single_carrier_alignment_decode R,
        CauchyCriterionForSeriesTasteGate_single_carrier_alignment_decode E,
        CauchyCriterionForSeriesTasteGate_single_carrier_alignment_decode T,
        CauchyCriterionForSeriesTasteGate_single_carrier_alignment_decode H,
        CauchyCriterionForSeriesTasteGate_single_carrier_alignment_decode C,
        CauchyCriterionForSeriesTasteGate_single_carrier_alignment_decode P,
        CauchyCriterionForSeriesTasteGate_single_carrier_alignment_decode N]

private theorem CauchyCriterionForSeriesTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyCriterionForSeriesUp} :
    cauchyCriterionForSeriesToEventFlow x = cauchyCriterionForSeriesToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyCriterionForSeriesFromEventFlow (cauchyCriterionForSeriesToEventFlow x) =
        cauchyCriterionForSeriesFromEventFlow (cauchyCriterionForSeriesToEventFlow y) :=
    congrArg cauchyCriterionForSeriesFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyCriterionForSeriesTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyCriterionForSeriesTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyCriterionForSeriesBHistCarrier :
    BHistCarrier CauchyCriterionForSeriesUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCriterionForSeriesToEventFlow
  fromEventFlow := cauchyCriterionForSeriesFromEventFlow

instance cauchyCriterionForSeriesChapterTasteGate :
    ChapterTasteGate CauchyCriterionForSeriesUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyCriterionForSeriesFromEventFlow (cauchyCriterionForSeriesToEventFlow x) = some x
    exact CauchyCriterionForSeriesTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchyCriterionForSeriesTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate CauchyCriterionForSeriesUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyCriterionForSeriesChapterTasteGate

theorem CauchyCriterionForSeriesTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyCriterionForSeriesDecodeBHist (cauchyCriterionForSeriesEncodeBHist h) = h) ∧
      (∀ x : CauchyCriterionForSeriesUp,
        cauchyCriterionForSeriesFromEventFlow (cauchyCriterionForSeriesToEventFlow x) =
          some x) ∧
        Nonempty (BHistCarrier CauchyCriterionForSeriesUp) ∧
          Nonempty (ChapterTasteGate CauchyCriterionForSeriesUp) ∧
            cauchyCriterionForSeriesEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CauchyCriterionForSeriesTasteGate_single_carrier_alignment_decode,
      CauchyCriterionForSeriesTasteGate_single_carrier_alignment_round_trip,
      ⟨cauchyCriterionForSeriesBHistCarrier⟩,
      ⟨cauchyCriterionForSeriesChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.CauchyCriterionForSeriesUp
