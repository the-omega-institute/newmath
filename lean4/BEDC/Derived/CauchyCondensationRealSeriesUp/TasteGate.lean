import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCondensationRealSeriesUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCondensationRealSeriesUp : Type where
  | mk (A M B G W Q D R E H C P N : BHist) : CauchyCondensationRealSeriesUp
  deriving DecidableEq

def cauchyCondensationRealSeriesEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCondensationRealSeriesEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCondensationRealSeriesEncodeBHist h

def cauchyCondensationRealSeriesDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCondensationRealSeriesDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCondensationRealSeriesDecodeBHist tail)

private theorem CauchyCondensationRealSeriesTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      cauchyCondensationRealSeriesDecodeBHist
        (cauchyCondensationRealSeriesEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyCondensationRealSeriesToEventFlow :
    CauchyCondensationRealSeriesUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCondensationRealSeriesUp.mk A M B G W Q D R E H C P N =>
      [cauchyCondensationRealSeriesEncodeBHist A,
        cauchyCondensationRealSeriesEncodeBHist M,
        cauchyCondensationRealSeriesEncodeBHist B,
        cauchyCondensationRealSeriesEncodeBHist G,
        cauchyCondensationRealSeriesEncodeBHist W,
        cauchyCondensationRealSeriesEncodeBHist Q,
        cauchyCondensationRealSeriesEncodeBHist D,
        cauchyCondensationRealSeriesEncodeBHist R,
        cauchyCondensationRealSeriesEncodeBHist E,
        cauchyCondensationRealSeriesEncodeBHist H,
        cauchyCondensationRealSeriesEncodeBHist C,
        cauchyCondensationRealSeriesEncodeBHist P,
        cauchyCondensationRealSeriesEncodeBHist N]

def cauchyCondensationRealSeriesFromEventFlow :
    EventFlow → Option CauchyCondensationRealSeriesUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | A :: rest0 =>
      match rest0 with
      | [] => none
      | M :: rest1 =>
          match rest1 with
          | [] => none
          | B :: rest2 =>
              match rest2 with
              | [] => none
              | G :: rest3 =>
                  match rest3 with
                  | [] => none
                  | W :: rest4 =>
                      match rest4 with
                      | [] => none
                      | Q :: rest5 =>
                          match rest5 with
                          | [] => none
                          | D :: rest6 =>
                              match rest6 with
                              | [] => none
                              | R :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | E :: rest8 =>
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
                                                            (CauchyCondensationRealSeriesUp.mk
                                                              (cauchyCondensationRealSeriesDecodeBHist A)
                                                              (cauchyCondensationRealSeriesDecodeBHist M)
                                                              (cauchyCondensationRealSeriesDecodeBHist B)
                                                              (cauchyCondensationRealSeriesDecodeBHist G)
                                                              (cauchyCondensationRealSeriesDecodeBHist W)
                                                              (cauchyCondensationRealSeriesDecodeBHist Q)
                                                              (cauchyCondensationRealSeriesDecodeBHist D)
                                                              (cauchyCondensationRealSeriesDecodeBHist R)
                                                              (cauchyCondensationRealSeriesDecodeBHist E)
                                                              (cauchyCondensationRealSeriesDecodeBHist H)
                                                              (cauchyCondensationRealSeriesDecodeBHist C)
                                                              (cauchyCondensationRealSeriesDecodeBHist P)
                                                              (cauchyCondensationRealSeriesDecodeBHist N))
                                                      | _ :: _ => none

private theorem CauchyCondensationRealSeriesTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyCondensationRealSeriesUp,
      cauchyCondensationRealSeriesFromEventFlow
        (cauchyCondensationRealSeriesToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A M B G W Q D R E H C P N =>
      change
        some
          (CauchyCondensationRealSeriesUp.mk
            (cauchyCondensationRealSeriesDecodeBHist
              (cauchyCondensationRealSeriesEncodeBHist A))
            (cauchyCondensationRealSeriesDecodeBHist
              (cauchyCondensationRealSeriesEncodeBHist M))
            (cauchyCondensationRealSeriesDecodeBHist
              (cauchyCondensationRealSeriesEncodeBHist B))
            (cauchyCondensationRealSeriesDecodeBHist
              (cauchyCondensationRealSeriesEncodeBHist G))
            (cauchyCondensationRealSeriesDecodeBHist
              (cauchyCondensationRealSeriesEncodeBHist W))
            (cauchyCondensationRealSeriesDecodeBHist
              (cauchyCondensationRealSeriesEncodeBHist Q))
            (cauchyCondensationRealSeriesDecodeBHist
              (cauchyCondensationRealSeriesEncodeBHist D))
            (cauchyCondensationRealSeriesDecodeBHist
              (cauchyCondensationRealSeriesEncodeBHist R))
            (cauchyCondensationRealSeriesDecodeBHist
              (cauchyCondensationRealSeriesEncodeBHist E))
            (cauchyCondensationRealSeriesDecodeBHist
              (cauchyCondensationRealSeriesEncodeBHist H))
            (cauchyCondensationRealSeriesDecodeBHist
              (cauchyCondensationRealSeriesEncodeBHist C))
            (cauchyCondensationRealSeriesDecodeBHist
              (cauchyCondensationRealSeriesEncodeBHist P))
            (cauchyCondensationRealSeriesDecodeBHist
              (cauchyCondensationRealSeriesEncodeBHist N))) =
          some (CauchyCondensationRealSeriesUp.mk A M B G W Q D R E H C P N)
      rw [CauchyCondensationRealSeriesTasteGate_single_carrier_alignment_decode A,
        CauchyCondensationRealSeriesTasteGate_single_carrier_alignment_decode M,
        CauchyCondensationRealSeriesTasteGate_single_carrier_alignment_decode B,
        CauchyCondensationRealSeriesTasteGate_single_carrier_alignment_decode G,
        CauchyCondensationRealSeriesTasteGate_single_carrier_alignment_decode W,
        CauchyCondensationRealSeriesTasteGate_single_carrier_alignment_decode Q,
        CauchyCondensationRealSeriesTasteGate_single_carrier_alignment_decode D,
        CauchyCondensationRealSeriesTasteGate_single_carrier_alignment_decode R,
        CauchyCondensationRealSeriesTasteGate_single_carrier_alignment_decode E,
        CauchyCondensationRealSeriesTasteGate_single_carrier_alignment_decode H,
        CauchyCondensationRealSeriesTasteGate_single_carrier_alignment_decode C,
        CauchyCondensationRealSeriesTasteGate_single_carrier_alignment_decode P,
        CauchyCondensationRealSeriesTasteGate_single_carrier_alignment_decode N]

private theorem CauchyCondensationRealSeriesTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyCondensationRealSeriesUp} :
    cauchyCondensationRealSeriesToEventFlow x =
      cauchyCondensationRealSeriesToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyCondensationRealSeriesFromEventFlow
          (cauchyCondensationRealSeriesToEventFlow x) =
        cauchyCondensationRealSeriesFromEventFlow
          (cauchyCondensationRealSeriesToEventFlow y) :=
    congrArg cauchyCondensationRealSeriesFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyCondensationRealSeriesTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyCondensationRealSeriesTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyCondensationRealSeriesBHistCarrier :
    BHistCarrier CauchyCondensationRealSeriesUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCondensationRealSeriesToEventFlow
  fromEventFlow := cauchyCondensationRealSeriesFromEventFlow

instance cauchyCondensationRealSeriesChapterTasteGate :
    ChapterTasteGate CauchyCondensationRealSeriesUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyCondensationRealSeriesFromEventFlow
      (cauchyCondensationRealSeriesToEventFlow x) = some x
    exact CauchyCondensationRealSeriesTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchyCondensationRealSeriesTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def CauchyCondensationRealSeriesTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate CauchyCondensationRealSeriesUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyCondensationRealSeriesChapterTasteGate

theorem CauchyCondensationRealSeriesTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyCondensationRealSeriesDecodeBHist
        (cauchyCondensationRealSeriesEncodeBHist h) = h) ∧
      (∀ x : CauchyCondensationRealSeriesUp,
        cauchyCondensationRealSeriesFromEventFlow
          (cauchyCondensationRealSeriesToEventFlow x) = some x) ∧
        (∀ x y : CauchyCondensationRealSeriesUp,
          cauchyCondensationRealSeriesToEventFlow x =
            cauchyCondensationRealSeriesToEventFlow y → x = y) ∧
          cauchyCondensationRealSeriesEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CauchyCondensationRealSeriesTasteGate_single_carrier_alignment_decode,
      CauchyCondensationRealSeriesTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        CauchyCondensationRealSeriesTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CauchyCondensationRealSeriesUp
