import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealCauchyFilterUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealCauchyFilterUp : Type where
  | mk (F M D S Q E H C P N : BHist) : RealCauchyFilterUp

def realCauchyFilterEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realCauchyFilterEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realCauchyFilterEncodeBHist h

def realCauchyFilterDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realCauchyFilterDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realCauchyFilterDecodeBHist tail)

private theorem RealCauchyFilterTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, realCauchyFilterDecodeBHist (realCauchyFilterEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realCauchyFilterToEventFlow : RealCauchyFilterUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RealCauchyFilterUp.mk F M D S Q E H C P N =>
      [realCauchyFilterEncodeBHist F,
        realCauchyFilterEncodeBHist M,
        realCauchyFilterEncodeBHist D,
        realCauchyFilterEncodeBHist S,
        realCauchyFilterEncodeBHist Q,
        realCauchyFilterEncodeBHist E,
        realCauchyFilterEncodeBHist H,
        realCauchyFilterEncodeBHist C,
        realCauchyFilterEncodeBHist P,
        realCauchyFilterEncodeBHist N]

def realCauchyFilterFromEventFlow : EventFlow → Option RealCauchyFilterUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | F :: rest0 =>
      match rest0 with
      | [] => none
      | M :: rest1 =>
          match rest1 with
          | [] => none
          | D :: rest2 =>
              match rest2 with
              | [] => none
              | S :: rest3 =>
                  match rest3 with
                  | [] => none
                  | Q :: rest4 =>
                      match rest4 with
                      | [] => none
                      | E :: rest5 =>
                          match rest5 with
                          | [] => none
                          | H :: rest6 =>
                              match rest6 with
                              | [] => none
                              | C :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | P :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | N :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (RealCauchyFilterUp.mk
                                                  (realCauchyFilterDecodeBHist F)
                                                  (realCauchyFilterDecodeBHist M)
                                                  (realCauchyFilterDecodeBHist D)
                                                  (realCauchyFilterDecodeBHist S)
                                                  (realCauchyFilterDecodeBHist Q)
                                                  (realCauchyFilterDecodeBHist E)
                                                  (realCauchyFilterDecodeBHist H)
                                                  (realCauchyFilterDecodeBHist C)
                                                  (realCauchyFilterDecodeBHist P)
                                                  (realCauchyFilterDecodeBHist N))
                                          | _extra :: _rest => none

private theorem realCauchyFilter_round_trip :
    ∀ x : RealCauchyFilterUp,
      realCauchyFilterFromEventFlow (realCauchyFilterToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F M D S Q E H C P N =>
      change
        some
          (RealCauchyFilterUp.mk
            (realCauchyFilterDecodeBHist (realCauchyFilterEncodeBHist F))
            (realCauchyFilterDecodeBHist (realCauchyFilterEncodeBHist M))
            (realCauchyFilterDecodeBHist (realCauchyFilterEncodeBHist D))
            (realCauchyFilterDecodeBHist (realCauchyFilterEncodeBHist S))
            (realCauchyFilterDecodeBHist (realCauchyFilterEncodeBHist Q))
            (realCauchyFilterDecodeBHist (realCauchyFilterEncodeBHist E))
            (realCauchyFilterDecodeBHist (realCauchyFilterEncodeBHist H))
            (realCauchyFilterDecodeBHist (realCauchyFilterEncodeBHist C))
            (realCauchyFilterDecodeBHist (realCauchyFilterEncodeBHist P))
            (realCauchyFilterDecodeBHist (realCauchyFilterEncodeBHist N))) =
          some (RealCauchyFilterUp.mk F M D S Q E H C P N)
      rw [RealCauchyFilterTasteGate_single_carrier_alignment_decode F,
        RealCauchyFilterTasteGate_single_carrier_alignment_decode M,
        RealCauchyFilterTasteGate_single_carrier_alignment_decode D,
        RealCauchyFilterTasteGate_single_carrier_alignment_decode S,
        RealCauchyFilterTasteGate_single_carrier_alignment_decode Q,
        RealCauchyFilterTasteGate_single_carrier_alignment_decode E,
        RealCauchyFilterTasteGate_single_carrier_alignment_decode H,
        RealCauchyFilterTasteGate_single_carrier_alignment_decode C,
        RealCauchyFilterTasteGate_single_carrier_alignment_decode P,
        RealCauchyFilterTasteGate_single_carrier_alignment_decode N]

private theorem realCauchyFilterToEventFlow_injective {x y : RealCauchyFilterUp} :
    realCauchyFilterToEventFlow x = realCauchyFilterToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realCauchyFilterFromEventFlow (realCauchyFilterToEventFlow x) =
        realCauchyFilterFromEventFlow (realCauchyFilterToEventFlow y) :=
    congrArg realCauchyFilterFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realCauchyFilter_round_trip x).symm
      (Eq.trans hread (realCauchyFilter_round_trip y)))

instance realCauchyFilterBHistCarrier : BHistCarrier RealCauchyFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realCauchyFilterToEventFlow
  fromEventFlow := realCauchyFilterFromEventFlow

instance realCauchyFilterChapterTasteGate : ChapterTasteGate RealCauchyFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realCauchyFilterFromEventFlow (realCauchyFilterToEventFlow x) = some x
    exact realCauchyFilter_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realCauchyFilterToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RealCauchyFilterUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realCauchyFilterChapterTasteGate

theorem RealCauchyFilterTasteGate_single_carrier_alignment :
    (∀ h : BHist, realCauchyFilterDecodeBHist (realCauchyFilterEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier RealCauchyFilterUp) ∧
        Nonempty (ChapterTasteGate RealCauchyFilterUp) ∧
          realCauchyFilterEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨RealCauchyFilterTasteGate_single_carrier_alignment_decode,
      ⟨realCauchyFilterBHistCarrier⟩,
      ⟨realCauchyFilterChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.RealCauchyFilterUp
