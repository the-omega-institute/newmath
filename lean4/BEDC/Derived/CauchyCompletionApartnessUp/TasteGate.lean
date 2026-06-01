import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCompletionApartnessUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCompletionApartnessUp : Type where
  | mk (U R S W E G H C P N : BHist) : CauchyCompletionApartnessUp
  deriving DecidableEq

def cauchyCompletionApartnessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCompletionApartnessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCompletionApartnessEncodeBHist h

def cauchyCompletionApartnessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCompletionApartnessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCompletionApartnessDecodeBHist tail)

private theorem cauchyCompletionApartnessDecode_encode_bhist :
    ∀ h : BHist,
      cauchyCompletionApartnessDecodeBHist (cauchyCompletionApartnessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyCompletionApartnessFields : CauchyCompletionApartnessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCompletionApartnessUp.mk U R S W E G H C P N => [U, R, S, W, E, G, H, C, P, N]

def cauchyCompletionApartnessToEventFlow : CauchyCompletionApartnessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyCompletionApartnessFields x).map cauchyCompletionApartnessEncodeBHist

def cauchyCompletionApartnessFromEventFlow :
    EventFlow → Option CauchyCompletionApartnessUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | U :: restR =>
      match restR with
      | [] => none
      | R :: restS =>
          match restS with
          | [] => none
          | S :: restW =>
              match restW with
              | [] => none
              | W :: restE =>
                  match restE with
                  | [] => none
                  | E :: restG =>
                      match restG with
                      | [] => none
                      | G :: restH =>
                          match restH with
                          | [] => none
                          | H :: restC =>
                              match restC with
                              | [] => none
                              | C :: restP =>
                                  match restP with
                                  | [] => none
                                  | P :: restN =>
                                      match restN with
                                      | [] => none
                                      | N :: rest =>
                                          match rest with
                                          | [] =>
                                              some
                                                (CauchyCompletionApartnessUp.mk
                                                  (cauchyCompletionApartnessDecodeBHist U)
                                                  (cauchyCompletionApartnessDecodeBHist R)
                                                  (cauchyCompletionApartnessDecodeBHist S)
                                                  (cauchyCompletionApartnessDecodeBHist W)
                                                  (cauchyCompletionApartnessDecodeBHist E)
                                                  (cauchyCompletionApartnessDecodeBHist G)
                                                  (cauchyCompletionApartnessDecodeBHist H)
                                                  (cauchyCompletionApartnessDecodeBHist C)
                                                  (cauchyCompletionApartnessDecodeBHist P)
                                                  (cauchyCompletionApartnessDecodeBHist N))
                                          | _ :: _ => none

private theorem cauchyCompletionApartness_round_trip :
    ∀ x : CauchyCompletionApartnessUp,
      cauchyCompletionApartnessFromEventFlow
        (cauchyCompletionApartnessToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk U R S W E G H C P N =>
      change
        some
          (CauchyCompletionApartnessUp.mk
            (cauchyCompletionApartnessDecodeBHist (cauchyCompletionApartnessEncodeBHist U))
            (cauchyCompletionApartnessDecodeBHist (cauchyCompletionApartnessEncodeBHist R))
            (cauchyCompletionApartnessDecodeBHist (cauchyCompletionApartnessEncodeBHist S))
            (cauchyCompletionApartnessDecodeBHist (cauchyCompletionApartnessEncodeBHist W))
            (cauchyCompletionApartnessDecodeBHist (cauchyCompletionApartnessEncodeBHist E))
            (cauchyCompletionApartnessDecodeBHist (cauchyCompletionApartnessEncodeBHist G))
            (cauchyCompletionApartnessDecodeBHist (cauchyCompletionApartnessEncodeBHist H))
            (cauchyCompletionApartnessDecodeBHist (cauchyCompletionApartnessEncodeBHist C))
            (cauchyCompletionApartnessDecodeBHist (cauchyCompletionApartnessEncodeBHist P))
            (cauchyCompletionApartnessDecodeBHist (cauchyCompletionApartnessEncodeBHist N))) =
          some (CauchyCompletionApartnessUp.mk U R S W E G H C P N)
      rw [cauchyCompletionApartnessDecode_encode_bhist U,
        cauchyCompletionApartnessDecode_encode_bhist R,
        cauchyCompletionApartnessDecode_encode_bhist S,
        cauchyCompletionApartnessDecode_encode_bhist W,
        cauchyCompletionApartnessDecode_encode_bhist E,
        cauchyCompletionApartnessDecode_encode_bhist G,
        cauchyCompletionApartnessDecode_encode_bhist H,
        cauchyCompletionApartnessDecode_encode_bhist C,
        cauchyCompletionApartnessDecode_encode_bhist P,
        cauchyCompletionApartnessDecode_encode_bhist N]

private theorem cauchyCompletionApartnessToEventFlow_injective
    {x y : CauchyCompletionApartnessUp} :
    cauchyCompletionApartnessToEventFlow x =
      cauchyCompletionApartnessToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyCompletionApartnessFromEventFlow (cauchyCompletionApartnessToEventFlow x) =
        cauchyCompletionApartnessFromEventFlow (cauchyCompletionApartnessToEventFlow y) :=
    congrArg cauchyCompletionApartnessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyCompletionApartness_round_trip x).symm
      (Eq.trans hread (cauchyCompletionApartness_round_trip y)))

instance cauchyCompletionApartnessBHistCarrier : BHistCarrier CauchyCompletionApartnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCompletionApartnessToEventFlow
  fromEventFlow := cauchyCompletionApartnessFromEventFlow

instance cauchyCompletionApartnessChapterTasteGate :
    ChapterTasteGate CauchyCompletionApartnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyCompletionApartnessFromEventFlow (cauchyCompletionApartnessToEventFlow x) =
        some x
    exact cauchyCompletionApartness_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyCompletionApartnessToEventFlow_injective heq)

theorem CauchyCompletionApartnessCarrier_namecert_obligations :
    Nonempty (ChapterTasteGate CauchyCompletionApartnessUp) ∧
      (∀ h : BHist,
        cauchyCompletionApartnessDecodeBHist (cauchyCompletionApartnessEncodeBHist h) = h) ∧
        (∀ x : CauchyCompletionApartnessUp,
          cauchyCompletionApartnessFromEventFlow
            (cauchyCompletionApartnessToEventFlow x) = some x) ∧
          cauchyCompletionApartnessEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact ⟨cauchyCompletionApartnessChapterTasteGate⟩
  · constructor
    · exact cauchyCompletionApartnessDecode_encode_bhist
    · constructor
      · exact cauchyCompletionApartness_round_trip
      · rfl

end BEDC.Derived.CauchyCompletionApartnessUp.TasteGate
