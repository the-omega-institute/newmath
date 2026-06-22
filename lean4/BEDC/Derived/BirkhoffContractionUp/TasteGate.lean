import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BirkhoffContractionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BirkhoffContractionUp : Type where
  | mk (V K M Delta T tau R E H C P N : BHist) : BirkhoffContractionUp
  deriving DecidableEq

def birkhoffContractionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: birkhoffContractionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: birkhoffContractionEncodeBHist h

def birkhoffContractionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (birkhoffContractionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (birkhoffContractionDecodeBHist tail)

private theorem BirkhoffContractionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      birkhoffContractionDecodeBHist (birkhoffContractionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def birkhoffContractionToEventFlow : BirkhoffContractionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BirkhoffContractionUp.mk V K M Delta T tau R E H C P N =>
      [birkhoffContractionEncodeBHist V,
        birkhoffContractionEncodeBHist K,
        birkhoffContractionEncodeBHist M,
        birkhoffContractionEncodeBHist Delta,
        birkhoffContractionEncodeBHist T,
        birkhoffContractionEncodeBHist tau,
        birkhoffContractionEncodeBHist R,
        birkhoffContractionEncodeBHist E,
        birkhoffContractionEncodeBHist H,
        birkhoffContractionEncodeBHist C,
        birkhoffContractionEncodeBHist P,
        birkhoffContractionEncodeBHist N]

def birkhoffContractionFromEventFlow : EventFlow → Option BirkhoffContractionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | V :: restK =>
      match restK with
      | [] => none
      | K :: restM =>
          match restM with
          | [] => none
          | M :: restDelta =>
              match restDelta with
              | [] => none
              | Delta :: restT =>
                  match restT with
                  | [] => none
                  | T :: restTau =>
                      match restTau with
                      | [] => none
                      | tau :: restR =>
                          match restR with
                          | [] => none
                          | R :: restE =>
                              match restE with
                              | [] => none
                              | E :: restH =>
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
                                                        (BirkhoffContractionUp.mk
                                                          (birkhoffContractionDecodeBHist V)
                                                          (birkhoffContractionDecodeBHist K)
                                                          (birkhoffContractionDecodeBHist M)
                                                          (birkhoffContractionDecodeBHist Delta)
                                                          (birkhoffContractionDecodeBHist T)
                                                          (birkhoffContractionDecodeBHist tau)
                                                          (birkhoffContractionDecodeBHist R)
                                                          (birkhoffContractionDecodeBHist E)
                                                          (birkhoffContractionDecodeBHist H)
                                                          (birkhoffContractionDecodeBHist C)
                                                          (birkhoffContractionDecodeBHist P)
                                                          (birkhoffContractionDecodeBHist N))
                                                  | _ :: _ => none

private theorem BirkhoffContractionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BirkhoffContractionUp,
      birkhoffContractionFromEventFlow (birkhoffContractionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk V K M Delta T tau R E H C P N =>
      change
        some
          (BirkhoffContractionUp.mk
            (birkhoffContractionDecodeBHist (birkhoffContractionEncodeBHist V))
            (birkhoffContractionDecodeBHist (birkhoffContractionEncodeBHist K))
            (birkhoffContractionDecodeBHist (birkhoffContractionEncodeBHist M))
            (birkhoffContractionDecodeBHist (birkhoffContractionEncodeBHist Delta))
            (birkhoffContractionDecodeBHist (birkhoffContractionEncodeBHist T))
            (birkhoffContractionDecodeBHist (birkhoffContractionEncodeBHist tau))
            (birkhoffContractionDecodeBHist (birkhoffContractionEncodeBHist R))
            (birkhoffContractionDecodeBHist (birkhoffContractionEncodeBHist E))
            (birkhoffContractionDecodeBHist (birkhoffContractionEncodeBHist H))
            (birkhoffContractionDecodeBHist (birkhoffContractionEncodeBHist C))
            (birkhoffContractionDecodeBHist (birkhoffContractionEncodeBHist P))
            (birkhoffContractionDecodeBHist (birkhoffContractionEncodeBHist N))) =
          some (BirkhoffContractionUp.mk V K M Delta T tau R E H C P N)
      rw [BirkhoffContractionTasteGate_single_carrier_alignment_decode V,
        BirkhoffContractionTasteGate_single_carrier_alignment_decode K,
        BirkhoffContractionTasteGate_single_carrier_alignment_decode M,
        BirkhoffContractionTasteGate_single_carrier_alignment_decode Delta,
        BirkhoffContractionTasteGate_single_carrier_alignment_decode T,
        BirkhoffContractionTasteGate_single_carrier_alignment_decode tau,
        BirkhoffContractionTasteGate_single_carrier_alignment_decode R,
        BirkhoffContractionTasteGate_single_carrier_alignment_decode E,
        BirkhoffContractionTasteGate_single_carrier_alignment_decode H,
        BirkhoffContractionTasteGate_single_carrier_alignment_decode C,
        BirkhoffContractionTasteGate_single_carrier_alignment_decode P,
        BirkhoffContractionTasteGate_single_carrier_alignment_decode N]

theorem BirkhoffContractionTasteGate_single_carrier_alignment_injective
    {x y : BirkhoffContractionUp} :
    birkhoffContractionToEventFlow x = birkhoffContractionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      birkhoffContractionFromEventFlow (birkhoffContractionToEventFlow x) =
        birkhoffContractionFromEventFlow (birkhoffContractionToEventFlow y) :=
    congrArg birkhoffContractionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BirkhoffContractionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BirkhoffContractionTasteGate_single_carrier_alignment_round_trip y)))

instance birkhoffContractionBHistCarrier : BHistCarrier BirkhoffContractionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := birkhoffContractionToEventFlow
  fromEventFlow := birkhoffContractionFromEventFlow

instance birkhoffContractionChapterTasteGate : ChapterTasteGate BirkhoffContractionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      birkhoffContractionFromEventFlow (birkhoffContractionToEventFlow x) = some x
    exact BirkhoffContractionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BirkhoffContractionTasteGate_single_carrier_alignment_injective heq)

theorem BirkhoffContractionTasteGate_single_carrier_alignment :
    (∀ h : BHist, birkhoffContractionDecodeBHist (birkhoffContractionEncodeBHist h) = h) ∧
      (∀ x : BirkhoffContractionUp,
        birkhoffContractionFromEventFlow (birkhoffContractionToEventFlow x) = some x) ∧
        (∀ x y : BirkhoffContractionUp,
          birkhoffContractionToEventFlow x = birkhoffContractionToEventFlow y → x = y) ∧
          birkhoffContractionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact BirkhoffContractionTasteGate_single_carrier_alignment_decode
  · constructor
    · exact BirkhoffContractionTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact BirkhoffContractionTasteGate_single_carrier_alignment_injective heq
      · rfl

end BEDC.Derived.BirkhoffContractionUp
