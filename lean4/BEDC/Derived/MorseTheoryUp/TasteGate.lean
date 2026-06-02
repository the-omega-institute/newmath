import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MorseTheoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MorseTheoryUp : Type where
  | mk (X F D R T G L H C P N : BHist) : MorseTheoryUp
  deriving DecidableEq

def morseTheoryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: morseTheoryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: morseTheoryEncodeBHist h

def morseTheoryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (morseTheoryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (morseTheoryDecodeBHist tail)

private theorem MorseTheoryTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, morseTheoryDecodeBHist (morseTheoryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def morseTheoryToEventFlow : MorseTheoryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MorseTheoryUp.mk X F D R T G L H C P N =>
      [morseTheoryEncodeBHist X,
        morseTheoryEncodeBHist F,
        morseTheoryEncodeBHist D,
        morseTheoryEncodeBHist R,
        morseTheoryEncodeBHist T,
        morseTheoryEncodeBHist G,
        morseTheoryEncodeBHist L,
        morseTheoryEncodeBHist H,
        morseTheoryEncodeBHist C,
        morseTheoryEncodeBHist P,
        morseTheoryEncodeBHist N]

def morseTheoryFromEventFlow : EventFlow → Option MorseTheoryUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | X :: rest0 =>
      match rest0 with
      | [] => none
      | F :: rest1 =>
          match rest1 with
          | [] => none
          | D :: rest2 =>
              match rest2 with
              | [] => none
              | R :: rest3 =>
                  match rest3 with
                  | [] => none
                  | T :: rest4 =>
                      match rest4 with
                      | [] => none
                      | G :: rest5 =>
                          match rest5 with
                          | [] => none
                          | L :: rest6 =>
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
                                                    (MorseTheoryUp.mk
                                                      (morseTheoryDecodeBHist X)
                                                      (morseTheoryDecodeBHist F)
                                                      (morseTheoryDecodeBHist D)
                                                      (morseTheoryDecodeBHist R)
                                                      (morseTheoryDecodeBHist T)
                                                      (morseTheoryDecodeBHist G)
                                                      (morseTheoryDecodeBHist L)
                                                      (morseTheoryDecodeBHist H)
                                                      (morseTheoryDecodeBHist C)
                                                      (morseTheoryDecodeBHist P)
                                                      (morseTheoryDecodeBHist N))
                                              | _extra :: _rest => none

private theorem morseTheory_round_trip :
    ∀ x : MorseTheoryUp,
      morseTheoryFromEventFlow (morseTheoryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X F D R T G L H C P N =>
      change
        some
          (MorseTheoryUp.mk
            (morseTheoryDecodeBHist (morseTheoryEncodeBHist X))
            (morseTheoryDecodeBHist (morseTheoryEncodeBHist F))
            (morseTheoryDecodeBHist (morseTheoryEncodeBHist D))
            (morseTheoryDecodeBHist (morseTheoryEncodeBHist R))
            (morseTheoryDecodeBHist (morseTheoryEncodeBHist T))
            (morseTheoryDecodeBHist (morseTheoryEncodeBHist G))
            (morseTheoryDecodeBHist (morseTheoryEncodeBHist L))
            (morseTheoryDecodeBHist (morseTheoryEncodeBHist H))
            (morseTheoryDecodeBHist (morseTheoryEncodeBHist C))
            (morseTheoryDecodeBHist (morseTheoryEncodeBHist P))
            (morseTheoryDecodeBHist (morseTheoryEncodeBHist N))) =
          some (MorseTheoryUp.mk X F D R T G L H C P N)
      rw [MorseTheoryTasteGate_single_carrier_alignment_decode X,
        MorseTheoryTasteGate_single_carrier_alignment_decode F,
        MorseTheoryTasteGate_single_carrier_alignment_decode D,
        MorseTheoryTasteGate_single_carrier_alignment_decode R,
        MorseTheoryTasteGate_single_carrier_alignment_decode T,
        MorseTheoryTasteGate_single_carrier_alignment_decode G,
        MorseTheoryTasteGate_single_carrier_alignment_decode L,
        MorseTheoryTasteGate_single_carrier_alignment_decode H,
        MorseTheoryTasteGate_single_carrier_alignment_decode C,
        MorseTheoryTasteGate_single_carrier_alignment_decode P,
        MorseTheoryTasteGate_single_carrier_alignment_decode N]

private theorem morseTheoryToEventFlow_injective {x y : MorseTheoryUp} :
    morseTheoryToEventFlow x = morseTheoryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      morseTheoryFromEventFlow (morseTheoryToEventFlow x) =
        morseTheoryFromEventFlow (morseTheoryToEventFlow y) :=
    congrArg morseTheoryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (morseTheory_round_trip x).symm
      (Eq.trans hread (morseTheory_round_trip y)))

instance morseTheoryBHistCarrier : BHistCarrier MorseTheoryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := morseTheoryToEventFlow
  fromEventFlow := morseTheoryFromEventFlow

instance morseTheoryChapterTasteGate : ChapterTasteGate MorseTheoryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change morseTheoryFromEventFlow (morseTheoryToEventFlow x) = some x
    exact morseTheory_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (morseTheoryToEventFlow_injective heq)

def taste_gate : ChapterTasteGate MorseTheoryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  morseTheoryChapterTasteGate

theorem MorseTheoryTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier MorseTheoryUp) ∧ Nonempty (ChapterTasteGate MorseTheoryUp) ∧
      (∀ h : BHist, morseTheoryDecodeBHist (morseTheoryEncodeBHist h) = h) ∧
        morseTheoryEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨morseTheoryBHistCarrier⟩,
      ⟨morseTheoryChapterTasteGate⟩,
      MorseTheoryTasteGate_single_carrier_alignment_decode,
      rfl⟩

end BEDC.Derived.MorseTheoryUp
