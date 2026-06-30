import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ClassifierBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ClassifierBoundaryUp : Type where
  | mk (S A R T G H C P N : BHist) : ClassifierBoundaryUp
  deriving DecidableEq

def classifierBoundaryEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: classifierBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: classifierBoundaryEncodeBHist h

def classifierBoundaryDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (classifierBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (classifierBoundaryDecodeBHist tail)

private theorem ClassifierBoundaryTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      classifierBoundaryDecodeBHist (classifierBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def classifierBoundaryToEventFlow : ClassifierBoundaryUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ClassifierBoundaryUp.mk S A R T G H C P N =>
      [classifierBoundaryEncodeBHist S,
        classifierBoundaryEncodeBHist A,
        classifierBoundaryEncodeBHist R,
        classifierBoundaryEncodeBHist T,
        classifierBoundaryEncodeBHist G,
        classifierBoundaryEncodeBHist H,
        classifierBoundaryEncodeBHist C,
        classifierBoundaryEncodeBHist P,
        classifierBoundaryEncodeBHist N]

def classifierBoundaryFromEventFlow : EventFlow -> Option ClassifierBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | S :: rest0 =>
      match rest0 with
      | [] => none
      | A :: rest1 =>
          match rest1 with
          | [] => none
          | R :: rest2 =>
              match rest2 with
              | [] => none
              | T :: rest3 =>
                  match rest3 with
                  | [] => none
                  | G :: rest4 =>
                      match rest4 with
                      | [] => none
                      | H :: rest5 =>
                          match rest5 with
                          | [] => none
                          | C :: rest6 =>
                              match rest6 with
                              | [] => none
                              | P :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | N :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some
                                            (ClassifierBoundaryUp.mk
                                              (classifierBoundaryDecodeBHist S)
                                              (classifierBoundaryDecodeBHist A)
                                              (classifierBoundaryDecodeBHist R)
                                              (classifierBoundaryDecodeBHist T)
                                              (classifierBoundaryDecodeBHist G)
                                              (classifierBoundaryDecodeBHist H)
                                              (classifierBoundaryDecodeBHist C)
                                              (classifierBoundaryDecodeBHist P)
                                              (classifierBoundaryDecodeBHist N))
                                      | _ :: _ => none

private theorem ClassifierBoundaryTasteGate_single_carrier_alignment_round_trip :
    forall x : ClassifierBoundaryUp,
      classifierBoundaryFromEventFlow (classifierBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S A R T G H C P N =>
      change
        some
          (ClassifierBoundaryUp.mk
            (classifierBoundaryDecodeBHist (classifierBoundaryEncodeBHist S))
            (classifierBoundaryDecodeBHist (classifierBoundaryEncodeBHist A))
            (classifierBoundaryDecodeBHist (classifierBoundaryEncodeBHist R))
            (classifierBoundaryDecodeBHist (classifierBoundaryEncodeBHist T))
            (classifierBoundaryDecodeBHist (classifierBoundaryEncodeBHist G))
            (classifierBoundaryDecodeBHist (classifierBoundaryEncodeBHist H))
            (classifierBoundaryDecodeBHist (classifierBoundaryEncodeBHist C))
            (classifierBoundaryDecodeBHist (classifierBoundaryEncodeBHist P))
            (classifierBoundaryDecodeBHist (classifierBoundaryEncodeBHist N))) =
          some (ClassifierBoundaryUp.mk S A R T G H C P N)
      rw [ClassifierBoundaryTasteGate_single_carrier_alignment_decode S,
        ClassifierBoundaryTasteGate_single_carrier_alignment_decode A,
        ClassifierBoundaryTasteGate_single_carrier_alignment_decode R,
        ClassifierBoundaryTasteGate_single_carrier_alignment_decode T,
        ClassifierBoundaryTasteGate_single_carrier_alignment_decode G,
        ClassifierBoundaryTasteGate_single_carrier_alignment_decode H,
        ClassifierBoundaryTasteGate_single_carrier_alignment_decode C,
        ClassifierBoundaryTasteGate_single_carrier_alignment_decode P,
        ClassifierBoundaryTasteGate_single_carrier_alignment_decode N]

private theorem ClassifierBoundaryTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ClassifierBoundaryUp} :
    classifierBoundaryToEventFlow x = classifierBoundaryToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      classifierBoundaryFromEventFlow (classifierBoundaryToEventFlow x) =
        classifierBoundaryFromEventFlow (classifierBoundaryToEventFlow y) :=
    congrArg classifierBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ClassifierBoundaryTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ClassifierBoundaryTasteGate_single_carrier_alignment_round_trip y)))

instance classifierBoundaryBHistCarrier : BHistCarrier ClassifierBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := classifierBoundaryToEventFlow
  fromEventFlow := classifierBoundaryFromEventFlow

instance classifierBoundaryChapterTasteGate : ChapterTasteGate ClassifierBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change classifierBoundaryFromEventFlow (classifierBoundaryToEventFlow x) = some x
    exact ClassifierBoundaryTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ClassifierBoundaryTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem ClassifierBoundaryTasteGate_single_carrier_alignment :
    (forall h : BHist, classifierBoundaryDecodeBHist (classifierBoundaryEncodeBHist h) = h) /\
      Nonempty (BHistCarrier ClassifierBoundaryUp) /\
        Nonempty (ChapterTasteGate ClassifierBoundaryUp) /\
          classifierBoundaryEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨ClassifierBoundaryTasteGate_single_carrier_alignment_decode,
      ⟨classifierBoundaryBHistCarrier⟩,
      ⟨classifierBoundaryChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.ClassifierBoundaryUp
