import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ArchimedeanApproximationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ArchimedeanApproximationUp : Type where
  | mk (N Q D epsilon S R E H C P M : BHist) : ArchimedeanApproximationUp
  deriving DecidableEq

def archimedeanApproximationEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: archimedeanApproximationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: archimedeanApproximationEncodeBHist h

def archimedeanApproximationDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (archimedeanApproximationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (archimedeanApproximationDecodeBHist tail)

private theorem ArchimedeanApproximationTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      archimedeanApproximationDecodeBHist (archimedeanApproximationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def archimedeanApproximationToEventFlow : ArchimedeanApproximationUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ArchimedeanApproximationUp.mk N Q D epsilon S R E H C P M =>
      [archimedeanApproximationEncodeBHist N,
        archimedeanApproximationEncodeBHist Q,
        archimedeanApproximationEncodeBHist D,
        archimedeanApproximationEncodeBHist epsilon,
        archimedeanApproximationEncodeBHist S,
        archimedeanApproximationEncodeBHist R,
        archimedeanApproximationEncodeBHist E,
        archimedeanApproximationEncodeBHist H,
        archimedeanApproximationEncodeBHist C,
        archimedeanApproximationEncodeBHist P,
        archimedeanApproximationEncodeBHist M]

def archimedeanApproximationFromEventFlow : EventFlow -> Option ArchimedeanApproximationUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | N :: rest0 =>
      match rest0 with
      | [] => none
      | Q :: rest1 =>
          match rest1 with
          | [] => none
          | D :: rest2 =>
              match rest2 with
              | [] => none
              | epsilon :: rest3 =>
                  match rest3 with
                  | [] => none
                  | S :: rest4 =>
                      match rest4 with
                      | [] => none
                      | R :: rest5 =>
                          match rest5 with
                          | [] => none
                          | E :: rest6 =>
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
                                          | M :: rest10 =>
                                              match rest10 with
                                              | [] =>
                                                  some
                                                    (ArchimedeanApproximationUp.mk
                                                      (archimedeanApproximationDecodeBHist N)
                                                      (archimedeanApproximationDecodeBHist Q)
                                                      (archimedeanApproximationDecodeBHist D)
                                                      (archimedeanApproximationDecodeBHist epsilon)
                                                      (archimedeanApproximationDecodeBHist S)
                                                      (archimedeanApproximationDecodeBHist R)
                                                      (archimedeanApproximationDecodeBHist E)
                                                      (archimedeanApproximationDecodeBHist H)
                                                      (archimedeanApproximationDecodeBHist C)
                                                      (archimedeanApproximationDecodeBHist P)
                                                      (archimedeanApproximationDecodeBHist M))
                                              | _ :: _ => none

private theorem ArchimedeanApproximationTasteGate_single_carrier_alignment_round_trip :
    forall x : ArchimedeanApproximationUp,
      archimedeanApproximationFromEventFlow
        (archimedeanApproximationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk N Q D epsilon S R E H C P M =>
      change
        some
          (ArchimedeanApproximationUp.mk
            (archimedeanApproximationDecodeBHist (archimedeanApproximationEncodeBHist N))
            (archimedeanApproximationDecodeBHist (archimedeanApproximationEncodeBHist Q))
            (archimedeanApproximationDecodeBHist (archimedeanApproximationEncodeBHist D))
            (archimedeanApproximationDecodeBHist
              (archimedeanApproximationEncodeBHist epsilon))
            (archimedeanApproximationDecodeBHist (archimedeanApproximationEncodeBHist S))
            (archimedeanApproximationDecodeBHist (archimedeanApproximationEncodeBHist R))
            (archimedeanApproximationDecodeBHist (archimedeanApproximationEncodeBHist E))
            (archimedeanApproximationDecodeBHist (archimedeanApproximationEncodeBHist H))
            (archimedeanApproximationDecodeBHist (archimedeanApproximationEncodeBHist C))
            (archimedeanApproximationDecodeBHist (archimedeanApproximationEncodeBHist P))
            (archimedeanApproximationDecodeBHist (archimedeanApproximationEncodeBHist M))) =
          some (ArchimedeanApproximationUp.mk N Q D epsilon S R E H C P M)
      rw [ArchimedeanApproximationTasteGate_single_carrier_alignment_decode N,
        ArchimedeanApproximationTasteGate_single_carrier_alignment_decode Q,
        ArchimedeanApproximationTasteGate_single_carrier_alignment_decode D,
        ArchimedeanApproximationTasteGate_single_carrier_alignment_decode epsilon,
        ArchimedeanApproximationTasteGate_single_carrier_alignment_decode S,
        ArchimedeanApproximationTasteGate_single_carrier_alignment_decode R,
        ArchimedeanApproximationTasteGate_single_carrier_alignment_decode E,
        ArchimedeanApproximationTasteGate_single_carrier_alignment_decode H,
        ArchimedeanApproximationTasteGate_single_carrier_alignment_decode C,
        ArchimedeanApproximationTasteGate_single_carrier_alignment_decode P,
        ArchimedeanApproximationTasteGate_single_carrier_alignment_decode M]

private theorem ArchimedeanApproximationTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ArchimedeanApproximationUp} :
    archimedeanApproximationToEventFlow x =
        archimedeanApproximationToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      archimedeanApproximationFromEventFlow (archimedeanApproximationToEventFlow x) =
        archimedeanApproximationFromEventFlow (archimedeanApproximationToEventFlow y) :=
    congrArg archimedeanApproximationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ArchimedeanApproximationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ArchimedeanApproximationTasteGate_single_carrier_alignment_round_trip y)))

instance archimedeanApproximationBHistCarrier :
    BHistCarrier ArchimedeanApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := archimedeanApproximationToEventFlow
  fromEventFlow := archimedeanApproximationFromEventFlow

instance archimedeanApproximationChapterTasteGate :
    ChapterTasteGate ArchimedeanApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      archimedeanApproximationFromEventFlow
        (archimedeanApproximationToEventFlow x) = some x
    exact ArchimedeanApproximationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ArchimedeanApproximationTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem ArchimedeanApproximationTasteGate_single_carrier_alignment :
    (forall h : BHist,
      archimedeanApproximationDecodeBHist (archimedeanApproximationEncodeBHist h) = h) /\
      Nonempty (BHistCarrier ArchimedeanApproximationUp) /\
        Nonempty (ChapterTasteGate ArchimedeanApproximationUp) /\
          archimedeanApproximationEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨ArchimedeanApproximationTasteGate_single_carrier_alignment_decode,
      ⟨archimedeanApproximationBHistCarrier⟩,
      ⟨archimedeanApproximationChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.ArchimedeanApproximationUp
