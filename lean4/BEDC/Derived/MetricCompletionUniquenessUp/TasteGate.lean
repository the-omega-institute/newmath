import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetricCompletionUniquenessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetricCompletionUniquenessUp : Type where
  | mk (M E0 F0 R0 S0 E1 F1 R1 S1 Q H C P N : BHist) :
      MetricCompletionUniquenessUp
  deriving DecidableEq

def metricCompletionUniquenessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metricCompletionUniquenessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metricCompletionUniquenessEncodeBHist h

def metricCompletionUniquenessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metricCompletionUniquenessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metricCompletionUniquenessDecodeBHist tail)

private theorem MetricCompletionUniquenessTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      metricCompletionUniquenessDecodeBHist
        (metricCompletionUniquenessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def metricCompletionUniquenessToEventFlow : MetricCompletionUniquenessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MetricCompletionUniquenessUp.mk M E0 F0 R0 S0 E1 F1 R1 S1 Q H C P N =>
      [[BMark.b0],
        metricCompletionUniquenessEncodeBHist M,
        [BMark.b1, BMark.b0],
        metricCompletionUniquenessEncodeBHist E0,
        [BMark.b1, BMark.b1, BMark.b0],
        metricCompletionUniquenessEncodeBHist F0,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metricCompletionUniquenessEncodeBHist R0,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metricCompletionUniquenessEncodeBHist S0,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metricCompletionUniquenessEncodeBHist E1,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metricCompletionUniquenessEncodeBHist F1,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        metricCompletionUniquenessEncodeBHist R1,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        metricCompletionUniquenessEncodeBHist S1,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        metricCompletionUniquenessEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metricCompletionUniquenessEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metricCompletionUniquenessEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metricCompletionUniquenessEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metricCompletionUniquenessEncodeBHist N]

def metricCompletionUniquenessFromEventFlow :
    EventFlow → Option MetricCompletionUniquenessUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tagM :: restM =>
      match restM with
      | [] => none
      | M :: restE0 =>
          match restE0 with
          | [] => none
          | _tagE0 :: restE0Row =>
              match restE0Row with
              | [] => none
              | E0 :: restF0 =>
                  match restF0 with
                  | [] => none
                  | _tagF0 :: restF0Row =>
                      match restF0Row with
                      | [] => none
                      | F0 :: restR0 =>
                          match restR0 with
                          | [] => none
                          | _tagR0 :: restR0Row =>
                              match restR0Row with
                              | [] => none
                              | R0 :: restS0 =>
                                  match restS0 with
                                  | [] => none
                                  | _tagS0 :: restS0Row =>
                                      match restS0Row with
                                      | [] => none
                                      | S0 :: restE1 =>
                                          match restE1 with
                                          | [] => none
                                          | _tagE1 :: restE1Row =>
                                              match restE1Row with
                                              | [] => none
                                              | E1 :: restF1 =>
                                                  match restF1 with
                                                  | [] => none
                                                  | _tagF1 :: restF1Row =>
                                                      match restF1Row with
                                                      | [] => none
                                                      | F1 :: restR1 =>
                                                          match restR1 with
                                                          | [] => none
                                                          | _tagR1 :: restR1Row =>
                                                              match restR1Row with
                                                              | [] => none
                                                              | R1 :: restS1 =>
                                                                  match restS1 with
                                                                  | [] => none
                                                                  | _tagS1 :: restS1Row =>
                                                                      match restS1Row with
                                                                      | [] => none
                                                                      | S1 :: restQ =>
                                                                          match restQ with
                                                                          | [] => none
                                                                          | _tagQ :: restQRow =>
                                                                              match restQRow with
                                                                              | [] => none
                                                                              | Q :: restH =>
                                                                                  match restH with
                                                                                  | [] => none
                                                                                  | _tagH :: restHRow =>
                                                                                      match restHRow with
                                                                                      | [] => none
                                                                                      | H :: restC =>
                                                                                          match restC with
                                                                                          | [] => none
                                                                                          | _tagC :: restCRow =>
                                                                                              match restCRow with
                                                                                              | [] => none
                                                                                              | C :: restP =>
                                                                                                  match restP with
                                                                                                  | [] => none
                                                                                                  | _tagP :: restPRow =>
                                                                                                      match restPRow with
                                                                                                      | [] => none
                                                                                                      | P :: restN =>
                                                                                                          match restN with
                                                                                                          | [] => none
                                                                                                          | _tagN :: restNRow =>
                                                                                                              match restNRow with
                                                                                                              | [] => none
                                                                                                              | N :: rest =>
                                                                                                                  match rest with
                                                                                                                  | [] =>
                                                                                                                      some
                                                                                                                        (MetricCompletionUniquenessUp.mk
                                                                                                                          (metricCompletionUniquenessDecodeBHist M)
                                                                                                                          (metricCompletionUniquenessDecodeBHist E0)
                                                                                                                          (metricCompletionUniquenessDecodeBHist F0)
                                                                                                                          (metricCompletionUniquenessDecodeBHist R0)
                                                                                                                          (metricCompletionUniquenessDecodeBHist S0)
                                                                                                                          (metricCompletionUniquenessDecodeBHist E1)
                                                                                                                          (metricCompletionUniquenessDecodeBHist F1)
                                                                                                                          (metricCompletionUniquenessDecodeBHist R1)
                                                                                                                          (metricCompletionUniquenessDecodeBHist S1)
                                                                                                                          (metricCompletionUniquenessDecodeBHist Q)
                                                                                                                          (metricCompletionUniquenessDecodeBHist H)
                                                                                                                          (metricCompletionUniquenessDecodeBHist C)
                                                                                                                          (metricCompletionUniquenessDecodeBHist P)
                                                                                                                          (metricCompletionUniquenessDecodeBHist N))
                                                                                                                  | _ :: _ => none

private theorem MetricCompletionUniquenessTasteGate_single_carrier_alignment_round_trip :
    ∀ x : MetricCompletionUniquenessUp,
      metricCompletionUniquenessFromEventFlow
        (metricCompletionUniquenessToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M E0 F0 R0 S0 E1 F1 R1 S1 Q H C P N =>
      change
        some
          (MetricCompletionUniquenessUp.mk
            (metricCompletionUniquenessDecodeBHist
              (metricCompletionUniquenessEncodeBHist M))
            (metricCompletionUniquenessDecodeBHist
              (metricCompletionUniquenessEncodeBHist E0))
            (metricCompletionUniquenessDecodeBHist
              (metricCompletionUniquenessEncodeBHist F0))
            (metricCompletionUniquenessDecodeBHist
              (metricCompletionUniquenessEncodeBHist R0))
            (metricCompletionUniquenessDecodeBHist
              (metricCompletionUniquenessEncodeBHist S0))
            (metricCompletionUniquenessDecodeBHist
              (metricCompletionUniquenessEncodeBHist E1))
            (metricCompletionUniquenessDecodeBHist
              (metricCompletionUniquenessEncodeBHist F1))
            (metricCompletionUniquenessDecodeBHist
              (metricCompletionUniquenessEncodeBHist R1))
            (metricCompletionUniquenessDecodeBHist
              (metricCompletionUniquenessEncodeBHist S1))
            (metricCompletionUniquenessDecodeBHist
              (metricCompletionUniquenessEncodeBHist Q))
            (metricCompletionUniquenessDecodeBHist
              (metricCompletionUniquenessEncodeBHist H))
            (metricCompletionUniquenessDecodeBHist
              (metricCompletionUniquenessEncodeBHist C))
            (metricCompletionUniquenessDecodeBHist
              (metricCompletionUniquenessEncodeBHist P))
            (metricCompletionUniquenessDecodeBHist
              (metricCompletionUniquenessEncodeBHist N))) =
          some (MetricCompletionUniquenessUp.mk M E0 F0 R0 S0 E1 F1 R1 S1 Q H C P N)
      rw [MetricCompletionUniquenessTasteGate_single_carrier_alignment_decode_encode M,
        MetricCompletionUniquenessTasteGate_single_carrier_alignment_decode_encode E0,
        MetricCompletionUniquenessTasteGate_single_carrier_alignment_decode_encode F0,
        MetricCompletionUniquenessTasteGate_single_carrier_alignment_decode_encode R0,
        MetricCompletionUniquenessTasteGate_single_carrier_alignment_decode_encode S0,
        MetricCompletionUniquenessTasteGate_single_carrier_alignment_decode_encode E1,
        MetricCompletionUniquenessTasteGate_single_carrier_alignment_decode_encode F1,
        MetricCompletionUniquenessTasteGate_single_carrier_alignment_decode_encode R1,
        MetricCompletionUniquenessTasteGate_single_carrier_alignment_decode_encode S1,
        MetricCompletionUniquenessTasteGate_single_carrier_alignment_decode_encode Q,
        MetricCompletionUniquenessTasteGate_single_carrier_alignment_decode_encode H,
        MetricCompletionUniquenessTasteGate_single_carrier_alignment_decode_encode C,
        MetricCompletionUniquenessTasteGate_single_carrier_alignment_decode_encode P,
        MetricCompletionUniquenessTasteGate_single_carrier_alignment_decode_encode N]

private theorem MetricCompletionUniquenessTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : MetricCompletionUniquenessUp} :
    metricCompletionUniquenessToEventFlow x =
      metricCompletionUniquenessToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metricCompletionUniquenessFromEventFlow
          (metricCompletionUniquenessToEventFlow x) =
        metricCompletionUniquenessFromEventFlow
          (metricCompletionUniquenessToEventFlow y) :=
    congrArg metricCompletionUniquenessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (MetricCompletionUniquenessTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (MetricCompletionUniquenessTasteGate_single_carrier_alignment_round_trip y)))

instance metricCompletionUniquenessBHistCarrier :
    BHistCarrier MetricCompletionUniquenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metricCompletionUniquenessToEventFlow
  fromEventFlow := metricCompletionUniquenessFromEventFlow

instance metricCompletionUniquenessChapterTasteGate :
    ChapterTasteGate MetricCompletionUniquenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metricCompletionUniquenessFromEventFlow
        (metricCompletionUniquenessToEventFlow x) = some x
    exact MetricCompletionUniquenessTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (MetricCompletionUniquenessTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate MetricCompletionUniquenessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metricCompletionUniquenessChapterTasteGate

theorem MetricCompletionUniquenessTasteGate_single_carrier_alignment :
    (∀ h : BHist, metricCompletionUniquenessDecodeBHist
      (metricCompletionUniquenessEncodeBHist h) = h) ∧
      (∀ x : MetricCompletionUniquenessUp,
        metricCompletionUniquenessFromEventFlow
          (metricCompletionUniquenessToEventFlow x) = some x) ∧
        (∀ x y : MetricCompletionUniquenessUp,
          metricCompletionUniquenessToEventFlow x =
            metricCompletionUniquenessToEventFlow y → x = y) ∧
          metricCompletionUniquenessEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨MetricCompletionUniquenessTasteGate_single_carrier_alignment_decode_encode,
      MetricCompletionUniquenessTasteGate_single_carrier_alignment_round_trip,
      fun _ _ heq =>
        MetricCompletionUniquenessTasteGate_single_carrier_alignment_toEventFlow_injective heq,
      rfl⟩

namespace TasteGate

def taste_gate : ChapterTasteGate MetricCompletionUniquenessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metricCompletionUniquenessChapterTasteGate

theorem MetricCompletionUniquenessTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate MetricCompletionUniquenessUp) ∧
      (∀ h : BHist,
        metricCompletionUniquenessDecodeBHist
          (metricCompletionUniquenessEncodeBHist h) = h) ∧
        (∀ x : MetricCompletionUniquenessUp,
          metricCompletionUniquenessFromEventFlow
            (metricCompletionUniquenessToEventFlow x) = some x) ∧
          (∀ x y : MetricCompletionUniquenessUp,
            metricCompletionUniquenessToEventFlow x =
              metricCompletionUniquenessToEventFlow y → x = y) ∧
            metricCompletionUniquenessEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨metricCompletionUniquenessChapterTasteGate⟩,
      BEDC.Derived.MetricCompletionUniquenessUp.MetricCompletionUniquenessTasteGate_single_carrier_alignment⟩

end TasteGate

end BEDC.Derived.MetricCompletionUniquenessUp
