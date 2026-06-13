import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyTransformUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyTransformUp : Type where
  | mk (S R M D U Q E H C P N : BHist) : RegularCauchyTransformUp
  deriving DecidableEq

def regularCauchyTransformEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyTransformEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyTransformEncodeBHist h

def regularCauchyTransformDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyTransformDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyTransformDecodeBHist tail)

private theorem regularCauchyTransform_decode_encode_bhist :
    forall h : BHist,
      regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def regularCauchyTransformFields : RegularCauchyTransformUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyTransformUp.mk S R M D U Q E H C P N =>
      [S, R, M, D, U, Q, E, H, C, P, N]

def regularCauchyTransformToEventFlow : RegularCauchyTransformUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (regularCauchyTransformFields x).map regularCauchyTransformEncodeBHist

inductive regularCauchyTransformReadStage : Type where
  -- BEDC touchpoint anchor: BHist BMark
  | row0
  | row1 (S : RawEvent)
  | row2 (S R : RawEvent)
  | row3 (S R M : RawEvent)
  | row4 (S R M D : RawEvent)
  | row5 (S R M D U : RawEvent)
  | row6 (S R M D U Q : RawEvent)
  | row7 (S R M D U Q E : RawEvent)
  | row8 (S R M D U Q E H : RawEvent)
  | row9 (S R M D U Q E H C : RawEvent)
  | row10 (S R M D U Q E H C P : RawEvent)
  | row11 (S R M D U Q E H C P N : RawEvent)

def regularCauchyTransformReadStep
    (stage : regularCauchyTransformReadStage) (row : RawEvent) :
    Option regularCauchyTransformReadStage := by
  -- BEDC touchpoint anchor: BHist BMark
  cases stage with
  | row0 =>
      exact some (regularCauchyTransformReadStage.row1 row)
  | row1 S =>
      exact some (regularCauchyTransformReadStage.row2 S row)
  | row2 S R =>
      exact some (regularCauchyTransformReadStage.row3 S R row)
  | row3 S R M =>
      exact some (regularCauchyTransformReadStage.row4 S R M row)
  | row4 S R M D =>
      exact some (regularCauchyTransformReadStage.row5 S R M D row)
  | row5 S R M D U =>
      exact some (regularCauchyTransformReadStage.row6 S R M D U row)
  | row6 S R M D U Q =>
      exact some (regularCauchyTransformReadStage.row7 S R M D U Q row)
  | row7 S R M D U Q E =>
      exact some (regularCauchyTransformReadStage.row8 S R M D U Q E row)
  | row8 S R M D U Q E H =>
      exact some (regularCauchyTransformReadStage.row9 S R M D U Q E H row)
  | row9 S R M D U Q E H C =>
      exact some (regularCauchyTransformReadStage.row10 S R M D U Q E H C row)
  | row10 S R M D U Q E H C P =>
      exact some (regularCauchyTransformReadStage.row11 S R M D U Q E H C P row)
  | row11 S R M D U Q E H C P N =>
      exact none

def regularCauchyTransformReadRows :
    EventFlow -> regularCauchyTransformReadStage -> Option regularCauchyTransformReadStage
  -- BEDC touchpoint anchor: BHist BMark
  | [], stage => some stage
  | row :: tail, stage =>
      match regularCauchyTransformReadStep stage row with
      | some stage' => regularCauchyTransformReadRows tail stage'
      | none => none

def regularCauchyTransformFinishRead
    (stage : regularCauchyTransformReadStage) :
    Option RegularCauchyTransformUp := by
  -- BEDC touchpoint anchor: BHist BMark
  cases stage with
  | row0 =>
      exact none
  | row1 S =>
      exact none
  | row2 S R =>
      exact none
  | row3 S R M =>
      exact none
  | row4 S R M D =>
      exact none
  | row5 S R M D U =>
      exact none
  | row6 S R M D U Q =>
      exact none
  | row7 S R M D U Q E =>
      exact none
  | row8 S R M D U Q E H =>
      exact none
  | row9 S R M D U Q E H C =>
      exact none
  | row10 S R M D U Q E H C P =>
      exact none
  | row11 S R M D U Q E H C P N =>
      exact
        some
          (RegularCauchyTransformUp.mk
            (regularCauchyTransformDecodeBHist S)
            (regularCauchyTransformDecodeBHist R)
            (regularCauchyTransformDecodeBHist M)
            (regularCauchyTransformDecodeBHist D)
            (regularCauchyTransformDecodeBHist U)
            (regularCauchyTransformDecodeBHist Q)
            (regularCauchyTransformDecodeBHist E)
            (regularCauchyTransformDecodeBHist H)
            (regularCauchyTransformDecodeBHist C)
            (regularCauchyTransformDecodeBHist P)
            (regularCauchyTransformDecodeBHist N))

def regularCauchyTransformFromEventFlow (ef : EventFlow) : Option RegularCauchyTransformUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match regularCauchyTransformReadRows ef regularCauchyTransformReadStage.row0 with
  | some stage => regularCauchyTransformFinishRead stage
  | none => none

private theorem regularCauchyTransform_round_trip :
    forall x : RegularCauchyTransformUp,
      regularCauchyTransformFromEventFlow (regularCauchyTransformToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S R M D U Q E H C P N =>
      change
        some
          (RegularCauchyTransformUp.mk
            (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist S))
            (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist R))
            (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist M))
            (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist D))
            (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist U))
            (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist Q))
            (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist E))
            (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist H))
            (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist C))
            (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist P))
            (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist N))) =
          some (RegularCauchyTransformUp.mk S R M D U Q E H C P N)
      apply congrArg some
      exact
        Eq.trans
          (congrArg
            (fun S' =>
              RegularCauchyTransformUp.mk S'
                (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist R))
                (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist M))
                (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist D))
                (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist U))
                (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist Q))
                (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist E))
                (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist H))
                (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist C))
                (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist P))
                (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist N)))
            (regularCauchyTransform_decode_encode_bhist S))
          (Eq.trans
            (congrArg
              (fun R' =>
                RegularCauchyTransformUp.mk S R'
                  (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist M))
                  (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist D))
                  (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist U))
                  (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist Q))
                  (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist E))
                  (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist H))
                  (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist C))
                  (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist P))
                  (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist N)))
              (regularCauchyTransform_decode_encode_bhist R))
            (Eq.trans
              (congrArg
                (fun M' =>
                  RegularCauchyTransformUp.mk S R M'
                    (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist D))
                    (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist U))
                    (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist Q))
                    (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist E))
                    (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist H))
                    (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist C))
                    (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist P))
                    (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist N)))
                (regularCauchyTransform_decode_encode_bhist M))
              (Eq.trans
                (congrArg
                  (fun D' =>
                    RegularCauchyTransformUp.mk S R M D'
                      (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist U))
                      (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist Q))
                      (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist E))
                      (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist H))
                      (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist C))
                      (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist P))
                      (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist N)))
                  (regularCauchyTransform_decode_encode_bhist D))
                (Eq.trans
                  (congrArg
                    (fun U' =>
                      RegularCauchyTransformUp.mk S R M D U'
                        (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist Q))
                        (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist E))
                        (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist H))
                        (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist C))
                        (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist P))
                        (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist N)))
                    (regularCauchyTransform_decode_encode_bhist U))
                  (Eq.trans
                    (congrArg
                      (fun Q' =>
                        RegularCauchyTransformUp.mk S R M D U Q'
                          (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist E))
                          (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist H))
                          (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist C))
                          (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist P))
                          (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist N)))
                      (regularCauchyTransform_decode_encode_bhist Q))
                    (Eq.trans
                      (congrArg
                        (fun E' =>
                          RegularCauchyTransformUp.mk S R M D U Q E'
                            (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist H))
                            (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist C))
                            (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist P))
                            (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist N)))
                        (regularCauchyTransform_decode_encode_bhist E))
                      (Eq.trans
                        (congrArg
                          (fun H' =>
                            RegularCauchyTransformUp.mk S R M D U Q E H'
                              (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist C))
                              (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist P))
                              (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist N)))
                          (regularCauchyTransform_decode_encode_bhist H))
                        (Eq.trans
                          (congrArg
                            (fun C' =>
                              RegularCauchyTransformUp.mk S R M D U Q E H C'
                                (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist P))
                                (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist N)))
                            (regularCauchyTransform_decode_encode_bhist C))
                          (Eq.trans
                            (congrArg
                              (fun P' =>
                                RegularCauchyTransformUp.mk S R M D U Q E H C P'
                                  (regularCauchyTransformDecodeBHist
                                    (regularCauchyTransformEncodeBHist N)))
                              (regularCauchyTransform_decode_encode_bhist P))
                            (congrArg
                              (fun N' => RegularCauchyTransformUp.mk S R M D U Q E H C P N')
                              (regularCauchyTransform_decode_encode_bhist N)))))))))))

private theorem regularCauchyTransformToEventFlow_injective
    {x y : RegularCauchyTransformUp} :
    regularCauchyTransformToEventFlow x = regularCauchyTransformToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyTransformFromEventFlow (regularCauchyTransformToEventFlow x) =
        regularCauchyTransformFromEventFlow (regularCauchyTransformToEventFlow y) :=
    congrArg regularCauchyTransformFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyTransform_round_trip x).symm
      (Eq.trans hread (regularCauchyTransform_round_trip y)))

private theorem regularCauchyTransform_field_faithful :
    forall x y : RegularCauchyTransformUp,
      regularCauchyTransformFields x = regularCauchyTransformFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S₁ R₁ M₁ D₁ U₁ Q₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk S₂ R₂ M₂ D₂ U₂ Q₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance regularCauchyTransformBHistCarrier : BHistCarrier RegularCauchyTransformUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyTransformToEventFlow
  fromEventFlow := regularCauchyTransformFromEventFlow

instance regularCauchyTransformChapterTasteGate :
    ChapterTasteGate RegularCauchyTransformUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := fun x =>
    id (regularCauchyTransform_round_trip x)
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyTransformToEventFlow_injective heq)

instance regularCauchyTransformFieldFaithful : FieldFaithful RegularCauchyTransformUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyTransformFields
  field_faithful := regularCauchyTransform_field_faithful

instance regularCauchyTransformNontrivial :
    BEDC.Meta.TasteGate.Nontrivial RegularCauchyTransformUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyTransformUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RegularCauchyTransformUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def regularCauchyTransformTasteGate : ChapterTasteGate RegularCauchyTransformUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyTransformChapterTasteGate

theorem RegularCauchyTransformTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

theorem RegularCauchyTransformTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularCauchyTransformUp,
      regularCauchyTransformFromEventFlow (regularCauchyTransformToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S R M D U Q E H C P N =>
      change
        some
          (RegularCauchyTransformUp.mk
            (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist S))
            (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist R))
            (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist M))
            (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist D))
            (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist U))
            (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist Q))
            (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist E))
            (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist H))
            (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist C))
            (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist P))
            (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist N))) =
          some (RegularCauchyTransformUp.mk S R M D U Q E H C P N)
      apply congrArg some
      exact
        Eq.trans
          (congrArg
            (fun S' =>
              RegularCauchyTransformUp.mk S'
                (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist R))
                (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist M))
                (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist D))
                (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist U))
                (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist Q))
                (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist E))
                (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist H))
                (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist C))
                (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist P))
                (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist N)))
            (RegularCauchyTransformTasteGate_single_carrier_alignment_decode_encode S))
          (Eq.trans
            (congrArg
              (fun R' =>
                RegularCauchyTransformUp.mk S R'
                  (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist M))
                  (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist D))
                  (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist U))
                  (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist Q))
                  (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist E))
                  (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist H))
                  (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist C))
                  (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist P))
                  (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist N)))
              (RegularCauchyTransformTasteGate_single_carrier_alignment_decode_encode R))
            (Eq.trans
              (congrArg
                (fun M' =>
                  RegularCauchyTransformUp.mk S R M'
                    (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist D))
                    (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist U))
                    (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist Q))
                    (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist E))
                    (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist H))
                    (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist C))
                    (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist P))
                    (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist N)))
                (RegularCauchyTransformTasteGate_single_carrier_alignment_decode_encode M))
              (Eq.trans
                (congrArg
                  (fun D' =>
                    RegularCauchyTransformUp.mk S R M D'
                      (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist U))
                      (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist Q))
                      (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist E))
                      (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist H))
                      (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist C))
                      (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist P))
                      (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist N)))
                  (RegularCauchyTransformTasteGate_single_carrier_alignment_decode_encode D))
                (Eq.trans
                  (congrArg
                    (fun U' =>
                      RegularCauchyTransformUp.mk S R M D U'
                        (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist Q))
                        (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist E))
                        (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist H))
                        (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist C))
                        (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist P))
                        (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist N)))
                    (RegularCauchyTransformTasteGate_single_carrier_alignment_decode_encode U))
                  (Eq.trans
                    (congrArg
                      (fun Q' =>
                        RegularCauchyTransformUp.mk S R M D U Q'
                          (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist E))
                          (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist H))
                          (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist C))
                          (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist P))
                          (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist N)))
                      (RegularCauchyTransformTasteGate_single_carrier_alignment_decode_encode Q))
                    (Eq.trans
                      (congrArg
                        (fun E' =>
                          RegularCauchyTransformUp.mk S R M D U Q E'
                            (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist H))
                            (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist C))
                            (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist P))
                            (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist N)))
                        (RegularCauchyTransformTasteGate_single_carrier_alignment_decode_encode E))
                      (Eq.trans
                        (congrArg
                          (fun H' =>
                            RegularCauchyTransformUp.mk S R M D U Q E H'
                              (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist C))
                              (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist P))
                              (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist N)))
                          (RegularCauchyTransformTasteGate_single_carrier_alignment_decode_encode H))
                        (Eq.trans
                          (congrArg
                            (fun C' =>
                              RegularCauchyTransformUp.mk S R M D U Q E H C'
                                (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist P))
                                (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist N)))
                            (RegularCauchyTransformTasteGate_single_carrier_alignment_decode_encode C))
                          (Eq.trans
                            (congrArg
                              (fun P' =>
                                RegularCauchyTransformUp.mk S R M D U Q E H C P'
                                  (regularCauchyTransformDecodeBHist
                                    (regularCauchyTransformEncodeBHist N)))
                              (RegularCauchyTransformTasteGate_single_carrier_alignment_decode_encode P))
                            (congrArg
                              (fun N' => RegularCauchyTransformUp.mk S R M D U Q E H C P N')
                              (RegularCauchyTransformTasteGate_single_carrier_alignment_decode_encode N)))))))))))

theorem RegularCauchyTransformTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : RegularCauchyTransformUp,
      regularCauchyTransformFields x = regularCauchyTransformFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S₁ R₁ M₁ D₁ U₁ Q₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk S₂ R₂ M₂ D₂ U₂ Q₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

theorem RegularCauchyTransformTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchyTransformUp} :
    regularCauchyTransformToEventFlow x = regularCauchyTransformToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyTransformFromEventFlow (regularCauchyTransformToEventFlow x) =
        regularCauchyTransformFromEventFlow (regularCauchyTransformToEventFlow y) :=
    congrArg regularCauchyTransformFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RegularCauchyTransformTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RegularCauchyTransformTasteGate_single_carrier_alignment_round_trip y)))

theorem RegularCauchyTransformTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyTransformUp,
        regularCauchyTransformFromEventFlow (regularCauchyTransformToEventFlow x) = some x) ∧
        (∀ x y : RegularCauchyTransformUp,
          regularCauchyTransformFields x = regularCauchyTransformFields y -> x = y) ∧
          (∀ x y : RegularCauchyTransformUp,
            regularCauchyTransformToEventFlow x = regularCauchyTransformToEventFlow y -> x = y) :=
  by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact RegularCauchyTransformTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact RegularCauchyTransformTasteGate_single_carrier_alignment_round_trip
    · constructor
      · exact RegularCauchyTransformTasteGate_single_carrier_alignment_field_faithful
      · intro x y heq
        exact RegularCauchyTransformTasteGate_single_carrier_alignment_toEventFlow_injective heq

end BEDC.Derived.RegularCauchyTransformUp.TasteGate
