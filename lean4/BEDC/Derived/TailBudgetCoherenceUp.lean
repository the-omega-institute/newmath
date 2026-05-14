import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TailBudgetCoherenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TailBudgetCoherenceUp : Type where
  | mk :
      (tailMeet observationBudget selectorBudget agreementSeal limitSeal window readback
        dyadicTolerance transport route provenance nameCert : BHist) →
        TailBudgetCoherenceUp
  deriving DecidableEq

def tailBudgetCoherenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: tailBudgetCoherenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: tailBudgetCoherenceEncodeBHist h

def tailBudgetCoherenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (tailBudgetCoherenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (tailBudgetCoherenceDecodeBHist tail)

private theorem TailBudgetCoherenceTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      tailBudgetCoherenceDecodeBHist (tailBudgetCoherenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def tailBudgetCoherenceToEventFlow : TailBudgetCoherenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | TailBudgetCoherenceUp.mk tailMeet observationBudget selectorBudget agreementSeal limitSeal
      window readback dyadicTolerance transport route provenance nameCert =>
      [[BMark.b0],
        tailBudgetCoherenceEncodeBHist tailMeet,
        [BMark.b1, BMark.b0],
        tailBudgetCoherenceEncodeBHist observationBudget,
        [BMark.b1, BMark.b1, BMark.b0],
        tailBudgetCoherenceEncodeBHist selectorBudget,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        tailBudgetCoherenceEncodeBHist agreementSeal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        tailBudgetCoherenceEncodeBHist limitSeal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        tailBudgetCoherenceEncodeBHist window,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        tailBudgetCoherenceEncodeBHist readback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        tailBudgetCoherenceEncodeBHist dyadicTolerance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        tailBudgetCoherenceEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        tailBudgetCoherenceEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        tailBudgetCoherenceEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        tailBudgetCoherenceEncodeBHist nameCert]

def tailBudgetCoherenceFromEventFlow : EventFlow → Option TailBudgetCoherenceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | tailMeet :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | observationBudget :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | selectorBudget :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | agreementSeal :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | limitSeal :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | window :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | readback :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | dyadicTolerance ::
                                                                  rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 ::
                                                                      rest16 =>
                                                                      match rest16
                                                                      with
                                                                      | [] => none
                                                                      | transport ::
                                                                          rest17 =>
                                                                          match
                                                                            rest17
                                                                          with
                                                                          | [] =>
                                                                              none
                                                                          | _tag9 ::
                                                                              rest18 =>
                                                                              match
                                                                                rest18
                                                                              with
                                                                              | [] =>
                                                                                  none
                                                                              | route ::
                                                                                  rest19 =>
                                                                                  match
                                                                                    rest19
                                                                                  with
                                                                                  | [] =>
                                                                                      none
                                                                                  | _tag10 ::
                                                                                      rest20 =>
                                                                                      match
                                                                                        rest20
                                                                                      with
                                                                                      | [] =>
                                                                                          none
                                                                                      | provenance ::
                                                                                          rest21 =>
                                                                                          match
                                                                                            rest21
                                                                                          with
                                                                                          | [] =>
                                                                                              none
                                                                                          | _tag11 ::
                                                                                              rest22 =>
                                                                                              match
                                                                                                rest22
                                                                                              with
                                                                                              | [] =>
                                                                                                  none
                                                                                              | nameCert ::
                                                                                                  rest23 =>
                                                                                                  match
                                                                                                    rest23
                                                                                                  with
                                                                                                  | [] =>
                                                                                                      some
                                                                                                        (TailBudgetCoherenceUp.mk
                                                                                                          (tailBudgetCoherenceDecodeBHist
                                                                                                            tailMeet)
                                                                                                          (tailBudgetCoherenceDecodeBHist
                                                                                                            observationBudget)
                                                                                                          (tailBudgetCoherenceDecodeBHist
                                                                                                            selectorBudget)
                                                                                                          (tailBudgetCoherenceDecodeBHist
                                                                                                            agreementSeal)
                                                                                                          (tailBudgetCoherenceDecodeBHist
                                                                                                            limitSeal)
                                                                                                          (tailBudgetCoherenceDecodeBHist
                                                                                                            window)
                                                                                                          (tailBudgetCoherenceDecodeBHist
                                                                                                            readback)
                                                                                                          (tailBudgetCoherenceDecodeBHist
                                                                                                            dyadicTolerance)
                                                                                                          (tailBudgetCoherenceDecodeBHist
                                                                                                            transport)
                                                                                                          (tailBudgetCoherenceDecodeBHist
                                                                                                            route)
                                                                                                          (tailBudgetCoherenceDecodeBHist
                                                                                                            provenance)
                                                                                                          (tailBudgetCoherenceDecodeBHist
                                                                                                            nameCert))
                                                                                                  | _ ::
                                                                                                      _ =>
                                                                                                      none

private theorem TailBudgetCoherenceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : TailBudgetCoherenceUp,
      tailBudgetCoherenceFromEventFlow (tailBudgetCoherenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk tailMeet observationBudget selectorBudget agreementSeal limitSeal window readback
      dyadicTolerance transport route provenance nameCert =>
      change
        some
          (TailBudgetCoherenceUp.mk
            (tailBudgetCoherenceDecodeBHist (tailBudgetCoherenceEncodeBHist tailMeet))
            (tailBudgetCoherenceDecodeBHist
              (tailBudgetCoherenceEncodeBHist observationBudget))
            (tailBudgetCoherenceDecodeBHist
              (tailBudgetCoherenceEncodeBHist selectorBudget))
            (tailBudgetCoherenceDecodeBHist (tailBudgetCoherenceEncodeBHist agreementSeal))
            (tailBudgetCoherenceDecodeBHist (tailBudgetCoherenceEncodeBHist limitSeal))
            (tailBudgetCoherenceDecodeBHist (tailBudgetCoherenceEncodeBHist window))
            (tailBudgetCoherenceDecodeBHist (tailBudgetCoherenceEncodeBHist readback))
            (tailBudgetCoherenceDecodeBHist
              (tailBudgetCoherenceEncodeBHist dyadicTolerance))
            (tailBudgetCoherenceDecodeBHist (tailBudgetCoherenceEncodeBHist transport))
            (tailBudgetCoherenceDecodeBHist (tailBudgetCoherenceEncodeBHist route))
            (tailBudgetCoherenceDecodeBHist (tailBudgetCoherenceEncodeBHist provenance))
            (tailBudgetCoherenceDecodeBHist (tailBudgetCoherenceEncodeBHist nameCert))) =
          some
            (TailBudgetCoherenceUp.mk tailMeet observationBudget selectorBudget agreementSeal
              limitSeal window readback dyadicTolerance transport route provenance nameCert)
      rw [TailBudgetCoherenceTasteGate_single_carrier_alignment_decode tailMeet,
        TailBudgetCoherenceTasteGate_single_carrier_alignment_decode observationBudget,
        TailBudgetCoherenceTasteGate_single_carrier_alignment_decode selectorBudget,
        TailBudgetCoherenceTasteGate_single_carrier_alignment_decode agreementSeal,
        TailBudgetCoherenceTasteGate_single_carrier_alignment_decode limitSeal,
        TailBudgetCoherenceTasteGate_single_carrier_alignment_decode window,
        TailBudgetCoherenceTasteGate_single_carrier_alignment_decode readback,
        TailBudgetCoherenceTasteGate_single_carrier_alignment_decode dyadicTolerance,
        TailBudgetCoherenceTasteGate_single_carrier_alignment_decode transport,
        TailBudgetCoherenceTasteGate_single_carrier_alignment_decode route,
        TailBudgetCoherenceTasteGate_single_carrier_alignment_decode provenance,
        TailBudgetCoherenceTasteGate_single_carrier_alignment_decode nameCert]

private theorem TailBudgetCoherenceTasteGate_single_carrier_alignment_injective
    {x y : TailBudgetCoherenceUp} :
    tailBudgetCoherenceToEventFlow x =
      tailBudgetCoherenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      tailBudgetCoherenceFromEventFlow (tailBudgetCoherenceToEventFlow x) =
        tailBudgetCoherenceFromEventFlow (tailBudgetCoherenceToEventFlow y) :=
    congrArg tailBudgetCoherenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (TailBudgetCoherenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (TailBudgetCoherenceTasteGate_single_carrier_alignment_round_trip y)))

instance tailBudgetCoherenceBHistCarrier : BHistCarrier TailBudgetCoherenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := tailBudgetCoherenceToEventFlow
  fromEventFlow := tailBudgetCoherenceFromEventFlow

instance tailBudgetCoherenceChapterTasteGate : ChapterTasteGate TailBudgetCoherenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change tailBudgetCoherenceFromEventFlow (tailBudgetCoherenceToEventFlow x) = some x
    exact TailBudgetCoherenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (TailBudgetCoherenceTasteGate_single_carrier_alignment_injective heq)

theorem TailBudgetCoherenceTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier TailBudgetCoherenceUp) ∧
      Nonempty (ChapterTasteGate TailBudgetCoherenceUp) ∧
      (∀ h : BHist, tailBudgetCoherenceDecodeBHist (tailBudgetCoherenceEncodeBHist h) = h) ∧
      tailBudgetCoherenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨tailBudgetCoherenceBHistCarrier⟩
  · constructor
    · exact ⟨tailBudgetCoherenceChapterTasteGate⟩
    · constructor
      · exact TailBudgetCoherenceTasteGate_single_carrier_alignment_decode
      · rfl

end BEDC.Derived.TailBudgetCoherenceUp
