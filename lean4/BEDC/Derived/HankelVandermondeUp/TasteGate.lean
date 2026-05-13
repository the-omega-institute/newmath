import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

/-!
# HankelVandermondeUp TasteGate carrier.
-/

namespace BEDC.Derived.HankelVandermondeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

/-- Finite Hankel-Vandermonde packet with the ten BEDC rows visible to consumers. -/
inductive HankelVandermondeUp : Type where
  | mk :
      (atom weight moment determinantLedger pairwiseDifference vandermondeSquare transportRow
        routeRow provenance cert : BHist) →
      HankelVandermondeUp
  deriving DecidableEq

def hankelVandermondeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hankelVandermondeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hankelVandermondeEncodeBHist h

def hankelVandermondeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hankelVandermondeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hankelVandermondeDecodeBHist tail)

private theorem hankelVandermondeDecode_encode_bhist :
    ∀ h : BHist, hankelVandermondeDecodeBHist (hankelVandermondeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def hankelVandermondeToEventFlow : HankelVandermondeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | HankelVandermondeUp.mk atom weight moment determinantLedger pairwiseDifference
      vandermondeSquare transportRow routeRow provenance cert =>
      [[BMark.b0],
        hankelVandermondeEncodeBHist atom,
        [BMark.b1, BMark.b0],
        hankelVandermondeEncodeBHist weight,
        [BMark.b1, BMark.b1, BMark.b0],
        hankelVandermondeEncodeBHist moment,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        hankelVandermondeEncodeBHist determinantLedger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        hankelVandermondeEncodeBHist pairwiseDifference,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        hankelVandermondeEncodeBHist vandermondeSquare,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        hankelVandermondeEncodeBHist transportRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        hankelVandermondeEncodeBHist routeRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        hankelVandermondeEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        hankelVandermondeEncodeBHist cert]

def hankelVandermondeFromEventFlow : EventFlow → Option HankelVandermondeUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | atom :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | weight :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | moment :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | determinantLedger :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | pairwiseDifference :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | vandermondeSquare :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | transportRow :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | routeRow :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | provenance :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | cert :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] =>
                                                                                      some
                                                                                        (HankelVandermondeUp.mk
                                                                                          (hankelVandermondeDecodeBHist
                                                                                            atom)
                                                                                          (hankelVandermondeDecodeBHist
                                                                                            weight)
                                                                                          (hankelVandermondeDecodeBHist
                                                                                            moment)
                                                                                          (hankelVandermondeDecodeBHist
                                                                                            determinantLedger)
                                                                                          (hankelVandermondeDecodeBHist
                                                                                            pairwiseDifference)
                                                                                          (hankelVandermondeDecodeBHist
                                                                                            vandermondeSquare)
                                                                                          (hankelVandermondeDecodeBHist
                                                                                            transportRow)
                                                                                          (hankelVandermondeDecodeBHist
                                                                                            routeRow)
                                                                                          (hankelVandermondeDecodeBHist
                                                                                            provenance)
                                                                                          (hankelVandermondeDecodeBHist
                                                                                            cert))
                                                                                  | _ :: _ => none

private theorem hankelVandermonde_round_trip :
    ∀ x : HankelVandermondeUp,
      hankelVandermondeFromEventFlow (hankelVandermondeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk atom weight moment determinantLedger pairwiseDifference vandermondeSquare transportRow
      routeRow provenance cert =>
      change
        some
          (HankelVandermondeUp.mk
            (hankelVandermondeDecodeBHist (hankelVandermondeEncodeBHist atom))
            (hankelVandermondeDecodeBHist (hankelVandermondeEncodeBHist weight))
            (hankelVandermondeDecodeBHist (hankelVandermondeEncodeBHist moment))
            (hankelVandermondeDecodeBHist
              (hankelVandermondeEncodeBHist determinantLedger))
            (hankelVandermondeDecodeBHist
              (hankelVandermondeEncodeBHist pairwiseDifference))
            (hankelVandermondeDecodeBHist
              (hankelVandermondeEncodeBHist vandermondeSquare))
            (hankelVandermondeDecodeBHist (hankelVandermondeEncodeBHist transportRow))
            (hankelVandermondeDecodeBHist (hankelVandermondeEncodeBHist routeRow))
            (hankelVandermondeDecodeBHist (hankelVandermondeEncodeBHist provenance))
            (hankelVandermondeDecodeBHist (hankelVandermondeEncodeBHist cert))) =
          some
            (HankelVandermondeUp.mk atom weight moment determinantLedger pairwiseDifference
              vandermondeSquare transportRow routeRow provenance cert)
      rw [hankelVandermondeDecode_encode_bhist atom,
        hankelVandermondeDecode_encode_bhist weight,
        hankelVandermondeDecode_encode_bhist moment,
        hankelVandermondeDecode_encode_bhist determinantLedger,
        hankelVandermondeDecode_encode_bhist pairwiseDifference,
        hankelVandermondeDecode_encode_bhist vandermondeSquare,
        hankelVandermondeDecode_encode_bhist transportRow,
        hankelVandermondeDecode_encode_bhist routeRow,
        hankelVandermondeDecode_encode_bhist provenance,
        hankelVandermondeDecode_encode_bhist cert]

private theorem hankelVandermondeToEventFlow_injective {x y : HankelVandermondeUp} :
    hankelVandermondeToEventFlow x = hankelVandermondeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hankelVandermondeFromEventFlow (hankelVandermondeToEventFlow x) =
        hankelVandermondeFromEventFlow (hankelVandermondeToEventFlow y) :=
    congrArg hankelVandermondeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (hankelVandermonde_round_trip x).symm
      (Eq.trans hread (hankelVandermonde_round_trip y)))

instance hankelVandermondeBHistCarrier : BHistCarrier HankelVandermondeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hankelVandermondeToEventFlow
  fromEventFlow := hankelVandermondeFromEventFlow

instance hankelVandermondeChapterTasteGate : ChapterTasteGate HankelVandermondeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change hankelVandermondeFromEventFlow (hankelVandermondeToEventFlow x) = some x
    exact hankelVandermonde_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (hankelVandermondeToEventFlow_injective heq)

def taste_gate : ChapterTasteGate HankelVandermondeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  hankelVandermondeChapterTasteGate

theorem HankelVandermondeTasteGate_single_carrier_alignment :
    (∀ h : BHist, hankelVandermondeDecodeBHist (hankelVandermondeEncodeBHist h) = h) ∧
      (∀ x : HankelVandermondeUp,
        hankelVandermondeFromEventFlow (hankelVandermondeToEventFlow x) = some x) ∧
        (∀ x y : HankelVandermondeUp,
          hankelVandermondeToEventFlow x = hankelVandermondeToEventFlow y → x = y) ∧
          hankelVandermondeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact hankelVandermondeDecode_encode_bhist
  · constructor
    · exact hankelVandermonde_round_trip
    · constructor
      · intro x y heq
        exact hankelVandermondeToEventFlow_injective heq
      · rfl

theorem HankelVandermondeCarrier_namecert_obligations :
    (forall x : HankelVandermondeUp,
      hankelVandermondeFromEventFlow (BHistCarrier.toEventFlow x) = some x) /\
      (forall x y : HankelVandermondeUp,
        BHistCarrier.toEventFlow x = BHistCarrier.toEventFlow y -> x = y) /\
        (forall (x : HankelVandermondeUp) w m, List.Mem w (BHistCarrier.toEventFlow x) ->
          List.Mem m w -> m = BMark.b0 \/ m = BMark.b1) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro x
    change hankelVandermondeFromEventFlow (hankelVandermondeToEventFlow x) = some x
    exact hankelVandermonde_round_trip x
  · constructor
    · intro x y heq
      change hankelVandermondeToEventFlow x = hankelVandermondeToEventFlow y at heq
      exact hankelVandermondeToEventFlow_injective heq
    · intro x w m hw hm
      exact ChapterTasteGate.conservativity x w m hw hm

end BEDC.Derived.HankelVandermondeUp
