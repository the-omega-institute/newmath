import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SchurOrthogonalityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SchurOrthogonalityUp : Type where
  | mk (G V X Phi Omega H C P N : BHist) : SchurOrthogonalityUp
  deriving DecidableEq

def schurOrthogonalityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: schurOrthogonalityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: schurOrthogonalityEncodeBHist h

def schurOrthogonalityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (schurOrthogonalityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (schurOrthogonalityDecodeBHist tail)

private theorem schurOrthogonality_decode_encode_bhist :
    ∀ h : BHist,
      schurOrthogonalityDecodeBHist (schurOrthogonalityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def schurOrthogonalityToEventFlow : SchurOrthogonalityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | SchurOrthogonalityUp.mk G V X Phi Omega H C P N =>
      [[BMark.b0],
        schurOrthogonalityEncodeBHist G,
        [BMark.b1, BMark.b0],
        schurOrthogonalityEncodeBHist V,
        [BMark.b1, BMark.b1, BMark.b0],
        schurOrthogonalityEncodeBHist X,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        schurOrthogonalityEncodeBHist Phi,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        schurOrthogonalityEncodeBHist Omega,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        schurOrthogonalityEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        schurOrthogonalityEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        schurOrthogonalityEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        schurOrthogonalityEncodeBHist N]

def schurOrthogonalityFromEventFlow : EventFlow → Option SchurOrthogonalityUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | G :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | V :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | X :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | Phi :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | Omega :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | H :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | C :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | P :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | N ::
                                                                          rest17 =>
                                                                          match
                                                                            rest17
                                                                          with
                                                                          | [] =>
                                                                              some
                                                                                (SchurOrthogonalityUp.mk
                                                                                  (schurOrthogonalityDecodeBHist
                                                                                    G)
                                                                                  (schurOrthogonalityDecodeBHist
                                                                                    V)
                                                                                  (schurOrthogonalityDecodeBHist
                                                                                    X)
                                                                                  (schurOrthogonalityDecodeBHist
                                                                                    Phi)
                                                                                  (schurOrthogonalityDecodeBHist
                                                                                    Omega)
                                                                                  (schurOrthogonalityDecodeBHist
                                                                                    H)
                                                                                  (schurOrthogonalityDecodeBHist
                                                                                    C)
                                                                                  (schurOrthogonalityDecodeBHist
                                                                                    P)
                                                                                  (schurOrthogonalityDecodeBHist
                                                                                    N))
                                                                          | _ :: _ =>
                                                                              none

private theorem schurOrthogonality_round_trip :
    ∀ x : SchurOrthogonalityUp,
      schurOrthogonalityFromEventFlow (schurOrthogonalityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk G V X Phi Omega H C P N =>
      change
        some
          (SchurOrthogonalityUp.mk
            (schurOrthogonalityDecodeBHist (schurOrthogonalityEncodeBHist G))
            (schurOrthogonalityDecodeBHist (schurOrthogonalityEncodeBHist V))
            (schurOrthogonalityDecodeBHist (schurOrthogonalityEncodeBHist X))
            (schurOrthogonalityDecodeBHist (schurOrthogonalityEncodeBHist Phi))
            (schurOrthogonalityDecodeBHist (schurOrthogonalityEncodeBHist Omega))
            (schurOrthogonalityDecodeBHist (schurOrthogonalityEncodeBHist H))
            (schurOrthogonalityDecodeBHist (schurOrthogonalityEncodeBHist C))
            (schurOrthogonalityDecodeBHist (schurOrthogonalityEncodeBHist P))
            (schurOrthogonalityDecodeBHist (schurOrthogonalityEncodeBHist N))) =
          some (SchurOrthogonalityUp.mk G V X Phi Omega H C P N)
      rw [schurOrthogonality_decode_encode_bhist G,
        schurOrthogonality_decode_encode_bhist V,
        schurOrthogonality_decode_encode_bhist X,
        schurOrthogonality_decode_encode_bhist Phi,
        schurOrthogonality_decode_encode_bhist Omega,
        schurOrthogonality_decode_encode_bhist H,
        schurOrthogonality_decode_encode_bhist C,
        schurOrthogonality_decode_encode_bhist P,
        schurOrthogonality_decode_encode_bhist N]

private theorem schurOrthogonalityToEventFlow_injective
    {x y : SchurOrthogonalityUp} :
    schurOrthogonalityToEventFlow x = schurOrthogonalityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      schurOrthogonalityFromEventFlow (schurOrthogonalityToEventFlow x) =
        schurOrthogonalityFromEventFlow (schurOrthogonalityToEventFlow y) :=
    congrArg schurOrthogonalityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (schurOrthogonality_round_trip x).symm
      (Eq.trans hread (schurOrthogonality_round_trip y)))

instance schurOrthogonalityBHistCarrier : BHistCarrier SchurOrthogonalityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := schurOrthogonalityToEventFlow
  fromEventFlow := schurOrthogonalityFromEventFlow

instance schurOrthogonalityChapterTasteGate :
    ChapterTasteGate SchurOrthogonalityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change schurOrthogonalityFromEventFlow (schurOrthogonalityToEventFlow x) = some x
    exact schurOrthogonality_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (schurOrthogonalityToEventFlow_injective heq)

theorem SchurOrthogonalityTasteGate_single_carrier_alignment :
    (∀ h : BHist, schurOrthogonalityDecodeBHist (schurOrthogonalityEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier SchurOrthogonalityUp) ∧
        Nonempty (ChapterTasteGate SchurOrthogonalityUp) ∧
          schurOrthogonalityEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact schurOrthogonality_decode_encode_bhist
  · constructor
    · exact Nonempty.intro schurOrthogonalityBHistCarrier
    · constructor
      · exact Nonempty.intro schurOrthogonalityChapterTasteGate
      · rfl

end BEDC.Derived.SchurOrthogonalityUp
