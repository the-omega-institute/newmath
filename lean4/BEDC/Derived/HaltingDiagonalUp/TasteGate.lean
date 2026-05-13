import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HaltingDiagonalUp

open BEDC.FKernel.Mark
open BEDC.FKernel.Hist
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HaltingDiagonalUp : Type where
  | mk :
      (program input selfReference fixedContinuation diagonalPolicy transport routes provenance
        nameCert : BHist) →
      HaltingDiagonalUp
  deriving DecidableEq

def haltingDiagonalEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: haltingDiagonalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: haltingDiagonalEncodeBHist h

def haltingDiagonalDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (haltingDiagonalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (haltingDiagonalDecodeBHist tail)

theorem HaltingDiagonalTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, haltingDiagonalDecodeBHist (haltingDiagonalEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def haltingDiagonalToEventFlow : HaltingDiagonalUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | HaltingDiagonalUp.mk program input selfReference fixedContinuation diagonalPolicy transport
      routes provenance nameCert =>
      [[BMark.b0],
        haltingDiagonalEncodeBHist program,
        [BMark.b1, BMark.b0],
        haltingDiagonalEncodeBHist input,
        [BMark.b1, BMark.b1, BMark.b0],
        haltingDiagonalEncodeBHist selfReference,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        haltingDiagonalEncodeBHist fixedContinuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        haltingDiagonalEncodeBHist diagonalPolicy,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        haltingDiagonalEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        haltingDiagonalEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        haltingDiagonalEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        haltingDiagonalEncodeBHist nameCert]

def haltingDiagonalFromEventFlow : EventFlow → Option HaltingDiagonalUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | program :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | input :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | selfReference :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | fixedContinuation :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | diagonalPolicy :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | transport :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | routes :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | provenance :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | nameCert ::
                                                                          rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (HaltingDiagonalUp.mk
                                                                                  (haltingDiagonalDecodeBHist
                                                                                    program)
                                                                                  (haltingDiagonalDecodeBHist
                                                                                    input)
                                                                                  (haltingDiagonalDecodeBHist
                                                                                    selfReference)
                                                                                  (haltingDiagonalDecodeBHist
                                                                                    fixedContinuation)
                                                                                  (haltingDiagonalDecodeBHist
                                                                                    diagonalPolicy)
                                                                                  (haltingDiagonalDecodeBHist
                                                                                    transport)
                                                                                  (haltingDiagonalDecodeBHist
                                                                                    routes)
                                                                                  (haltingDiagonalDecodeBHist
                                                                                    provenance)
                                                                                  (haltingDiagonalDecodeBHist
                                                                                    nameCert))
                                                                          | _ :: _ => none

private theorem haltingDiagonal_round_trip :
    ∀ x : HaltingDiagonalUp,
      haltingDiagonalFromEventFlow (haltingDiagonalToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk program input selfReference fixedContinuation diagonalPolicy transport routes provenance
      nameCert =>
      change
        some
          (HaltingDiagonalUp.mk
            (haltingDiagonalDecodeBHist (haltingDiagonalEncodeBHist program))
            (haltingDiagonalDecodeBHist (haltingDiagonalEncodeBHist input))
            (haltingDiagonalDecodeBHist (haltingDiagonalEncodeBHist selfReference))
            (haltingDiagonalDecodeBHist (haltingDiagonalEncodeBHist fixedContinuation))
            (haltingDiagonalDecodeBHist (haltingDiagonalEncodeBHist diagonalPolicy))
            (haltingDiagonalDecodeBHist (haltingDiagonalEncodeBHist transport))
            (haltingDiagonalDecodeBHist (haltingDiagonalEncodeBHist routes))
            (haltingDiagonalDecodeBHist (haltingDiagonalEncodeBHist provenance))
            (haltingDiagonalDecodeBHist (haltingDiagonalEncodeBHist nameCert))) =
          some
            (HaltingDiagonalUp.mk program input selfReference fixedContinuation diagonalPolicy
              transport routes provenance nameCert)
      rw [HaltingDiagonalTasteGate_single_carrier_alignment_decode_encode program,
        HaltingDiagonalTasteGate_single_carrier_alignment_decode_encode input,
        HaltingDiagonalTasteGate_single_carrier_alignment_decode_encode selfReference,
        HaltingDiagonalTasteGate_single_carrier_alignment_decode_encode fixedContinuation,
        HaltingDiagonalTasteGate_single_carrier_alignment_decode_encode diagonalPolicy,
        HaltingDiagonalTasteGate_single_carrier_alignment_decode_encode transport,
        HaltingDiagonalTasteGate_single_carrier_alignment_decode_encode routes,
        HaltingDiagonalTasteGate_single_carrier_alignment_decode_encode provenance,
        HaltingDiagonalTasteGate_single_carrier_alignment_decode_encode nameCert]

private theorem haltingDiagonalToEventFlow_injective {x y : HaltingDiagonalUp} :
    haltingDiagonalToEventFlow x = haltingDiagonalToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      haltingDiagonalFromEventFlow (haltingDiagonalToEventFlow x) =
        haltingDiagonalFromEventFlow (haltingDiagonalToEventFlow y) :=
    congrArg haltingDiagonalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (haltingDiagonal_round_trip x).symm
      (Eq.trans hread (haltingDiagonal_round_trip y)))

instance haltingDiagonalBHistCarrier : BHistCarrier HaltingDiagonalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := haltingDiagonalToEventFlow
  fromEventFlow := haltingDiagonalFromEventFlow

instance haltingDiagonalChapterTasteGate : ChapterTasteGate HaltingDiagonalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change haltingDiagonalFromEventFlow (haltingDiagonalToEventFlow x) = some x
    exact haltingDiagonal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (haltingDiagonalToEventFlow_injective heq)

theorem HaltingDiagonalTasteGate_single_carrier_alignment :
    (∀ h : BHist, haltingDiagonalDecodeBHist (haltingDiagonalEncodeBHist h) = h) ∧
      (∀ x : HaltingDiagonalUp,
        haltingDiagonalFromEventFlow (haltingDiagonalToEventFlow x) = some x) ∧
        (∀ x y : HaltingDiagonalUp,
          haltingDiagonalToEventFlow x = haltingDiagonalToEventFlow y → x = y) ∧
          haltingDiagonalEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact HaltingDiagonalTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact haltingDiagonal_round_trip
    · constructor
      · intro x y heq
        exact haltingDiagonalToEventFlow_injective heq
      · rfl

end BEDC.Derived.HaltingDiagonalUp
