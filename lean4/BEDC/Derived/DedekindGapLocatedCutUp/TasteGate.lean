import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DedekindGapLocatedCutUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DedekindGapLocatedCutUp : Type where
  | mk (L U D W R S E H C P N : BHist) : DedekindGapLocatedCutUp
  deriving DecidableEq

def dedekindGapLocatedCutEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dedekindGapLocatedCutEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dedekindGapLocatedCutEncodeBHist h

def dedekindGapLocatedCutDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dedekindGapLocatedCutDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dedekindGapLocatedCutDecodeBHist tail)

private theorem DedekindGapLocatedCutTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      dedekindGapLocatedCutDecodeBHist (dedekindGapLocatedCutEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dedekindGapLocatedCutFields : DedekindGapLocatedCutUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DedekindGapLocatedCutUp.mk L U D W R S E H C P N => [L, U, D, W, R, S, E, H, C, P, N]

def dedekindGapLocatedCutToEventFlow : DedekindGapLocatedCutUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (dedekindGapLocatedCutFields x).map dedekindGapLocatedCutEncodeBHist

def dedekindGapLocatedCutFromEventFlow : EventFlow → Option DedekindGapLocatedCutUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | lower :: rest0 =>
      match rest0 with
      | [] => none
      | upper :: rest1 =>
          match rest1 with
          | [] => none
          | gap :: rest2 =>
              match rest2 with
              | [] => none
              | window :: rest3 =>
                  match rest3 with
                  | [] => none
                  | readback :: rest4 =>
                      match rest4 with
                      | [] => none
                      | supremum :: rest5 =>
                          match rest5 with
                          | [] => none
                          | realSeal :: rest6 =>
                              match rest6 with
                              | [] => none
                              | transport :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | replay :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | provenance :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | nameCert :: rest10 =>
                                              match rest10 with
                                              | [] =>
                                                  some
                                                    (DedekindGapLocatedCutUp.mk
                                                      (dedekindGapLocatedCutDecodeBHist lower)
                                                      (dedekindGapLocatedCutDecodeBHist upper)
                                                      (dedekindGapLocatedCutDecodeBHist gap)
                                                      (dedekindGapLocatedCutDecodeBHist window)
                                                      (dedekindGapLocatedCutDecodeBHist readback)
                                                      (dedekindGapLocatedCutDecodeBHist supremum)
                                                      (dedekindGapLocatedCutDecodeBHist realSeal)
                                                      (dedekindGapLocatedCutDecodeBHist transport)
                                                      (dedekindGapLocatedCutDecodeBHist replay)
                                                      (dedekindGapLocatedCutDecodeBHist provenance)
                                                      (dedekindGapLocatedCutDecodeBHist nameCert))
                                              | _ :: _ => none

private theorem DedekindGapLocatedCutTasteGate_single_carrier_alignment_round_trip
    (x : DedekindGapLocatedCutUp) :
    dedekindGapLocatedCutFromEventFlow (dedekindGapLocatedCutToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk L U D W R S E H C P N =>
      change
        some
          (DedekindGapLocatedCutUp.mk
            (dedekindGapLocatedCutDecodeBHist (dedekindGapLocatedCutEncodeBHist L))
            (dedekindGapLocatedCutDecodeBHist (dedekindGapLocatedCutEncodeBHist U))
            (dedekindGapLocatedCutDecodeBHist (dedekindGapLocatedCutEncodeBHist D))
            (dedekindGapLocatedCutDecodeBHist (dedekindGapLocatedCutEncodeBHist W))
            (dedekindGapLocatedCutDecodeBHist (dedekindGapLocatedCutEncodeBHist R))
            (dedekindGapLocatedCutDecodeBHist (dedekindGapLocatedCutEncodeBHist S))
            (dedekindGapLocatedCutDecodeBHist (dedekindGapLocatedCutEncodeBHist E))
            (dedekindGapLocatedCutDecodeBHist (dedekindGapLocatedCutEncodeBHist H))
            (dedekindGapLocatedCutDecodeBHist (dedekindGapLocatedCutEncodeBHist C))
            (dedekindGapLocatedCutDecodeBHist (dedekindGapLocatedCutEncodeBHist P))
            (dedekindGapLocatedCutDecodeBHist (dedekindGapLocatedCutEncodeBHist N))) =
          some (DedekindGapLocatedCutUp.mk L U D W R S E H C P N)
      rw [DedekindGapLocatedCutTasteGate_single_carrier_alignment_decode_encode L,
        DedekindGapLocatedCutTasteGate_single_carrier_alignment_decode_encode U,
        DedekindGapLocatedCutTasteGate_single_carrier_alignment_decode_encode D,
        DedekindGapLocatedCutTasteGate_single_carrier_alignment_decode_encode W,
        DedekindGapLocatedCutTasteGate_single_carrier_alignment_decode_encode R,
        DedekindGapLocatedCutTasteGate_single_carrier_alignment_decode_encode S,
        DedekindGapLocatedCutTasteGate_single_carrier_alignment_decode_encode E,
        DedekindGapLocatedCutTasteGate_single_carrier_alignment_decode_encode H,
        DedekindGapLocatedCutTasteGate_single_carrier_alignment_decode_encode C,
        DedekindGapLocatedCutTasteGate_single_carrier_alignment_decode_encode P,
        DedekindGapLocatedCutTasteGate_single_carrier_alignment_decode_encode N]

private theorem DedekindGapLocatedCutTasteGate_single_carrier_alignment_injective
    {x y : DedekindGapLocatedCutUp} :
    dedekindGapLocatedCutToEventFlow x = dedekindGapLocatedCutToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dedekindGapLocatedCutFromEventFlow (dedekindGapLocatedCutToEventFlow x) =
        dedekindGapLocatedCutFromEventFlow (dedekindGapLocatedCutToEventFlow y) :=
    congrArg dedekindGapLocatedCutFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (DedekindGapLocatedCutTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (DedekindGapLocatedCutTasteGate_single_carrier_alignment_round_trip y)))

private theorem DedekindGapLocatedCutTasteGate_single_carrier_alignment_fields :
    ∀ x y : DedekindGapLocatedCutUp,
      dedekindGapLocatedCutFields x = dedekindGapLocatedCutFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk L1 U1 D1 W1 R1 S1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk L2 U2 D2 W2 R2 S2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance dedekindGapLocatedCutBHistCarrier : BHistCarrier DedekindGapLocatedCutUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dedekindGapLocatedCutToEventFlow
  fromEventFlow := dedekindGapLocatedCutFromEventFlow

instance dedekindGapLocatedCutChapterTasteGate :
    ChapterTasteGate DedekindGapLocatedCutUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dedekindGapLocatedCutFromEventFlow (dedekindGapLocatedCutToEventFlow x) = some x
    exact DedekindGapLocatedCutTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DedekindGapLocatedCutTasteGate_single_carrier_alignment_injective heq)

instance dedekindGapLocatedCutFieldFaithful : FieldFaithful DedekindGapLocatedCutUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := dedekindGapLocatedCutFields
  field_faithful := DedekindGapLocatedCutTasteGate_single_carrier_alignment_fields

instance dedekindGapLocatedCutNontrivial : Nontrivial DedekindGapLocatedCutUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DedekindGapLocatedCutUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DedekindGapLocatedCutUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate DedekindGapLocatedCutUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dedekindGapLocatedCutChapterTasteGate

theorem DedekindGapLocatedCutTasteGate_single_carrier_alignment :
    (∀ h : BHist, dedekindGapLocatedCutDecodeBHist (dedekindGapLocatedCutEncodeBHist h) = h) ∧
      (∀ x : DedekindGapLocatedCutUp,
        dedekindGapLocatedCutFromEventFlow (dedekindGapLocatedCutToEventFlow x) = some x) ∧
        (∀ x y : DedekindGapLocatedCutUp,
          dedekindGapLocatedCutToEventFlow x = dedekindGapLocatedCutToEventFlow y -> x = y) ∧
          dedekindGapLocatedCutEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  constructor
  · exact DedekindGapLocatedCutTasteGate_single_carrier_alignment_decode_encode
  constructor
  · exact DedekindGapLocatedCutTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact DedekindGapLocatedCutTasteGate_single_carrier_alignment_injective heq
  · rfl

end BEDC.Derived.DedekindGapLocatedCutUp
