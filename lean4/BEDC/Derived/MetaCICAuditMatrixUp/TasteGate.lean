import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetaCICAuditMatrixUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetaCICAuditMatrixUp : Type where
  | mk :
      (available nonClaim blocked synthesis nonescape transport route provenance localName :
        BHist) → MetaCICAuditMatrixUp
  deriving DecidableEq

def metaCICAuditMatrixEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metaCICAuditMatrixEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metaCICAuditMatrixEncodeBHist h

def metaCICAuditMatrixDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metaCICAuditMatrixDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metaCICAuditMatrixDecodeBHist tail)

private theorem metaCICAuditMatrix_decode_encode_bhist :
    ∀ h : BHist,
      metaCICAuditMatrixDecodeBHist
        (metaCICAuditMatrixEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def metaCICAuditMatrixToEventFlow : MetaCICAuditMatrixUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MetaCICAuditMatrixUp.mk available nonClaim blocked synthesis nonescape transport route
      provenance localName =>
      [[BMark.b0],
        metaCICAuditMatrixEncodeBHist available,
        [BMark.b1, BMark.b0],
        metaCICAuditMatrixEncodeBHist nonClaim,
        [BMark.b1, BMark.b1, BMark.b0],
        metaCICAuditMatrixEncodeBHist blocked,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICAuditMatrixEncodeBHist synthesis,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICAuditMatrixEncodeBHist nonescape,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICAuditMatrixEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICAuditMatrixEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        metaCICAuditMatrixEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        metaCICAuditMatrixEncodeBHist localName]

def metaCICAuditMatrixFromEventFlow :
    EventFlow → Option MetaCICAuditMatrixUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | available :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | nonClaim :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | blocked :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | synthesis :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | nonescape :: rest9 =>
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
                                                      | route :: rest13 =>
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
                                                                      | localName :: rest17 =>
                                                                          match
                                                                            rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (MetaCICAuditMatrixUp.mk
                                                                                  (metaCICAuditMatrixDecodeBHist available)
                                                                                  (metaCICAuditMatrixDecodeBHist nonClaim)
                                                                                  (metaCICAuditMatrixDecodeBHist blocked)
                                                                                  (metaCICAuditMatrixDecodeBHist synthesis)
                                                                                  (metaCICAuditMatrixDecodeBHist nonescape)
                                                                                  (metaCICAuditMatrixDecodeBHist transport)
                                                                                  (metaCICAuditMatrixDecodeBHist route)
                                                                                  (metaCICAuditMatrixDecodeBHist provenance)
                                                                                  (metaCICAuditMatrixDecodeBHist localName))
                                                                          | _ :: _ =>
                                                                              none

private theorem metaCICAuditMatrix_round_trip :
    ∀ x : MetaCICAuditMatrixUp,
      metaCICAuditMatrixFromEventFlow
        (metaCICAuditMatrixToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk available nonClaim blocked synthesis nonescape transport route provenance localName =>
      change
        some
          (MetaCICAuditMatrixUp.mk
            (metaCICAuditMatrixDecodeBHist
              (metaCICAuditMatrixEncodeBHist available))
            (metaCICAuditMatrixDecodeBHist
              (metaCICAuditMatrixEncodeBHist nonClaim))
            (metaCICAuditMatrixDecodeBHist
              (metaCICAuditMatrixEncodeBHist blocked))
            (metaCICAuditMatrixDecodeBHist
              (metaCICAuditMatrixEncodeBHist synthesis))
            (metaCICAuditMatrixDecodeBHist
              (metaCICAuditMatrixEncodeBHist nonescape))
            (metaCICAuditMatrixDecodeBHist
              (metaCICAuditMatrixEncodeBHist transport))
            (metaCICAuditMatrixDecodeBHist
              (metaCICAuditMatrixEncodeBHist route))
            (metaCICAuditMatrixDecodeBHist
              (metaCICAuditMatrixEncodeBHist provenance))
            (metaCICAuditMatrixDecodeBHist
              (metaCICAuditMatrixEncodeBHist localName))) =
          some
            (MetaCICAuditMatrixUp.mk available nonClaim blocked synthesis nonescape
              transport route provenance localName)
      rw [metaCICAuditMatrix_decode_encode_bhist available,
        metaCICAuditMatrix_decode_encode_bhist nonClaim,
        metaCICAuditMatrix_decode_encode_bhist blocked,
        metaCICAuditMatrix_decode_encode_bhist synthesis,
        metaCICAuditMatrix_decode_encode_bhist nonescape,
        metaCICAuditMatrix_decode_encode_bhist transport,
        metaCICAuditMatrix_decode_encode_bhist route,
        metaCICAuditMatrix_decode_encode_bhist provenance,
        metaCICAuditMatrix_decode_encode_bhist localName]

private theorem metaCICAuditMatrixToEventFlow_injective
    {x y : MetaCICAuditMatrixUp} :
    metaCICAuditMatrixToEventFlow x =
      metaCICAuditMatrixToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metaCICAuditMatrixFromEventFlow
          (metaCICAuditMatrixToEventFlow x) =
        metaCICAuditMatrixFromEventFlow
          (metaCICAuditMatrixToEventFlow y) :=
    congrArg metaCICAuditMatrixFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (metaCICAuditMatrix_round_trip x).symm
      (Eq.trans hread (metaCICAuditMatrix_round_trip y)))

def metaCICAuditMatrixFields : MetaCICAuditMatrixUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetaCICAuditMatrixUp.mk available nonClaim blocked synthesis nonescape transport route
      provenance localName =>
      [available, nonClaim, blocked, synthesis, nonescape, transport, route, provenance,
        localName]

private theorem MetaCICAuditMatrixTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : MetaCICAuditMatrixUp,
      metaCICAuditMatrixFields x = metaCICAuditMatrixFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk available nonClaim blocked synthesis nonescape transport route provenance localName =>
      cases y with
      | mk available' nonClaim' blocked' synthesis' nonescape' transport' route'
          provenance' localName' =>
          cases hfields
          rfl

instance metaCICAuditMatrixBHistCarrier :
    BHistCarrier MetaCICAuditMatrixUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metaCICAuditMatrixToEventFlow
  fromEventFlow := metaCICAuditMatrixFromEventFlow

instance metaCICAuditMatrixChapterTasteGate :
    ChapterTasteGate MetaCICAuditMatrixUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change metaCICAuditMatrixFromEventFlow (metaCICAuditMatrixToEventFlow x) = some x
    exact metaCICAuditMatrix_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metaCICAuditMatrixToEventFlow_injective heq)

instance metaCICAuditMatrixFieldFaithful :
    FieldFaithful MetaCICAuditMatrixUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := metaCICAuditMatrixFields
  field_faithful := MetaCICAuditMatrixTasteGate_single_carrier_alignment_field_faithful

theorem MetaCICAuditMatrixTasteGate_single_carrier_alignment :
    (∀ h : BHist, metaCICAuditMatrixDecodeBHist
      (metaCICAuditMatrixEncodeBHist h) = h) ∧
      (∀ x : MetaCICAuditMatrixUp,
        metaCICAuditMatrixFromEventFlow
          (metaCICAuditMatrixToEventFlow x) = some x) ∧
      (∀ x y : MetaCICAuditMatrixUp,
        metaCICAuditMatrixToEventFlow x =
          metaCICAuditMatrixToEventFlow y → x = y) ∧
      metaCICAuditMatrixEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  constructor
  · exact metaCICAuditMatrix_decode_encode_bhist
  · constructor
    · exact metaCICAuditMatrix_round_trip
    · constructor
      · intro x y heq
        exact metaCICAuditMatrixToEventFlow_injective heq
      · rfl

theorem MetaCICAuditMatrixUp_obligation_surface :
    Nonempty (BHistCarrier MetaCICAuditMatrixUp) ∧
      Nonempty (ChapterTasteGate MetaCICAuditMatrixUp) ∧
      ∃ x : MetaCICAuditMatrixUp,
        x =
            MetaCICAuditMatrixUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty ∧
          BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  let x : MetaCICAuditMatrixUp :=
    MetaCICAuditMatrixUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
      BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
  constructor
  · exact ⟨metaCICAuditMatrixBHistCarrier⟩
  · constructor
    · exact ⟨metaCICAuditMatrixChapterTasteGate⟩
    · exact ⟨x, rfl, ChapterTasteGate.round_trip x⟩

end BEDC.Derived.MetaCICAuditMatrixUp
