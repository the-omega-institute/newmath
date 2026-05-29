import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedRealIntervalPartitionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedRealIntervalPartitionUp : Type where
  -- BEDC touchpoint anchor: BHist BMark
  | mk :
      (located mesh rational dyadic stream readback realSeal transport replay provenance
        localName : BHist) ->
        LocatedRealIntervalPartitionUp
  deriving DecidableEq

def locatedRealIntervalPartitionEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedRealIntervalPartitionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedRealIntervalPartitionEncodeBHist h

def locatedRealIntervalPartitionDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedRealIntervalPartitionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedRealIntervalPartitionDecodeBHist tail)

private theorem LocatedRealIntervalPartitionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      locatedRealIntervalPartitionDecodeBHist
          (locatedRealIntervalPartitionEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def LocatedRealIntervalPartitionTasteGate_single_carrier_alignment_fields :
    LocatedRealIntervalPartitionUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedRealIntervalPartitionUp.mk located mesh rational dyadic stream readback realSeal
      transport replay provenance localName =>
      [located, mesh, rational, dyadic, stream, readback, realSeal, transport, replay,
        provenance, localName]

def LocatedRealIntervalPartitionTasteGate_single_carrier_alignment_toEventFlow :
    LocatedRealIntervalPartitionUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (LocatedRealIntervalPartitionTasteGate_single_carrier_alignment_fields x).map
        locatedRealIntervalPartitionEncodeBHist

def LocatedRealIntervalPartitionTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow -> Option LocatedRealIntervalPartitionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | located :: rest0 =>
      match rest0 with
      | [] => none
      | mesh :: rest1 =>
          match rest1 with
          | [] => none
          | rational :: rest2 =>
              match rest2 with
              | [] => none
              | dyadic :: rest3 =>
                  match rest3 with
                  | [] => none
                  | stream :: rest4 =>
                      match rest4 with
                      | [] => none
                      | readback :: rest5 =>
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
                                          | localName :: rest10 =>
                                              match rest10 with
                                              | [] =>
                                                  some
                                                    (LocatedRealIntervalPartitionUp.mk
                                                      (locatedRealIntervalPartitionDecodeBHist
                                                        located)
                                                      (locatedRealIntervalPartitionDecodeBHist
                                                        mesh)
                                                      (locatedRealIntervalPartitionDecodeBHist
                                                        rational)
                                                      (locatedRealIntervalPartitionDecodeBHist
                                                        dyadic)
                                                      (locatedRealIntervalPartitionDecodeBHist
                                                        stream)
                                                      (locatedRealIntervalPartitionDecodeBHist
                                                        readback)
                                                      (locatedRealIntervalPartitionDecodeBHist
                                                        realSeal)
                                                      (locatedRealIntervalPartitionDecodeBHist
                                                        transport)
                                                      (locatedRealIntervalPartitionDecodeBHist
                                                        replay)
                                                      (locatedRealIntervalPartitionDecodeBHist
                                                        provenance)
                                                      (locatedRealIntervalPartitionDecodeBHist
                                                        localName))
                                              | _ :: _ => none

private theorem LocatedRealIntervalPartitionTasteGate_single_carrier_alignment_round_trip
    (x : LocatedRealIntervalPartitionUp) :
    LocatedRealIntervalPartitionTasteGate_single_carrier_alignment_fromEventFlow
        (LocatedRealIntervalPartitionTasteGate_single_carrier_alignment_toEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk located mesh rational dyadic stream readback realSeal transport replay provenance
      localName =>
      change
        some
          (LocatedRealIntervalPartitionUp.mk
            (locatedRealIntervalPartitionDecodeBHist
              (locatedRealIntervalPartitionEncodeBHist located))
            (locatedRealIntervalPartitionDecodeBHist
              (locatedRealIntervalPartitionEncodeBHist mesh))
            (locatedRealIntervalPartitionDecodeBHist
              (locatedRealIntervalPartitionEncodeBHist rational))
            (locatedRealIntervalPartitionDecodeBHist
              (locatedRealIntervalPartitionEncodeBHist dyadic))
            (locatedRealIntervalPartitionDecodeBHist
              (locatedRealIntervalPartitionEncodeBHist stream))
            (locatedRealIntervalPartitionDecodeBHist
              (locatedRealIntervalPartitionEncodeBHist readback))
            (locatedRealIntervalPartitionDecodeBHist
              (locatedRealIntervalPartitionEncodeBHist realSeal))
            (locatedRealIntervalPartitionDecodeBHist
              (locatedRealIntervalPartitionEncodeBHist transport))
            (locatedRealIntervalPartitionDecodeBHist
              (locatedRealIntervalPartitionEncodeBHist replay))
            (locatedRealIntervalPartitionDecodeBHist
              (locatedRealIntervalPartitionEncodeBHist provenance))
            (locatedRealIntervalPartitionDecodeBHist
              (locatedRealIntervalPartitionEncodeBHist localName))) =
          some
            (LocatedRealIntervalPartitionUp.mk located mesh rational dyadic stream readback
              realSeal transport replay provenance localName)
      rw [LocatedRealIntervalPartitionTasteGate_single_carrier_alignment_decode_encode located,
        LocatedRealIntervalPartitionTasteGate_single_carrier_alignment_decode_encode mesh,
        LocatedRealIntervalPartitionTasteGate_single_carrier_alignment_decode_encode rational,
        LocatedRealIntervalPartitionTasteGate_single_carrier_alignment_decode_encode dyadic,
        LocatedRealIntervalPartitionTasteGate_single_carrier_alignment_decode_encode stream,
        LocatedRealIntervalPartitionTasteGate_single_carrier_alignment_decode_encode readback,
        LocatedRealIntervalPartitionTasteGate_single_carrier_alignment_decode_encode realSeal,
        LocatedRealIntervalPartitionTasteGate_single_carrier_alignment_decode_encode transport,
        LocatedRealIntervalPartitionTasteGate_single_carrier_alignment_decode_encode replay,
        LocatedRealIntervalPartitionTasteGate_single_carrier_alignment_decode_encode provenance,
        LocatedRealIntervalPartitionTasteGate_single_carrier_alignment_decode_encode localName]

private theorem LocatedRealIntervalPartitionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LocatedRealIntervalPartitionUp} :
    LocatedRealIntervalPartitionTasteGate_single_carrier_alignment_toEventFlow x =
        LocatedRealIntervalPartitionTasteGate_single_carrier_alignment_toEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      LocatedRealIntervalPartitionTasteGate_single_carrier_alignment_fromEventFlow
          (LocatedRealIntervalPartitionTasteGate_single_carrier_alignment_toEventFlow x) =
        LocatedRealIntervalPartitionTasteGate_single_carrier_alignment_fromEventFlow
          (LocatedRealIntervalPartitionTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg LocatedRealIntervalPartitionTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (LocatedRealIntervalPartitionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (LocatedRealIntervalPartitionTasteGate_single_carrier_alignment_round_trip y)))

private theorem LocatedRealIntervalPartitionTasteGate_single_carrier_alignment_fields_faithful
    (x y : LocatedRealIntervalPartitionUp) :
    LocatedRealIntervalPartitionTasteGate_single_carrier_alignment_fields x =
        LocatedRealIntervalPartitionTasteGate_single_carrier_alignment_fields y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  cases x with
  | mk located₁ mesh₁ rational₁ dyadic₁ stream₁ readback₁ realSeal₁ transport₁ replay₁
      provenance₁ localName₁ =>
      cases y with
      | mk located₂ mesh₂ rational₂ dyadic₂ stream₂ readback₂ realSeal₂ transport₂ replay₂
          provenance₂ localName₂ =>
          injection h with hLocated hRest₁
          injection hRest₁ with hMesh hRest₂
          injection hRest₂ with hRational hRest₃
          injection hRest₃ with hDyadic hRest₄
          injection hRest₄ with hStream hRest₅
          injection hRest₅ with hReadback hRest₆
          injection hRest₆ with hRealSeal hRest₇
          injection hRest₇ with hTransport hRest₈
          injection hRest₈ with hReplay hRest₉
          injection hRest₉ with hProvenance hRest₁₀
          injection hRest₁₀ with hLocalName _
          subst hLocated
          subst hMesh
          subst hRational
          subst hDyadic
          subst hStream
          subst hReadback
          subst hRealSeal
          subst hTransport
          subst hReplay
          subst hProvenance
          subst hLocalName
          rfl

instance locatedRealIntervalPartitionBHistCarrier :
    BHistCarrier LocatedRealIntervalPartitionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := LocatedRealIntervalPartitionTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := LocatedRealIntervalPartitionTasteGate_single_carrier_alignment_fromEventFlow

instance locatedRealIntervalPartitionChapterTasteGate :
    ChapterTasteGate LocatedRealIntervalPartitionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := fun x =>
    id (LocatedRealIntervalPartitionTasteGate_single_carrier_alignment_round_trip x)
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (LocatedRealIntervalPartitionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance locatedRealIntervalPartitionFieldFaithful :
    FieldFaithful LocatedRealIntervalPartitionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := LocatedRealIntervalPartitionTasteGate_single_carrier_alignment_fields
  field_faithful :=
    LocatedRealIntervalPartitionTasteGate_single_carrier_alignment_fields_faithful

instance locatedRealIntervalPartitionNontrivial :
    Nontrivial LocatedRealIntervalPartitionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LocatedRealIntervalPartitionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      LocatedRealIntervalPartitionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def LocatedRealIntervalPartitionTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate LocatedRealIntervalPartitionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locatedRealIntervalPartitionChapterTasteGate

theorem LocatedRealIntervalPartitionTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate LocatedRealIntervalPartitionUp) ∧
      Nonempty (BHistCarrier LocatedRealIntervalPartitionUp) ∧
        Nonempty (FieldFaithful LocatedRealIntervalPartitionUp) ∧
          Nonempty (BEDC.Meta.TasteGate.Nontrivial LocatedRealIntervalPartitionUp) ∧
            (∀ h : BHist,
              locatedRealIntervalPartitionDecodeBHist
                  (locatedRealIntervalPartitionEncodeBHist h) =
                h) ∧
              (∀ x : LocatedRealIntervalPartitionUp,
                LocatedRealIntervalPartitionTasteGate_single_carrier_alignment_fromEventFlow
                    (LocatedRealIntervalPartitionTasteGate_single_carrier_alignment_toEventFlow
                      x) =
                  some x) ∧
                (∀ x y : LocatedRealIntervalPartitionUp,
                  LocatedRealIntervalPartitionTasteGate_single_carrier_alignment_toEventFlow x =
                      LocatedRealIntervalPartitionTasteGate_single_carrier_alignment_toEventFlow
                        y ->
                    x = y) ∧
                  locatedRealIntervalPartitionEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨locatedRealIntervalPartitionChapterTasteGate⟩
  · constructor
    · exact ⟨locatedRealIntervalPartitionBHistCarrier⟩
    · constructor
      · exact ⟨locatedRealIntervalPartitionFieldFaithful⟩
      · constructor
        · exact ⟨locatedRealIntervalPartitionNontrivial⟩
        · constructor
          · exact LocatedRealIntervalPartitionTasteGate_single_carrier_alignment_decode_encode
          · constructor
            · exact LocatedRealIntervalPartitionTasteGate_single_carrier_alignment_round_trip
            · constructor
              · intro x y heq
                exact
                  LocatedRealIntervalPartitionTasteGate_single_carrier_alignment_toEventFlow_injective
                    heq
              · rfl

end BEDC.Derived.LocatedRealIntervalPartitionUp
