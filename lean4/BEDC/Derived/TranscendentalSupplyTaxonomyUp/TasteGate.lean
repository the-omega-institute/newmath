import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

/-!
# TranscendentalSupplyTaxonomyUp TasteGate carrier.
-/

namespace BEDC.Derived.TranscendentalSupplyTaxonomyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

/-- Finite taxonomy packet with the nine displayed BEDC rows. -/
inductive TranscendentalSupplyTaxonomyUp : Type where
  | mk :
      (socketKind requestedSupply gap auditGate site transport route provenance name : BHist) →
      TranscendentalSupplyTaxonomyUp
  deriving DecidableEq

def transcendentalSupplyTaxonomyEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: transcendentalSupplyTaxonomyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: transcendentalSupplyTaxonomyEncodeBHist h

def transcendentalSupplyTaxonomyDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (transcendentalSupplyTaxonomyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (transcendentalSupplyTaxonomyDecodeBHist tail)

private theorem TranscendentalSupplyTaxonomyTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      transcendentalSupplyTaxonomyDecodeBHist
          (transcendentalSupplyTaxonomyEncodeBHist h) =
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

def transcendentalSupplyTaxonomyToEventFlow :
    TranscendentalSupplyTaxonomyUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | TranscendentalSupplyTaxonomyUp.mk socketKind requestedSupply gap auditGate site transport
      route provenance name =>
      [[BMark.b0],
        transcendentalSupplyTaxonomyEncodeBHist socketKind,
        [BMark.b1, BMark.b0],
        transcendentalSupplyTaxonomyEncodeBHist requestedSupply,
        [BMark.b1, BMark.b1, BMark.b0],
        transcendentalSupplyTaxonomyEncodeBHist gap,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        transcendentalSupplyTaxonomyEncodeBHist auditGate,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        transcendentalSupplyTaxonomyEncodeBHist site,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        transcendentalSupplyTaxonomyEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        transcendentalSupplyTaxonomyEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        transcendentalSupplyTaxonomyEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        transcendentalSupplyTaxonomyEncodeBHist name]

private def transcendentalSupplyTaxonomyDecodePacket
    (socketKind requestedSupply gap auditGate site transport route provenance name : RawEvent) :
    TranscendentalSupplyTaxonomyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  TranscendentalSupplyTaxonomyUp.mk
    (transcendentalSupplyTaxonomyDecodeBHist socketKind)
    (transcendentalSupplyTaxonomyDecodeBHist requestedSupply)
    (transcendentalSupplyTaxonomyDecodeBHist gap)
    (transcendentalSupplyTaxonomyDecodeBHist auditGate)
    (transcendentalSupplyTaxonomyDecodeBHist site)
    (transcendentalSupplyTaxonomyDecodeBHist transport)
    (transcendentalSupplyTaxonomyDecodeBHist route)
    (transcendentalSupplyTaxonomyDecodeBHist provenance)
    (transcendentalSupplyTaxonomyDecodeBHist name)

def transcendentalSupplyTaxonomyFromEventFlow :
    EventFlow → Option TranscendentalSupplyTaxonomyUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | socketKind :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | requestedSupply :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | gap :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | auditGate :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | site :: rest9 =>
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
                                                                      | name :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (transcendentalSupplyTaxonomyDecodePacket
                                                                                  socketKind
                                                                                  requestedSupply
                                                                                  gap
                                                                                  auditGate
                                                                                  site
                                                                                  transport
                                                                                  route
                                                                                  provenance
                                                                                  name)
                                                                          | _ :: _ => none

private theorem TranscendentalSupplyTaxonomyTasteGate_single_carrier_alignment_round :
    ∀ x : TranscendentalSupplyTaxonomyUp,
      transcendentalSupplyTaxonomyFromEventFlow
          (transcendentalSupplyTaxonomyToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk socketKind requestedSupply gap auditGate site transport route provenance name =>
      change
        some
          (transcendentalSupplyTaxonomyDecodePacket
            (transcendentalSupplyTaxonomyEncodeBHist socketKind)
            (transcendentalSupplyTaxonomyEncodeBHist requestedSupply)
            (transcendentalSupplyTaxonomyEncodeBHist gap)
            (transcendentalSupplyTaxonomyEncodeBHist auditGate)
            (transcendentalSupplyTaxonomyEncodeBHist site)
            (transcendentalSupplyTaxonomyEncodeBHist transport)
            (transcendentalSupplyTaxonomyEncodeBHist route)
            (transcendentalSupplyTaxonomyEncodeBHist provenance)
            (transcendentalSupplyTaxonomyEncodeBHist name)) =
          some
            (TranscendentalSupplyTaxonomyUp.mk socketKind requestedSupply gap auditGate site
              transport route provenance name)
      unfold transcendentalSupplyTaxonomyDecodePacket
      have hmk :
          TranscendentalSupplyTaxonomyUp.mk
              (transcendentalSupplyTaxonomyDecodeBHist
                (transcendentalSupplyTaxonomyEncodeBHist socketKind))
              (transcendentalSupplyTaxonomyDecodeBHist
                (transcendentalSupplyTaxonomyEncodeBHist requestedSupply))
              (transcendentalSupplyTaxonomyDecodeBHist
                (transcendentalSupplyTaxonomyEncodeBHist gap))
              (transcendentalSupplyTaxonomyDecodeBHist
                (transcendentalSupplyTaxonomyEncodeBHist auditGate))
              (transcendentalSupplyTaxonomyDecodeBHist
                (transcendentalSupplyTaxonomyEncodeBHist site))
              (transcendentalSupplyTaxonomyDecodeBHist
                (transcendentalSupplyTaxonomyEncodeBHist transport))
              (transcendentalSupplyTaxonomyDecodeBHist
                (transcendentalSupplyTaxonomyEncodeBHist route))
              (transcendentalSupplyTaxonomyDecodeBHist
                (transcendentalSupplyTaxonomyEncodeBHist provenance))
              (transcendentalSupplyTaxonomyDecodeBHist
                (transcendentalSupplyTaxonomyEncodeBHist name)) =
            TranscendentalSupplyTaxonomyUp.mk socketKind requestedSupply gap auditGate site
              transport route provenance name := by
        rw [TranscendentalSupplyTaxonomyTasteGate_single_carrier_alignment_decode socketKind,
          TranscendentalSupplyTaxonomyTasteGate_single_carrier_alignment_decode requestedSupply,
          TranscendentalSupplyTaxonomyTasteGate_single_carrier_alignment_decode gap,
          TranscendentalSupplyTaxonomyTasteGate_single_carrier_alignment_decode auditGate,
          TranscendentalSupplyTaxonomyTasteGate_single_carrier_alignment_decode site,
          TranscendentalSupplyTaxonomyTasteGate_single_carrier_alignment_decode transport,
          TranscendentalSupplyTaxonomyTasteGate_single_carrier_alignment_decode route,
          TranscendentalSupplyTaxonomyTasteGate_single_carrier_alignment_decode provenance,
          TranscendentalSupplyTaxonomyTasteGate_single_carrier_alignment_decode name]
      exact congrArg Option.some hmk

private theorem TranscendentalSupplyTaxonomyTasteGate_single_carrier_alignment_injective
    {x y : TranscendentalSupplyTaxonomyUp} :
    transcendentalSupplyTaxonomyToEventFlow x =
        transcendentalSupplyTaxonomyToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      transcendentalSupplyTaxonomyFromEventFlow
          (transcendentalSupplyTaxonomyToEventFlow x) =
        transcendentalSupplyTaxonomyFromEventFlow
          (transcendentalSupplyTaxonomyToEventFlow y) :=
    congrArg transcendentalSupplyTaxonomyFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (TranscendentalSupplyTaxonomyTasteGate_single_carrier_alignment_round x).symm
      (Eq.trans hread (TranscendentalSupplyTaxonomyTasteGate_single_carrier_alignment_round y)))

instance transcendentalSupplyTaxonomyBHistCarrier :
    BHistCarrier TranscendentalSupplyTaxonomyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := transcendentalSupplyTaxonomyToEventFlow
  fromEventFlow := transcendentalSupplyTaxonomyFromEventFlow

instance transcendentalSupplyTaxonomyChapterTasteGate :
    ChapterTasteGate TranscendentalSupplyTaxonomyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      transcendentalSupplyTaxonomyFromEventFlow
          (transcendentalSupplyTaxonomyToEventFlow x) =
        some x
    exact TranscendentalSupplyTaxonomyTasteGate_single_carrier_alignment_round x
  layer_separation := by
    intro x y hxy heq
    exact hxy (TranscendentalSupplyTaxonomyTasteGate_single_carrier_alignment_injective heq)

def taste_gate : ChapterTasteGate TranscendentalSupplyTaxonomyUp :=
  transcendentalSupplyTaxonomyChapterTasteGate

theorem TranscendentalSupplyTaxonomyTasteGate_single_carrier_alignment :
    transcendentalSupplyTaxonomyEncodeBHist BHist.Empty = ([] : List BMark) ∧
      (∀ h : BHist,
        transcendentalSupplyTaxonomyDecodeBHist
            (transcendentalSupplyTaxonomyEncodeBHist h) =
          h) ∧
        (∀ x : TranscendentalSupplyTaxonomyUp,
          BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow x) = some x) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · rfl
  · constructor
    · exact TranscendentalSupplyTaxonomyTasteGate_single_carrier_alignment_decode
    · intro x
      change
        transcendentalSupplyTaxonomyFromEventFlow
            (transcendentalSupplyTaxonomyToEventFlow x) =
          some x
      exact TranscendentalSupplyTaxonomyTasteGate_single_carrier_alignment_round x

end BEDC.Derived.TranscendentalSupplyTaxonomyUp
