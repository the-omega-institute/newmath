import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CertifiedPhysicalTruthUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CertifiedPhysicalTruthUp : Type where
  | mk (S G K A D I L F H C P N : BHist) : CertifiedPhysicalTruthUp
  deriving DecidableEq

def certifiedPhysicalTruthEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: certifiedPhysicalTruthEncodeBHist h
  | BHist.e1 h => BMark.b1 :: certifiedPhysicalTruthEncodeBHist h

def certifiedPhysicalTruthDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (certifiedPhysicalTruthDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (certifiedPhysicalTruthDecodeBHist tail)

private theorem CertifiedPhysicalTruthTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      certifiedPhysicalTruthDecodeBHist (certifiedPhysicalTruthEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def certifiedPhysicalTruthToEventFlow : CertifiedPhysicalTruthUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CertifiedPhysicalTruthUp.mk S G K A D I L F H C P N =>
      [[BMark.b0],
        certifiedPhysicalTruthEncodeBHist S,
        [BMark.b1, BMark.b0],
        certifiedPhysicalTruthEncodeBHist G,
        [BMark.b1, BMark.b1, BMark.b0],
        certifiedPhysicalTruthEncodeBHist K,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        certifiedPhysicalTruthEncodeBHist A,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        certifiedPhysicalTruthEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        certifiedPhysicalTruthEncodeBHist I,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        certifiedPhysicalTruthEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        certifiedPhysicalTruthEncodeBHist F,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        certifiedPhysicalTruthEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        certifiedPhysicalTruthEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        certifiedPhysicalTruthEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        certifiedPhysicalTruthEncodeBHist N]

private def certifiedPhysicalTruthDecodePacket
    (S G K A D I L F H C P N : RawEvent) : CertifiedPhysicalTruthUp :=
  -- BEDC touchpoint anchor: BHist BMark
  CertifiedPhysicalTruthUp.mk
    (certifiedPhysicalTruthDecodeBHist S)
    (certifiedPhysicalTruthDecodeBHist G)
    (certifiedPhysicalTruthDecodeBHist K)
    (certifiedPhysicalTruthDecodeBHist A)
    (certifiedPhysicalTruthDecodeBHist D)
    (certifiedPhysicalTruthDecodeBHist I)
    (certifiedPhysicalTruthDecodeBHist L)
    (certifiedPhysicalTruthDecodeBHist F)
    (certifiedPhysicalTruthDecodeBHist H)
    (certifiedPhysicalTruthDecodeBHist C)
    (certifiedPhysicalTruthDecodeBHist P)
    (certifiedPhysicalTruthDecodeBHist N)

def certifiedPhysicalTruthFromEventFlow : EventFlow -> Option CertifiedPhysicalTruthUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | S :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | G :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | K :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | A :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | D :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | I :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | L :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | F :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | H :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | C :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] => none
                                                                                  | _tag10 :: rest20 =>
                                                                                      match rest20 with
                                                                                      | [] => none
                                                                                      | P :: rest21 =>
                                                                                          match rest21 with
                                                                                          | [] => none
                                                                                          | _tag11 :: rest22 =>
                                                                                              match rest22 with
                                                                                              | [] => none
                                                                                              | N :: rest23 =>
                                                                                                  match rest23 with
                                                                                                  | [] =>
                                                                                                      some
                                                                                                        (certifiedPhysicalTruthDecodePacket
                                                                                                          S G K A D I L F H C P N)
                                                                                                  | _ :: _ => none

private theorem CertifiedPhysicalTruthTasteGate_single_carrier_alignment_round_trip :
    forall x : CertifiedPhysicalTruthUp,
      certifiedPhysicalTruthFromEventFlow (certifiedPhysicalTruthToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S G K A D I L F H C P N =>
      change
        some
          (certifiedPhysicalTruthDecodePacket
            (certifiedPhysicalTruthEncodeBHist S)
            (certifiedPhysicalTruthEncodeBHist G)
            (certifiedPhysicalTruthEncodeBHist K)
            (certifiedPhysicalTruthEncodeBHist A)
            (certifiedPhysicalTruthEncodeBHist D)
            (certifiedPhysicalTruthEncodeBHist I)
            (certifiedPhysicalTruthEncodeBHist L)
            (certifiedPhysicalTruthEncodeBHist F)
            (certifiedPhysicalTruthEncodeBHist H)
            (certifiedPhysicalTruthEncodeBHist C)
            (certifiedPhysicalTruthEncodeBHist P)
            (certifiedPhysicalTruthEncodeBHist N)) =
          some (CertifiedPhysicalTruthUp.mk S G K A D I L F H C P N)
      unfold certifiedPhysicalTruthDecodePacket
      rw [CertifiedPhysicalTruthTasteGate_single_carrier_alignment_decode S,
        CertifiedPhysicalTruthTasteGate_single_carrier_alignment_decode G,
        CertifiedPhysicalTruthTasteGate_single_carrier_alignment_decode K,
        CertifiedPhysicalTruthTasteGate_single_carrier_alignment_decode A,
        CertifiedPhysicalTruthTasteGate_single_carrier_alignment_decode D,
        CertifiedPhysicalTruthTasteGate_single_carrier_alignment_decode I,
        CertifiedPhysicalTruthTasteGate_single_carrier_alignment_decode L,
        CertifiedPhysicalTruthTasteGate_single_carrier_alignment_decode F,
        CertifiedPhysicalTruthTasteGate_single_carrier_alignment_decode H,
        CertifiedPhysicalTruthTasteGate_single_carrier_alignment_decode C,
        CertifiedPhysicalTruthTasteGate_single_carrier_alignment_decode P,
        CertifiedPhysicalTruthTasteGate_single_carrier_alignment_decode N]

private theorem CertifiedPhysicalTruthTasteGate_single_carrier_alignment_injective
    {x y : CertifiedPhysicalTruthUp} :
    certifiedPhysicalTruthToEventFlow x = certifiedPhysicalTruthToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      certifiedPhysicalTruthFromEventFlow (certifiedPhysicalTruthToEventFlow x) =
        certifiedPhysicalTruthFromEventFlow (certifiedPhysicalTruthToEventFlow y) :=
    congrArg certifiedPhysicalTruthFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CertifiedPhysicalTruthTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CertifiedPhysicalTruthTasteGate_single_carrier_alignment_round_trip y)))

private def certifiedPhysicalTruthFields : CertifiedPhysicalTruthUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CertifiedPhysicalTruthUp.mk S G K A D I L F H C P N => [S, G, K, A, D, I, L, F, H, C, P, N]

private theorem CertifiedPhysicalTruthTasteGate_single_carrier_alignment_fields :
    forall x y : CertifiedPhysicalTruthUp,
      certifiedPhysicalTruthFields x = certifiedPhysicalTruthFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S1 G1 K1 A1 D1 I1 L1 F1 H1 C1 P1 N1 =>
      cases y with
      | mk S2 G2 K2 A2 D2 I2 L2 F2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance certifiedPhysicalTruthBHistCarrier : BHistCarrier CertifiedPhysicalTruthUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := certifiedPhysicalTruthToEventFlow
  fromEventFlow := certifiedPhysicalTruthFromEventFlow

instance certifiedPhysicalTruthChapterTasteGate :
    ChapterTasteGate CertifiedPhysicalTruthUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change certifiedPhysicalTruthFromEventFlow (certifiedPhysicalTruthToEventFlow x) = some x
    exact CertifiedPhysicalTruthTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CertifiedPhysicalTruthTasteGate_single_carrier_alignment_injective heq)

instance certifiedPhysicalTruthFieldFaithful :
    FieldFaithful CertifiedPhysicalTruthUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := certifiedPhysicalTruthFields
  field_faithful := CertifiedPhysicalTruthTasteGate_single_carrier_alignment_fields

instance certifiedPhysicalTruthNontrivial : Nontrivial CertifiedPhysicalTruthUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CertifiedPhysicalTruthUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      CertifiedPhysicalTruthUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CertifiedPhysicalTruthUp :=
  -- BEDC touchpoint anchor: BHist BMark
  certifiedPhysicalTruthChapterTasteGate

theorem CertifiedPhysicalTruthTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      certifiedPhysicalTruthDecodeBHist (certifiedPhysicalTruthEncodeBHist h) = h) ∧
      (∀ x : CertifiedPhysicalTruthUp,
        certifiedPhysicalTruthFromEventFlow (certifiedPhysicalTruthToEventFlow x) = some x) ∧
        (∀ x y : CertifiedPhysicalTruthUp,
          certifiedPhysicalTruthToEventFlow x = certifiedPhysicalTruthToEventFlow y → x = y) ∧
          certifiedPhysicalTruthEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨CertifiedPhysicalTruthTasteGate_single_carrier_alignment_decode,
      CertifiedPhysicalTruthTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => CertifiedPhysicalTruthTasteGate_single_carrier_alignment_injective heq),
      rfl⟩

end BEDC.Derived.CertifiedPhysicalTruthUp
