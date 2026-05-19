import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BHistHeptaSequenceNameCertUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BHistHeptaSequenceNameCertUp : Type where
  | mk (a b c d e f g route provenance nameRow : BHist) :
      BHistHeptaSequenceNameCertUp
  deriving DecidableEq

def bHistHeptaSequenceNameCertEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bHistHeptaSequenceNameCertEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bHistHeptaSequenceNameCertEncodeBHist h

def bHistHeptaSequenceNameCertDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bHistHeptaSequenceNameCertDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bHistHeptaSequenceNameCertDecodeBHist tail)

private theorem BHistHeptaSequenceNameCertCarrierAdmission_decode :
    ∀ h : BHist,
      bHistHeptaSequenceNameCertDecodeBHist
        (bHistHeptaSequenceNameCertEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bHistHeptaSequenceNameCertFields :
    BHistHeptaSequenceNameCertUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BHistHeptaSequenceNameCertUp.mk a b c d e f g route provenance nameRow =>
      [a, b, c, d, e, f, g, route, provenance, nameRow]

def bHistHeptaSequenceNameCertToEventFlow :
    BHistHeptaSequenceNameCertUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BHistHeptaSequenceNameCertUp.mk a b c d e f g route provenance nameRow =>
      [[BMark.b0],
        bHistHeptaSequenceNameCertEncodeBHist a,
        [BMark.b1, BMark.b0],
        bHistHeptaSequenceNameCertEncodeBHist b,
        [BMark.b1, BMark.b1, BMark.b0],
        bHistHeptaSequenceNameCertEncodeBHist c,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bHistHeptaSequenceNameCertEncodeBHist d,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bHistHeptaSequenceNameCertEncodeBHist e,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bHistHeptaSequenceNameCertEncodeBHist f,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bHistHeptaSequenceNameCertEncodeBHist g,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        bHistHeptaSequenceNameCertEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        bHistHeptaSequenceNameCertEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        bHistHeptaSequenceNameCertEncodeBHist nameRow]

private def bHistHeptaSequenceNameCertDecodePacket
    (a b c d e f g route provenance nameRow : RawEvent) :
    BHistHeptaSequenceNameCertUp :=
  -- BEDC touchpoint anchor: BHist BMark
  BHistHeptaSequenceNameCertUp.mk
    (bHistHeptaSequenceNameCertDecodeBHist a)
    (bHistHeptaSequenceNameCertDecodeBHist b)
    (bHistHeptaSequenceNameCertDecodeBHist c)
    (bHistHeptaSequenceNameCertDecodeBHist d)
    (bHistHeptaSequenceNameCertDecodeBHist e)
    (bHistHeptaSequenceNameCertDecodeBHist f)
    (bHistHeptaSequenceNameCertDecodeBHist g)
    (bHistHeptaSequenceNameCertDecodeBHist route)
    (bHistHeptaSequenceNameCertDecodeBHist provenance)
    (bHistHeptaSequenceNameCertDecodeBHist nameRow)

def bHistHeptaSequenceNameCertFromEventFlow :
    EventFlow → Option BHistHeptaSequenceNameCertUp
  -- BEDC touchpoint anchor: BHist BMark
  | [_tag0, a, _tag1, b, _tag2, c, _tag3, d, _tag4, e, _tag5, f, _tag6, g,
      _tag7, route, _tag8, provenance, _tag9, nameRow] =>
      some
        (bHistHeptaSequenceNameCertDecodePacket a b c d e f g route provenance
          nameRow)
  | _ => none

private theorem BHistHeptaSequenceNameCertCarrierAdmission_round_trip :
    ∀ x : BHistHeptaSequenceNameCertUp,
      bHistHeptaSequenceNameCertFromEventFlow
        (bHistHeptaSequenceNameCertToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk a b c d e f g route provenance nameRow =>
      change
        some
          (bHistHeptaSequenceNameCertDecodePacket
            (bHistHeptaSequenceNameCertEncodeBHist a)
            (bHistHeptaSequenceNameCertEncodeBHist b)
            (bHistHeptaSequenceNameCertEncodeBHist c)
            (bHistHeptaSequenceNameCertEncodeBHist d)
            (bHistHeptaSequenceNameCertEncodeBHist e)
            (bHistHeptaSequenceNameCertEncodeBHist f)
            (bHistHeptaSequenceNameCertEncodeBHist g)
            (bHistHeptaSequenceNameCertEncodeBHist route)
            (bHistHeptaSequenceNameCertEncodeBHist provenance)
            (bHistHeptaSequenceNameCertEncodeBHist nameRow)) =
          some
            (BHistHeptaSequenceNameCertUp.mk a b c d e f g route provenance
              nameRow)
      unfold bHistHeptaSequenceNameCertDecodePacket
      rw [BHistHeptaSequenceNameCertCarrierAdmission_decode a,
        BHistHeptaSequenceNameCertCarrierAdmission_decode b,
        BHistHeptaSequenceNameCertCarrierAdmission_decode c,
        BHistHeptaSequenceNameCertCarrierAdmission_decode d,
        BHistHeptaSequenceNameCertCarrierAdmission_decode e,
        BHistHeptaSequenceNameCertCarrierAdmission_decode f,
        BHistHeptaSequenceNameCertCarrierAdmission_decode g,
        BHistHeptaSequenceNameCertCarrierAdmission_decode route,
        BHistHeptaSequenceNameCertCarrierAdmission_decode provenance,
        BHistHeptaSequenceNameCertCarrierAdmission_decode nameRow]

private theorem BHistHeptaSequenceNameCertCarrierAdmission_injective
    {x y : BHistHeptaSequenceNameCertUp} :
    bHistHeptaSequenceNameCertToEventFlow x =
        bHistHeptaSequenceNameCertToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bHistHeptaSequenceNameCertFromEventFlow
          (bHistHeptaSequenceNameCertToEventFlow x) =
        bHistHeptaSequenceNameCertFromEventFlow
          (bHistHeptaSequenceNameCertToEventFlow y) :=
    congrArg bHistHeptaSequenceNameCertFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BHistHeptaSequenceNameCertCarrierAdmission_round_trip x).symm
      (Eq.trans hread (BHistHeptaSequenceNameCertCarrierAdmission_round_trip y)))

private theorem BHistHeptaSequenceNameCertCarrierAdmission_field_faithful :
    ∀ x y : BHistHeptaSequenceNameCertUp,
      bHistHeptaSequenceNameCertFields x =
          bHistHeptaSequenceNameCertFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk a1 b1 c1 d1 e1 f1 g1 route1 provenance1 nameRow1 =>
      cases y with
      | mk a2 b2 c2 d2 e2 f2 g2 route2 provenance2 nameRow2 =>
          cases hfields
          rfl

instance bHistHeptaSequenceNameCertBHistCarrier :
    BHistCarrier BHistHeptaSequenceNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bHistHeptaSequenceNameCertToEventFlow
  fromEventFlow := bHistHeptaSequenceNameCertFromEventFlow

instance bHistHeptaSequenceNameCertChapterTasteGate :
    ChapterTasteGate BHistHeptaSequenceNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bHistHeptaSequenceNameCertFromEventFlow
          (bHistHeptaSequenceNameCertToEventFlow x) = some x
    exact BHistHeptaSequenceNameCertCarrierAdmission_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BHistHeptaSequenceNameCertCarrierAdmission_injective heq)

instance bHistHeptaSequenceNameCertFieldFaithful :
    FieldFaithful BHistHeptaSequenceNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bHistHeptaSequenceNameCertFields
  field_faithful := BHistHeptaSequenceNameCertCarrierAdmission_field_faithful

instance bHistHeptaSequenceNameCertNontrivial :
    Nontrivial BHistHeptaSequenceNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BHistHeptaSequenceNameCertUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      BHistHeptaSequenceNameCertUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem BHistHeptaSequenceNameCertCarrierAdmission
    {a b c d e f g route provenance nameRow : BHist} :
    bHistHeptaSequenceNameCertFields
        (BHistHeptaSequenceNameCertUp.mk a b c d e f g route provenance nameRow) =
      [a, b, c, d, e, f, g, route, provenance, nameRow] ∧
        bHistHeptaSequenceNameCertEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · rfl
  · rfl

end BEDC.Derived.BHistHeptaSequenceNameCertUp
