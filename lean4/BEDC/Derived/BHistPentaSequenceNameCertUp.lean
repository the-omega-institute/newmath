import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BHistPentaSequenceNameCertUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BHistPentaSequenceNameCertUp : Type where
  | mk (a b c d e route provenance nameRow : BHist) : BHistPentaSequenceNameCertUp
  deriving DecidableEq

def bHistPentaSequenceNameCertEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bHistPentaSequenceNameCertEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bHistPentaSequenceNameCertEncodeBHist h

def bHistPentaSequenceNameCertDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bHistPentaSequenceNameCertDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bHistPentaSequenceNameCertDecodeBHist tail)

private theorem bHistPentaSequenceNameCert_decode_encode :
    forall h : BHist,
      bHistPentaSequenceNameCertDecodeBHist
        (bHistPentaSequenceNameCertEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bHistPentaSequenceNameCertFields :
    BHistPentaSequenceNameCertUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BHistPentaSequenceNameCertUp.mk a b c d e route provenance nameRow =>
      [a, b, c, d, e, route, provenance, nameRow]

def bHistPentaSequenceNameCertToEventFlow :
    BHistPentaSequenceNameCertUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BHistPentaSequenceNameCertUp.mk a b c d e route provenance nameRow =>
      [bHistPentaSequenceNameCertEncodeBHist a,
        bHistPentaSequenceNameCertEncodeBHist b,
        bHistPentaSequenceNameCertEncodeBHist c,
        bHistPentaSequenceNameCertEncodeBHist d,
        bHistPentaSequenceNameCertEncodeBHist e,
        bHistPentaSequenceNameCertEncodeBHist route,
        bHistPentaSequenceNameCertEncodeBHist provenance,
        bHistPentaSequenceNameCertEncodeBHist nameRow]

def bHistPentaSequenceNameCertFromEventFlow :
    EventFlow -> Option BHistPentaSequenceNameCertUp
  -- BEDC touchpoint anchor: BHist BMark
  | a :: b :: c :: d :: e :: route :: provenance :: nameRow :: [] =>
      some
        (BHistPentaSequenceNameCertUp.mk
          (bHistPentaSequenceNameCertDecodeBHist a)
          (bHistPentaSequenceNameCertDecodeBHist b)
          (bHistPentaSequenceNameCertDecodeBHist c)
          (bHistPentaSequenceNameCertDecodeBHist d)
          (bHistPentaSequenceNameCertDecodeBHist e)
          (bHistPentaSequenceNameCertDecodeBHist route)
          (bHistPentaSequenceNameCertDecodeBHist provenance)
          (bHistPentaSequenceNameCertDecodeBHist nameRow))
  | _ => none

private theorem bHistPentaSequenceNameCert_round_trip :
    forall x : BHistPentaSequenceNameCertUp,
      bHistPentaSequenceNameCertFromEventFlow
        (bHistPentaSequenceNameCertToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk a b c d e route provenance nameRow =>
      change
        some
          (BHistPentaSequenceNameCertUp.mk
            (bHistPentaSequenceNameCertDecodeBHist
              (bHistPentaSequenceNameCertEncodeBHist a))
            (bHistPentaSequenceNameCertDecodeBHist
              (bHistPentaSequenceNameCertEncodeBHist b))
            (bHistPentaSequenceNameCertDecodeBHist
              (bHistPentaSequenceNameCertEncodeBHist c))
            (bHistPentaSequenceNameCertDecodeBHist
              (bHistPentaSequenceNameCertEncodeBHist d))
            (bHistPentaSequenceNameCertDecodeBHist
              (bHistPentaSequenceNameCertEncodeBHist e))
            (bHistPentaSequenceNameCertDecodeBHist
              (bHistPentaSequenceNameCertEncodeBHist route))
            (bHistPentaSequenceNameCertDecodeBHist
              (bHistPentaSequenceNameCertEncodeBHist provenance))
            (bHistPentaSequenceNameCertDecodeBHist
              (bHistPentaSequenceNameCertEncodeBHist nameRow))) =
          some (BHistPentaSequenceNameCertUp.mk a b c d e route provenance nameRow)
      rw [bHistPentaSequenceNameCert_decode_encode a,
        bHistPentaSequenceNameCert_decode_encode b,
        bHistPentaSequenceNameCert_decode_encode c,
        bHistPentaSequenceNameCert_decode_encode d,
        bHistPentaSequenceNameCert_decode_encode e,
        bHistPentaSequenceNameCert_decode_encode route,
        bHistPentaSequenceNameCert_decode_encode provenance,
        bHistPentaSequenceNameCert_decode_encode nameRow]

private theorem bHistPentaSequenceNameCertToEventFlow_injective
    {x y : BHistPentaSequenceNameCertUp} :
    bHistPentaSequenceNameCertToEventFlow x =
        bHistPentaSequenceNameCertToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bHistPentaSequenceNameCertFromEventFlow
          (bHistPentaSequenceNameCertToEventFlow x) =
        bHistPentaSequenceNameCertFromEventFlow
          (bHistPentaSequenceNameCertToEventFlow y) :=
    congrArg bHistPentaSequenceNameCertFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (bHistPentaSequenceNameCert_round_trip x).symm
      (Eq.trans hread (bHistPentaSequenceNameCert_round_trip y)))

private theorem bHistPentaSequenceNameCert_field_faithful :
    forall x y : BHistPentaSequenceNameCertUp,
      bHistPentaSequenceNameCertFields x =
        bHistPentaSequenceNameCertFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk a1 b1 c1 d1 e1 route1 provenance1 nameRow1 =>
      cases y with
      | mk a2 b2 c2 d2 e2 route2 provenance2 nameRow2 =>
          cases hfields
          rfl

instance bHistPentaSequenceNameCertBHistCarrier :
    BHistCarrier BHistPentaSequenceNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bHistPentaSequenceNameCertToEventFlow
  fromEventFlow := bHistPentaSequenceNameCertFromEventFlow

instance bHistPentaSequenceNameCertChapterTasteGate :
    ChapterTasteGate BHistPentaSequenceNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bHistPentaSequenceNameCertFromEventFlow
          (bHistPentaSequenceNameCertToEventFlow x) = some x
    exact bHistPentaSequenceNameCert_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (bHistPentaSequenceNameCertToEventFlow_injective heq)

instance bHistPentaSequenceNameCertFieldFaithful :
    FieldFaithful BHistPentaSequenceNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bHistPentaSequenceNameCertFields
  field_faithful := bHistPentaSequenceNameCert_field_faithful

instance bHistPentaSequenceNameCertNontrivial :
    Nontrivial BHistPentaSequenceNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BHistPentaSequenceNameCertUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BHistPentaSequenceNameCertUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BHistPentaSequenceNameCertUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bHistPentaSequenceNameCertChapterTasteGate

theorem BHistPentaSequenceNameCertCarrierAdmission
    {a b c d e route provenance nameRow : BHist} :
    bHistPentaSequenceNameCertFields
        (BHistPentaSequenceNameCertUp.mk a b c d e route provenance nameRow) =
          [a, b, c, d, e, route, provenance, nameRow] ∧
      bHistPentaSequenceNameCertEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  exact ⟨rfl, rfl⟩

end BEDC.Derived.BHistPentaSequenceNameCertUp
