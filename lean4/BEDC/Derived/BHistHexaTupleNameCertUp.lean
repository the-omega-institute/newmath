import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BHistHexaTupleNameCertUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BHistHexaTupleNameCertUp : Type where
  | mk
      (source target classifier replay transport package provenance localName : BHist) :
      BHistHexaTupleNameCertUp
  deriving DecidableEq

def bHistHexaTupleNameCertEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bHistHexaTupleNameCertEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bHistHexaTupleNameCertEncodeBHist h

def bHistHexaTupleNameCertDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bHistHexaTupleNameCertDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bHistHexaTupleNameCertDecodeBHist tail)

private theorem bHistHexaTupleNameCertDecode_encode_bhist :
    ∀ h : BHist,
      bHistHexaTupleNameCertDecodeBHist
        (bHistHexaTupleNameCertEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bHistHexaTupleNameCertFields :
    BHistHexaTupleNameCertUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BHistHexaTupleNameCertUp.mk source target classifier replay transport package
      provenance localName =>
      [source, target, classifier, replay, transport, package, provenance, localName]

def bHistHexaTupleNameCertToEventFlow :
    BHistHexaTupleNameCertUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BHistHexaTupleNameCertUp.mk source target classifier replay transport package
      provenance localName =>
      (bHistHexaTupleNameCertFields
        (BHistHexaTupleNameCertUp.mk source target classifier replay transport package
          provenance localName)).map bHistHexaTupleNameCertEncodeBHist

private def bHistHexaTupleNameCertEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bHistHexaTupleNameCertEventAt index rest

def bHistHexaTupleNameCertFromEventFlow :
    EventFlow → Option BHistHexaTupleNameCertUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (BHistHexaTupleNameCertUp.mk
          (bHistHexaTupleNameCertDecodeBHist (bHistHexaTupleNameCertEventAt 0 ef))
          (bHistHexaTupleNameCertDecodeBHist (bHistHexaTupleNameCertEventAt 1 ef))
          (bHistHexaTupleNameCertDecodeBHist (bHistHexaTupleNameCertEventAt 2 ef))
          (bHistHexaTupleNameCertDecodeBHist (bHistHexaTupleNameCertEventAt 3 ef))
          (bHistHexaTupleNameCertDecodeBHist (bHistHexaTupleNameCertEventAt 4 ef))
          (bHistHexaTupleNameCertDecodeBHist (bHistHexaTupleNameCertEventAt 5 ef))
          (bHistHexaTupleNameCertDecodeBHist (bHistHexaTupleNameCertEventAt 6 ef))
          (bHistHexaTupleNameCertDecodeBHist (bHistHexaTupleNameCertEventAt 7 ef)))

private theorem bHistHexaTupleNameCert_round_trip :
    ∀ x : BHistHexaTupleNameCertUp,
      bHistHexaTupleNameCertFromEventFlow
        (bHistHexaTupleNameCertToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source target classifier replay transport package provenance localName =>
      change
        some
          (BHistHexaTupleNameCertUp.mk
            (bHistHexaTupleNameCertDecodeBHist
              (bHistHexaTupleNameCertEncodeBHist source))
            (bHistHexaTupleNameCertDecodeBHist
              (bHistHexaTupleNameCertEncodeBHist target))
            (bHistHexaTupleNameCertDecodeBHist
              (bHistHexaTupleNameCertEncodeBHist classifier))
            (bHistHexaTupleNameCertDecodeBHist
              (bHistHexaTupleNameCertEncodeBHist replay))
            (bHistHexaTupleNameCertDecodeBHist
              (bHistHexaTupleNameCertEncodeBHist transport))
            (bHistHexaTupleNameCertDecodeBHist
              (bHistHexaTupleNameCertEncodeBHist package))
            (bHistHexaTupleNameCertDecodeBHist
              (bHistHexaTupleNameCertEncodeBHist provenance))
            (bHistHexaTupleNameCertDecodeBHist
              (bHistHexaTupleNameCertEncodeBHist localName))) =
          some
            (BHistHexaTupleNameCertUp.mk source target classifier replay transport
              package provenance localName)
      rw [bHistHexaTupleNameCertDecode_encode_bhist source,
        bHistHexaTupleNameCertDecode_encode_bhist target,
        bHistHexaTupleNameCertDecode_encode_bhist classifier,
        bHistHexaTupleNameCertDecode_encode_bhist replay,
        bHistHexaTupleNameCertDecode_encode_bhist transport,
        bHistHexaTupleNameCertDecode_encode_bhist package,
        bHistHexaTupleNameCertDecode_encode_bhist provenance,
        bHistHexaTupleNameCertDecode_encode_bhist localName]

private theorem bHistHexaTupleNameCertToEventFlow_injective
    {x y : BHistHexaTupleNameCertUp} :
    bHistHexaTupleNameCertToEventFlow x =
      bHistHexaTupleNameCertToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bHistHexaTupleNameCertFromEventFlow
          (bHistHexaTupleNameCertToEventFlow x) =
        bHistHexaTupleNameCertFromEventFlow
          (bHistHexaTupleNameCertToEventFlow y) :=
    congrArg bHistHexaTupleNameCertFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (bHistHexaTupleNameCert_round_trip x).symm
      (Eq.trans hread (bHistHexaTupleNameCert_round_trip y)))

private theorem bHistHexaTupleNameCert_field_faithful :
    ∀ x y : BHistHexaTupleNameCertUp,
      bHistHexaTupleNameCertFields x =
          bHistHexaTupleNameCertFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk source₁ target₁ classifier₁ replay₁ transport₁ package₁ provenance₁ localName₁ =>
      cases y with
      | mk source₂ target₂ classifier₂ replay₂ transport₂ package₂ provenance₂ localName₂ =>
          cases hfields
          rfl

instance bHistHexaTupleNameCertBHistCarrier :
    BHistCarrier BHistHexaTupleNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bHistHexaTupleNameCertToEventFlow
  fromEventFlow := bHistHexaTupleNameCertFromEventFlow

instance bHistHexaTupleNameCertChapterTasteGate :
    ChapterTasteGate BHistHexaTupleNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bHistHexaTupleNameCertFromEventFlow
        (bHistHexaTupleNameCertToEventFlow x) = some x
    exact bHistHexaTupleNameCert_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (bHistHexaTupleNameCertToEventFlow_injective heq)

instance bHistHexaTupleNameCertFieldFaithful :
    FieldFaithful BHistHexaTupleNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bHistHexaTupleNameCertFields
  field_faithful := bHistHexaTupleNameCert_field_faithful

instance bHistHexaTupleNameCertNontrivial :
    Nontrivial BHistHexaTupleNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BHistHexaTupleNameCertUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BHistHexaTupleNameCertUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def bHistHexaTupleNameCertCarrier (h : BHist) : Prop :=
  ∃ x : BHistHexaTupleNameCertUp,
    match x with
    | BHistHexaTupleNameCertUp.mk source target classifier replay transport package
        provenance localName =>
        hsame h source ∧ hsame target target ∧ hsame classifier classifier ∧
          hsame replay replay ∧ hsame transport transport ∧ hsame package package ∧
            hsame provenance provenance ∧ hsame localName localName

theorem BHistHexaTupleNameCertUp_single_carrier_alignment_semanticNameCert :
    SemanticNameCert bHistHexaTupleNameCertCarrier bHistHexaTupleNameCertCarrier
      bHistHexaTupleNameCertCarrier hsame := by
  -- BEDC touchpoint anchor: BHist NameCert SemanticNameCert hsame
  exact
    NameCert_carrier_self_semantic_lifting {
      carrier_inhabited :=
        ⟨BHist.Empty,
          ⟨BHistHexaTupleNameCertUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
            hsame_refl BHist.Empty,
            hsame_refl BHist.Empty,
            hsame_refl BHist.Empty,
            hsame_refl BHist.Empty,
            hsame_refl BHist.Empty,
            hsame_refl BHist.Empty,
            hsame_refl BHist.Empty,
            hsame_refl BHist.Empty⟩⟩
      equiv_refl := by
        intro h _carrier
        exact hsame_refl h
      equiv_symm := by
        intro h k same
        exact hsame_symm same
      equiv_trans := by
        intro h k r sameHK sameKR
        exact hsame_trans sameHK sameKR
      carrier_respects_equiv := by
        intro h k same carrier
        cases carrier with
        | intro x hx =>
            exact
              ⟨x, hsame_trans (hsame_symm same) hx.left, hx.right⟩
    }

theorem BHistHexaTupleNameCertUp_single_carrier_alignment :
    (∀ h : BHist,
      bHistHexaTupleNameCertDecodeBHist (bHistHexaTupleNameCertEncodeBHist h) = h) ∧
      (∀ x : BHistHexaTupleNameCertUp,
        bHistHexaTupleNameCertFromEventFlow
          (bHistHexaTupleNameCertToEventFlow x) = some x) ∧
        (∀ x y : BHistHexaTupleNameCertUp,
          bHistHexaTupleNameCertToEventFlow x =
              bHistHexaTupleNameCertToEventFlow y → x = y) ∧
          bHistHexaTupleNameCertEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨bHistHexaTupleNameCertDecode_encode_bhist,
      bHistHexaTupleNameCert_round_trip,
      (fun _ _ heq => bHistHexaTupleNameCertToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.BHistHexaTupleNameCertUp
