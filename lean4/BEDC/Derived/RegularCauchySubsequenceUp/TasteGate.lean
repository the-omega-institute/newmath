import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchySubsequenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchySubsequenceUp : Type where
  | mk
      (source reindex windows radius «seal» sameRows routeRows provenance localCert endpoint :
        BHist) : RegularCauchySubsequenceUp
  deriving DecidableEq

def regularCauchySubsequenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchySubsequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchySubsequenceEncodeBHist h

def regularCauchySubsequenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchySubsequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchySubsequenceDecodeBHist tail)

private theorem regularCauchySubsequenceDecode_encode_bhist :
    ∀ h : BHist,
      regularCauchySubsequenceDecodeBHist
        (regularCauchySubsequenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def regularCauchySubsequenceFields : RegularCauchySubsequenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchySubsequenceUp.mk source reindex windows radius «seal» sameRows routeRows
      provenance localCert endpoint =>
      [source, reindex, windows, radius, «seal», sameRows, routeRows, provenance, localCert,
        endpoint]

def regularCauchySubsequenceToEventFlow : RegularCauchySubsequenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (regularCauchySubsequenceFields x).map regularCauchySubsequenceEncodeBHist

def regularCauchySubsequenceFromEventFlow : EventFlow → Option RegularCauchySubsequenceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _a :: [] => none
  | _a :: _b :: [] => none
  | _a :: _b :: _c :: [] => none
  | _a :: _b :: _c :: _d :: [] => none
  | _a :: _b :: _c :: _d :: _e :: [] => none
  | _a :: _b :: _c :: _d :: _e :: _f :: [] => none
  | _a :: _b :: _c :: _d :: _e :: _f :: _g :: [] => none
  | _a :: _b :: _c :: _d :: _e :: _f :: _g :: _h :: [] => none
  | _a :: _b :: _c :: _d :: _e :: _f :: _g :: _h :: _i :: [] => none
  | source :: reindex :: windows :: radius :: sealRow :: sameRows :: routeRows :: provenance ::
      localCert :: endpoint :: [] =>
      some
        (RegularCauchySubsequenceUp.mk
          (regularCauchySubsequenceDecodeBHist source)
          (regularCauchySubsequenceDecodeBHist reindex)
          (regularCauchySubsequenceDecodeBHist windows)
          (regularCauchySubsequenceDecodeBHist radius)
          (regularCauchySubsequenceDecodeBHist sealRow)
          (regularCauchySubsequenceDecodeBHist sameRows)
          (regularCauchySubsequenceDecodeBHist routeRows)
          (regularCauchySubsequenceDecodeBHist provenance)
          (regularCauchySubsequenceDecodeBHist localCert)
          (regularCauchySubsequenceDecodeBHist endpoint))
  | _a :: _b :: _c :: _d :: _e :: _f :: _g :: _h :: _i :: _j :: _k :: _rest => none

private theorem regularCauchySubsequence_round_trip :
    ∀ x : RegularCauchySubsequenceUp,
      regularCauchySubsequenceFromEventFlow
        (regularCauchySubsequenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source reindex windows radius sealRow sameRows routeRows provenance localCert endpoint =>
      change
        some
          (RegularCauchySubsequenceUp.mk
            (regularCauchySubsequenceDecodeBHist
              (regularCauchySubsequenceEncodeBHist source))
            (regularCauchySubsequenceDecodeBHist
              (regularCauchySubsequenceEncodeBHist reindex))
            (regularCauchySubsequenceDecodeBHist
              (regularCauchySubsequenceEncodeBHist windows))
            (regularCauchySubsequenceDecodeBHist
              (regularCauchySubsequenceEncodeBHist radius))
            (regularCauchySubsequenceDecodeBHist
              (regularCauchySubsequenceEncodeBHist sealRow))
            (regularCauchySubsequenceDecodeBHist
              (regularCauchySubsequenceEncodeBHist sameRows))
            (regularCauchySubsequenceDecodeBHist
              (regularCauchySubsequenceEncodeBHist routeRows))
            (regularCauchySubsequenceDecodeBHist
              (regularCauchySubsequenceEncodeBHist provenance))
            (regularCauchySubsequenceDecodeBHist
              (regularCauchySubsequenceEncodeBHist localCert))
            (regularCauchySubsequenceDecodeBHist
              (regularCauchySubsequenceEncodeBHist endpoint))) =
          some
            (RegularCauchySubsequenceUp.mk source reindex windows radius sealRow sameRows
              routeRows provenance localCert endpoint)
      rw [regularCauchySubsequenceDecode_encode_bhist source,
        regularCauchySubsequenceDecode_encode_bhist reindex,
        regularCauchySubsequenceDecode_encode_bhist windows,
        regularCauchySubsequenceDecode_encode_bhist radius,
        regularCauchySubsequenceDecode_encode_bhist sealRow,
        regularCauchySubsequenceDecode_encode_bhist sameRows,
        regularCauchySubsequenceDecode_encode_bhist routeRows,
        regularCauchySubsequenceDecode_encode_bhist provenance,
        regularCauchySubsequenceDecode_encode_bhist localCert,
        regularCauchySubsequenceDecode_encode_bhist endpoint]

private theorem regularCauchySubsequenceToEventFlow_injective
    {x y : RegularCauchySubsequenceUp} :
    regularCauchySubsequenceToEventFlow x =
      regularCauchySubsequenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchySubsequenceFromEventFlow
          (regularCauchySubsequenceToEventFlow x) =
        regularCauchySubsequenceFromEventFlow
          (regularCauchySubsequenceToEventFlow y) :=
    congrArg regularCauchySubsequenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchySubsequence_round_trip x).symm
      (Eq.trans hread (regularCauchySubsequence_round_trip y)))

private theorem regularCauchySubsequence_fields_faithful :
    ∀ x y : RegularCauchySubsequenceUp,
      regularCauchySubsequenceFields x = regularCauchySubsequenceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk source reindex windows radius sealRow sameRows routeRows provenance localCert endpoint =>
      cases y with
      | mk source' reindex' windows' radius' sealRow' sameRows' routeRows' provenance'
          localCert' endpoint' =>
          cases hfields
          rfl

instance regularCauchySubsequenceBHistCarrier : BHistCarrier RegularCauchySubsequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchySubsequenceToEventFlow
  fromEventFlow := regularCauchySubsequenceFromEventFlow

instance regularCauchySubsequenceChapterTasteGate :
    ChapterTasteGate RegularCauchySubsequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchySubsequenceFromEventFlow
        (regularCauchySubsequenceToEventFlow x) = some x
    exact regularCauchySubsequence_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchySubsequenceToEventFlow_injective heq)

instance regularCauchySubsequenceFieldFaithful :
    FieldFaithful RegularCauchySubsequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchySubsequenceFields
  field_faithful := regularCauchySubsequence_fields_faithful

instance regularCauchySubsequenceNontrivial : Nontrivial RegularCauchySubsequenceUp where
  witness_pair :=
    ⟨RegularCauchySubsequenceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RegularCauchySubsequenceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RegularCauchySubsequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchySubsequenceChapterTasteGate

theorem RegularCauchySubsequenceTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RegularCauchySubsequenceUp) ∧
      Nonempty (FieldFaithful RegularCauchySubsequenceUp) ∧
      Nonempty (Nontrivial RegularCauchySubsequenceUp) ∧
      (∀ h : BHist,
        regularCauchySubsequenceDecodeBHist
          (regularCauchySubsequenceEncodeBHist h) = h) ∧
      (∀ x : RegularCauchySubsequenceUp,
        regularCauchySubsequenceFromEventFlow
          (regularCauchySubsequenceToEventFlow x) = some x) ∧
      (∀ x y : RegularCauchySubsequenceUp,
        regularCauchySubsequenceToEventFlow x =
          regularCauchySubsequenceToEventFlow y -> x = y) ∧
      regularCauchySubsequenceEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨regularCauchySubsequenceChapterTasteGate⟩,
      ⟨regularCauchySubsequenceFieldFaithful⟩,
      ⟨regularCauchySubsequenceNontrivial⟩,
      regularCauchySubsequenceDecode_encode_bhist,
      regularCauchySubsequence_round_trip,
      fun _ _ heq => regularCauchySubsequenceToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.RegularCauchySubsequenceUp
