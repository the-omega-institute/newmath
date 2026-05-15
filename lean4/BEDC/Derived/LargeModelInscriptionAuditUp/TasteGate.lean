import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LargeModelInscriptionAuditUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LargeModelInscriptionAuditUp : Type where
  | mk (O C V R T K H P N : BHist) : LargeModelInscriptionAuditUp
  deriving DecidableEq

def largeModelInscriptionAuditEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: largeModelInscriptionAuditEncodeBHist h
  | BHist.e1 h => BMark.b1 :: largeModelInscriptionAuditEncodeBHist h

def largeModelInscriptionAuditDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (largeModelInscriptionAuditDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (largeModelInscriptionAuditDecodeBHist tail)

private theorem largeModelInscriptionAuditDecode_encode_bhist :
    ∀ h : BHist,
      largeModelInscriptionAuditDecodeBHist
        (largeModelInscriptionAuditEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def largeModelInscriptionAuditFields :
    LargeModelInscriptionAuditUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LargeModelInscriptionAuditUp.mk O C V R T K H P N =>
      [O, C, V, R, T, K, H, P, N]

def largeModelInscriptionAuditToEventFlow :
    LargeModelInscriptionAuditUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (largeModelInscriptionAuditFields x).map largeModelInscriptionAuditEncodeBHist

def largeModelInscriptionAuditFromEventFlow :
    EventFlow → Option LargeModelInscriptionAuditUp
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
  | O :: C :: V :: R :: T :: K :: H :: P :: N :: [] =>
      some
        (LargeModelInscriptionAuditUp.mk
          (largeModelInscriptionAuditDecodeBHist O)
          (largeModelInscriptionAuditDecodeBHist C)
          (largeModelInscriptionAuditDecodeBHist V)
          (largeModelInscriptionAuditDecodeBHist R)
          (largeModelInscriptionAuditDecodeBHist T)
          (largeModelInscriptionAuditDecodeBHist K)
          (largeModelInscriptionAuditDecodeBHist H)
          (largeModelInscriptionAuditDecodeBHist P)
          (largeModelInscriptionAuditDecodeBHist N))
  | _a :: _b :: _c :: _d :: _e :: _f :: _g :: _h :: _i :: _j :: _rest => none

private theorem largeModelInscriptionAudit_round_trip :
    ∀ x : LargeModelInscriptionAuditUp,
      largeModelInscriptionAuditFromEventFlow
        (largeModelInscriptionAuditToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk O C V R T K H P N =>
      change
        some
          (LargeModelInscriptionAuditUp.mk
            (largeModelInscriptionAuditDecodeBHist
              (largeModelInscriptionAuditEncodeBHist O))
            (largeModelInscriptionAuditDecodeBHist
              (largeModelInscriptionAuditEncodeBHist C))
            (largeModelInscriptionAuditDecodeBHist
              (largeModelInscriptionAuditEncodeBHist V))
            (largeModelInscriptionAuditDecodeBHist
              (largeModelInscriptionAuditEncodeBHist R))
            (largeModelInscriptionAuditDecodeBHist
              (largeModelInscriptionAuditEncodeBHist T))
            (largeModelInscriptionAuditDecodeBHist
              (largeModelInscriptionAuditEncodeBHist K))
            (largeModelInscriptionAuditDecodeBHist
              (largeModelInscriptionAuditEncodeBHist H))
            (largeModelInscriptionAuditDecodeBHist
              (largeModelInscriptionAuditEncodeBHist P))
            (largeModelInscriptionAuditDecodeBHist
              (largeModelInscriptionAuditEncodeBHist N))) =
          some (LargeModelInscriptionAuditUp.mk O C V R T K H P N)
      rw [largeModelInscriptionAuditDecode_encode_bhist O,
        largeModelInscriptionAuditDecode_encode_bhist C,
        largeModelInscriptionAuditDecode_encode_bhist V,
        largeModelInscriptionAuditDecode_encode_bhist R,
        largeModelInscriptionAuditDecode_encode_bhist T,
        largeModelInscriptionAuditDecode_encode_bhist K,
        largeModelInscriptionAuditDecode_encode_bhist H,
        largeModelInscriptionAuditDecode_encode_bhist P,
        largeModelInscriptionAuditDecode_encode_bhist N]

private theorem largeModelInscriptionAuditToEventFlow_injective
    {x y : LargeModelInscriptionAuditUp} :
    largeModelInscriptionAuditToEventFlow x =
      largeModelInscriptionAuditToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      largeModelInscriptionAuditFromEventFlow
          (largeModelInscriptionAuditToEventFlow x) =
        largeModelInscriptionAuditFromEventFlow
          (largeModelInscriptionAuditToEventFlow y) :=
    congrArg largeModelInscriptionAuditFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (largeModelInscriptionAudit_round_trip x).symm
      (Eq.trans hread (largeModelInscriptionAudit_round_trip y)))

private theorem largeModelInscriptionAudit_fields_faithful :
    ∀ x y : LargeModelInscriptionAuditUp,
      largeModelInscriptionAuditFields x = largeModelInscriptionAuditFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk O C V R T K H P N =>
      cases y with
      | mk O' C' V' R' T' K' H' P' N' =>
          cases hfields
          rfl

instance largeModelInscriptionAuditBHistCarrier :
    BHistCarrier LargeModelInscriptionAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := largeModelInscriptionAuditToEventFlow
  fromEventFlow := largeModelInscriptionAuditFromEventFlow

instance largeModelInscriptionAuditChapterTasteGate :
    ChapterTasteGate LargeModelInscriptionAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      largeModelInscriptionAuditFromEventFlow
        (largeModelInscriptionAuditToEventFlow x) = some x
    exact largeModelInscriptionAudit_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (largeModelInscriptionAuditToEventFlow_injective heq)

instance largeModelInscriptionAuditFieldFaithful :
    FieldFaithful LargeModelInscriptionAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := largeModelInscriptionAuditFields
  field_faithful := largeModelInscriptionAudit_fields_faithful

instance largeModelInscriptionAuditNontrivial :
    Nontrivial LargeModelInscriptionAuditUp where
  witness_pair :=
    ⟨LargeModelInscriptionAuditUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      LargeModelInscriptionAuditUp.mk BHist.Empty BHist.Empty (BHist.e0 BHist.Empty)
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate LargeModelInscriptionAuditUp :=
  -- BEDC touchpoint anchor: BHist BMark
  largeModelInscriptionAuditChapterTasteGate

theorem LargeModelInscriptionAuditTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        largeModelInscriptionAuditDecodeBHist
          (largeModelInscriptionAuditEncodeBHist h) = h) ∧
      (∀ x : LargeModelInscriptionAuditUp,
        largeModelInscriptionAuditFromEventFlow
          (largeModelInscriptionAuditToEventFlow x) = some x) ∧
      (∀ x y : LargeModelInscriptionAuditUp,
        largeModelInscriptionAuditToEventFlow x =
          largeModelInscriptionAuditToEventFlow y → x = y) ∧
      largeModelInscriptionAuditEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact ⟨largeModelInscriptionAuditDecode_encode_bhist,
    largeModelInscriptionAudit_round_trip,
    fun _ _ heq => largeModelInscriptionAuditToEventFlow_injective heq,
    rfl⟩

end BEDC.Derived.LargeModelInscriptionAuditUp
