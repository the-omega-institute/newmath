import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyNetFilterCorrespondenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyNetFilterCorrespondenceUp : Type where
  | mk (K F U W R E J H C P N : BHist) : CauchyNetFilterCorrespondenceUp
  deriving DecidableEq

def cauchyNetFilterCorrespondenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyNetFilterCorrespondenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyNetFilterCorrespondenceEncodeBHist h

def cauchyNetFilterCorrespondenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyNetFilterCorrespondenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyNetFilterCorrespondenceDecodeBHist tail)

private theorem cauchyNetFilterCorrespondenceDecode_encode_bhist :
    ∀ h : BHist,
      cauchyNetFilterCorrespondenceDecodeBHist
        (cauchyNetFilterCorrespondenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cauchyNetFilterCorrespondenceFields :
    CauchyNetFilterCorrespondenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyNetFilterCorrespondenceUp.mk K F U W R E J H C P N =>
      [K, F, U, W, R, E, J, H, C, P, N]

def cauchyNetFilterCorrespondenceToEventFlow :
    CauchyNetFilterCorrespondenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyNetFilterCorrespondenceFields x).map
      cauchyNetFilterCorrespondenceEncodeBHist

def cauchyNetFilterCorrespondenceFromEventFlow :
    EventFlow → Option CauchyNetFilterCorrespondenceUp
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
  | _a :: _b :: _c :: _d :: _e :: _f :: _g :: _h :: _i :: _j :: [] => none
  | K :: F :: U :: W :: R :: E :: J :: H :: C :: P :: N :: [] =>
      some
        (CauchyNetFilterCorrespondenceUp.mk
          (cauchyNetFilterCorrespondenceDecodeBHist K)
          (cauchyNetFilterCorrespondenceDecodeBHist F)
          (cauchyNetFilterCorrespondenceDecodeBHist U)
          (cauchyNetFilterCorrespondenceDecodeBHist W)
          (cauchyNetFilterCorrespondenceDecodeBHist R)
          (cauchyNetFilterCorrespondenceDecodeBHist E)
          (cauchyNetFilterCorrespondenceDecodeBHist J)
          (cauchyNetFilterCorrespondenceDecodeBHist H)
          (cauchyNetFilterCorrespondenceDecodeBHist C)
          (cauchyNetFilterCorrespondenceDecodeBHist P)
          (cauchyNetFilterCorrespondenceDecodeBHist N))
  | _a :: _b :: _c :: _d :: _e :: _f :: _g :: _h :: _i :: _j ::
      _k :: _l :: _rest => none

private theorem cauchyNetFilterCorrespondence_round_trip :
    ∀ x : CauchyNetFilterCorrespondenceUp,
      cauchyNetFilterCorrespondenceFromEventFlow
        (cauchyNetFilterCorrespondenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K F U W R E J H C P N =>
      change
        some
          (CauchyNetFilterCorrespondenceUp.mk
            (cauchyNetFilterCorrespondenceDecodeBHist
              (cauchyNetFilterCorrespondenceEncodeBHist K))
            (cauchyNetFilterCorrespondenceDecodeBHist
              (cauchyNetFilterCorrespondenceEncodeBHist F))
            (cauchyNetFilterCorrespondenceDecodeBHist
              (cauchyNetFilterCorrespondenceEncodeBHist U))
            (cauchyNetFilterCorrespondenceDecodeBHist
              (cauchyNetFilterCorrespondenceEncodeBHist W))
            (cauchyNetFilterCorrespondenceDecodeBHist
              (cauchyNetFilterCorrespondenceEncodeBHist R))
            (cauchyNetFilterCorrespondenceDecodeBHist
              (cauchyNetFilterCorrespondenceEncodeBHist E))
            (cauchyNetFilterCorrespondenceDecodeBHist
              (cauchyNetFilterCorrespondenceEncodeBHist J))
            (cauchyNetFilterCorrespondenceDecodeBHist
              (cauchyNetFilterCorrespondenceEncodeBHist H))
            (cauchyNetFilterCorrespondenceDecodeBHist
              (cauchyNetFilterCorrespondenceEncodeBHist C))
            (cauchyNetFilterCorrespondenceDecodeBHist
              (cauchyNetFilterCorrespondenceEncodeBHist P))
            (cauchyNetFilterCorrespondenceDecodeBHist
              (cauchyNetFilterCorrespondenceEncodeBHist N))) =
          some (CauchyNetFilterCorrespondenceUp.mk K F U W R E J H C P N)
      rw [cauchyNetFilterCorrespondenceDecode_encode_bhist K,
        cauchyNetFilterCorrespondenceDecode_encode_bhist F,
        cauchyNetFilterCorrespondenceDecode_encode_bhist U,
        cauchyNetFilterCorrespondenceDecode_encode_bhist W,
        cauchyNetFilterCorrespondenceDecode_encode_bhist R,
        cauchyNetFilterCorrespondenceDecode_encode_bhist E,
        cauchyNetFilterCorrespondenceDecode_encode_bhist J,
        cauchyNetFilterCorrespondenceDecode_encode_bhist H,
        cauchyNetFilterCorrespondenceDecode_encode_bhist C,
        cauchyNetFilterCorrespondenceDecode_encode_bhist P,
        cauchyNetFilterCorrespondenceDecode_encode_bhist N]

private theorem cauchyNetFilterCorrespondenceToEventFlow_injective
    {x y : CauchyNetFilterCorrespondenceUp} :
    cauchyNetFilterCorrespondenceToEventFlow x =
      cauchyNetFilterCorrespondenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyNetFilterCorrespondenceFromEventFlow
          (cauchyNetFilterCorrespondenceToEventFlow x) =
        cauchyNetFilterCorrespondenceFromEventFlow
          (cauchyNetFilterCorrespondenceToEventFlow y) :=
    congrArg cauchyNetFilterCorrespondenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyNetFilterCorrespondence_round_trip x).symm
      (Eq.trans hread (cauchyNetFilterCorrespondence_round_trip y)))

private theorem cauchyNetFilterCorrespondence_fields_faithful :
    ∀ x y : CauchyNetFilterCorrespondenceUp,
      cauchyNetFilterCorrespondenceFields x =
        cauchyNetFilterCorrespondenceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk K F U W R E J H C P N =>
      cases y with
      | mk K' F' U' W' R' E' J' H' C' P' N' =>
          cases hfields
          rfl

instance cauchyNetFilterCorrespondenceBHistCarrier :
    BHistCarrier CauchyNetFilterCorrespondenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyNetFilterCorrespondenceToEventFlow
  fromEventFlow := cauchyNetFilterCorrespondenceFromEventFlow

instance cauchyNetFilterCorrespondenceChapterTasteGate :
    ChapterTasteGate CauchyNetFilterCorrespondenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyNetFilterCorrespondenceFromEventFlow
        (cauchyNetFilterCorrespondenceToEventFlow x) = some x
    exact cauchyNetFilterCorrespondence_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyNetFilterCorrespondenceToEventFlow_injective heq)

instance cauchyNetFilterCorrespondenceFieldFaithful :
    FieldFaithful CauchyNetFilterCorrespondenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyNetFilterCorrespondenceFields
  field_faithful := cauchyNetFilterCorrespondence_fields_faithful

instance cauchyNetFilterCorrespondenceNontrivial :
    Nontrivial CauchyNetFilterCorrespondenceUp where
  witness_pair :=
    ⟨CauchyNetFilterCorrespondenceUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      CauchyNetFilterCorrespondenceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchyNetFilterCorrespondenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyNetFilterCorrespondenceChapterTasteGate

theorem CauchyNetFilterCorrespondenceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        cauchyNetFilterCorrespondenceDecodeBHist
          (cauchyNetFilterCorrespondenceEncodeBHist h) = h) ∧
      (∀ x : CauchyNetFilterCorrespondenceUp,
        cauchyNetFilterCorrespondenceFromEventFlow
          (cauchyNetFilterCorrespondenceToEventFlow x) = some x) ∧
      (∀ x y : CauchyNetFilterCorrespondenceUp,
        cauchyNetFilterCorrespondenceToEventFlow x =
          cauchyNetFilterCorrespondenceToEventFlow y → x = y) ∧
      cauchyNetFilterCorrespondenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact ⟨cauchyNetFilterCorrespondenceDecode_encode_bhist,
    cauchyNetFilterCorrespondence_round_trip,
    fun _ _ heq => cauchyNetFilterCorrespondenceToEventFlow_injective heq,
    rfl⟩

end BEDC.Derived.CauchyNetFilterCorrespondenceUp
