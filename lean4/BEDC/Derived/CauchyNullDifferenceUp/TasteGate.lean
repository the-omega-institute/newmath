import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyNullDifferenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyNullDifferenceUp : Type where
  | mk (X Y D Z W T E H K P N : BHist) : CauchyNullDifferenceUp
  deriving DecidableEq

def cauchyNullDifferenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyNullDifferenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyNullDifferenceEncodeBHist h

def cauchyNullDifferenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyNullDifferenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyNullDifferenceDecodeBHist tail)

private theorem cauchyNullDifferenceDecode_encode_bhist :
    ∀ h : BHist,
      cauchyNullDifferenceDecodeBHist
        (cauchyNullDifferenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cauchyNullDifferenceFields : CauchyNullDifferenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyNullDifferenceUp.mk X Y D Z W T E H K P N =>
      [X, Y, D, Z, W, T, E, H, K, P, N]

def cauchyNullDifferenceToEventFlow : CauchyNullDifferenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyNullDifferenceFields x).map cauchyNullDifferenceEncodeBHist

def cauchyNullDifferenceFromEventFlow : EventFlow → Option CauchyNullDifferenceUp
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
  | X :: Y :: D :: Z :: W :: T :: E :: H :: K :: P :: N :: [] =>
      some
        (CauchyNullDifferenceUp.mk
          (cauchyNullDifferenceDecodeBHist X)
          (cauchyNullDifferenceDecodeBHist Y)
          (cauchyNullDifferenceDecodeBHist D)
          (cauchyNullDifferenceDecodeBHist Z)
          (cauchyNullDifferenceDecodeBHist W)
          (cauchyNullDifferenceDecodeBHist T)
          (cauchyNullDifferenceDecodeBHist E)
          (cauchyNullDifferenceDecodeBHist H)
          (cauchyNullDifferenceDecodeBHist K)
          (cauchyNullDifferenceDecodeBHist P)
          (cauchyNullDifferenceDecodeBHist N))
  | _a :: _b :: _c :: _d :: _e :: _f :: _g :: _h :: _i :: _j ::
      _k :: _l :: _rest => none

private theorem cauchyNullDifference_round_trip :
    ∀ x : CauchyNullDifferenceUp,
      cauchyNullDifferenceFromEventFlow
        (cauchyNullDifferenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X Y D Z W T E H K P N =>
      change
        some
          (CauchyNullDifferenceUp.mk
            (cauchyNullDifferenceDecodeBHist (cauchyNullDifferenceEncodeBHist X))
            (cauchyNullDifferenceDecodeBHist (cauchyNullDifferenceEncodeBHist Y))
            (cauchyNullDifferenceDecodeBHist (cauchyNullDifferenceEncodeBHist D))
            (cauchyNullDifferenceDecodeBHist (cauchyNullDifferenceEncodeBHist Z))
            (cauchyNullDifferenceDecodeBHist (cauchyNullDifferenceEncodeBHist W))
            (cauchyNullDifferenceDecodeBHist (cauchyNullDifferenceEncodeBHist T))
            (cauchyNullDifferenceDecodeBHist (cauchyNullDifferenceEncodeBHist E))
            (cauchyNullDifferenceDecodeBHist (cauchyNullDifferenceEncodeBHist H))
            (cauchyNullDifferenceDecodeBHist (cauchyNullDifferenceEncodeBHist K))
            (cauchyNullDifferenceDecodeBHist (cauchyNullDifferenceEncodeBHist P))
            (cauchyNullDifferenceDecodeBHist (cauchyNullDifferenceEncodeBHist N))) =
          some (CauchyNullDifferenceUp.mk X Y D Z W T E H K P N)
      rw [cauchyNullDifferenceDecode_encode_bhist X,
        cauchyNullDifferenceDecode_encode_bhist Y,
        cauchyNullDifferenceDecode_encode_bhist D,
        cauchyNullDifferenceDecode_encode_bhist Z,
        cauchyNullDifferenceDecode_encode_bhist W,
        cauchyNullDifferenceDecode_encode_bhist T,
        cauchyNullDifferenceDecode_encode_bhist E,
        cauchyNullDifferenceDecode_encode_bhist H,
        cauchyNullDifferenceDecode_encode_bhist K,
        cauchyNullDifferenceDecode_encode_bhist P,
        cauchyNullDifferenceDecode_encode_bhist N]

private theorem cauchyNullDifferenceToEventFlow_injective
    {x y : CauchyNullDifferenceUp} :
    cauchyNullDifferenceToEventFlow x =
      cauchyNullDifferenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyNullDifferenceFromEventFlow (cauchyNullDifferenceToEventFlow x) =
        cauchyNullDifferenceFromEventFlow (cauchyNullDifferenceToEventFlow y) :=
    congrArg cauchyNullDifferenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyNullDifference_round_trip x).symm
      (Eq.trans hread (cauchyNullDifference_round_trip y)))

private theorem cauchyNullDifference_fields_faithful :
    ∀ x y : CauchyNullDifferenceUp,
      cauchyNullDifferenceFields x = cauchyNullDifferenceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X Y D Z W T E H K P N =>
      cases y with
      | mk X' Y' D' Z' W' T' E' H' K' P' N' =>
          cases hfields
          rfl

instance cauchyNullDifferenceBHistCarrier : BHistCarrier CauchyNullDifferenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyNullDifferenceToEventFlow
  fromEventFlow := cauchyNullDifferenceFromEventFlow

instance cauchyNullDifferenceChapterTasteGate :
    ChapterTasteGate CauchyNullDifferenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyNullDifferenceFromEventFlow (cauchyNullDifferenceToEventFlow x) = some x
    exact cauchyNullDifference_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyNullDifferenceToEventFlow_injective heq)

instance cauchyNullDifferenceFieldFaithful : FieldFaithful CauchyNullDifferenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyNullDifferenceFields
  field_faithful := cauchyNullDifference_fields_faithful

instance cauchyNullDifferenceNontrivial : Nontrivial CauchyNullDifferenceUp where
  witness_pair :=
    ⟨CauchyNullDifferenceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyNullDifferenceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchyNullDifferenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyNullDifferenceChapterTasteGate

theorem CauchyNullDifferenceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        cauchyNullDifferenceDecodeBHist
          (cauchyNullDifferenceEncodeBHist h) = h) ∧
      (∀ x : CauchyNullDifferenceUp,
        cauchyNullDifferenceFromEventFlow
          (cauchyNullDifferenceToEventFlow x) = some x) ∧
      (∀ x y : CauchyNullDifferenceUp,
        cauchyNullDifferenceToEventFlow x =
          cauchyNullDifferenceToEventFlow y → x = y) ∧
      cauchyNullDifferenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact ⟨cauchyNullDifferenceDecode_encode_bhist,
    cauchyNullDifference_round_trip,
    fun _ _ heq => cauchyNullDifferenceToEventFlow_injective heq,
    rfl⟩

end BEDC.Derived.CauchyNullDifferenceUp
