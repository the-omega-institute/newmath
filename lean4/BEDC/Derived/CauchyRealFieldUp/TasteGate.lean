import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyRealFieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyRealFieldUp : Type where
  | mk (R S D Z A M I O H C P N : BHist) : CauchyRealFieldUp
  deriving DecidableEq

def cauchyRealFieldEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyRealFieldEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyRealFieldEncodeBHist h

def cauchyRealFieldDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyRealFieldDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyRealFieldDecodeBHist tail)

private theorem CauchyRealFieldTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, cauchyRealFieldDecodeBHist (cauchyRealFieldEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyRealFieldFields : CauchyRealFieldUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyRealFieldUp.mk R S D Z A M I O H C P N => [R, S, D, Z, A, M, I, O, H, C, P, N]

def cauchyRealFieldToEventFlow : CauchyRealFieldUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map cauchyRealFieldEncodeBHist (cauchyRealFieldFields x)

private def cauchyRealFieldRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyRealFieldRawAt index rest

def cauchyRealFieldFromEventFlow (flow : EventFlow) : Option CauchyRealFieldUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyRealFieldUp.mk
      (cauchyRealFieldDecodeBHist (cauchyRealFieldRawAt 0 flow))
      (cauchyRealFieldDecodeBHist (cauchyRealFieldRawAt 1 flow))
      (cauchyRealFieldDecodeBHist (cauchyRealFieldRawAt 2 flow))
      (cauchyRealFieldDecodeBHist (cauchyRealFieldRawAt 3 flow))
      (cauchyRealFieldDecodeBHist (cauchyRealFieldRawAt 4 flow))
      (cauchyRealFieldDecodeBHist (cauchyRealFieldRawAt 5 flow))
      (cauchyRealFieldDecodeBHist (cauchyRealFieldRawAt 6 flow))
      (cauchyRealFieldDecodeBHist (cauchyRealFieldRawAt 7 flow))
      (cauchyRealFieldDecodeBHist (cauchyRealFieldRawAt 8 flow))
      (cauchyRealFieldDecodeBHist (cauchyRealFieldRawAt 9 flow))
      (cauchyRealFieldDecodeBHist (cauchyRealFieldRawAt 10 flow))
      (cauchyRealFieldDecodeBHist (cauchyRealFieldRawAt 11 flow)))

private theorem CauchyRealFieldTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyRealFieldUp,
      cauchyRealFieldFromEventFlow (cauchyRealFieldToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R S D Z A M I O H C P N =>
      change
        some
          (CauchyRealFieldUp.mk
            (cauchyRealFieldDecodeBHist (cauchyRealFieldEncodeBHist R))
            (cauchyRealFieldDecodeBHist (cauchyRealFieldEncodeBHist S))
            (cauchyRealFieldDecodeBHist (cauchyRealFieldEncodeBHist D))
            (cauchyRealFieldDecodeBHist (cauchyRealFieldEncodeBHist Z))
            (cauchyRealFieldDecodeBHist (cauchyRealFieldEncodeBHist A))
            (cauchyRealFieldDecodeBHist (cauchyRealFieldEncodeBHist M))
            (cauchyRealFieldDecodeBHist (cauchyRealFieldEncodeBHist I))
            (cauchyRealFieldDecodeBHist (cauchyRealFieldEncodeBHist O))
            (cauchyRealFieldDecodeBHist (cauchyRealFieldEncodeBHist H))
            (cauchyRealFieldDecodeBHist (cauchyRealFieldEncodeBHist C))
            (cauchyRealFieldDecodeBHist (cauchyRealFieldEncodeBHist P))
            (cauchyRealFieldDecodeBHist (cauchyRealFieldEncodeBHist N))) =
          some (CauchyRealFieldUp.mk R S D Z A M I O H C P N)
      rw [CauchyRealFieldTasteGate_single_carrier_alignment_decode R,
        CauchyRealFieldTasteGate_single_carrier_alignment_decode S,
        CauchyRealFieldTasteGate_single_carrier_alignment_decode D,
        CauchyRealFieldTasteGate_single_carrier_alignment_decode Z,
        CauchyRealFieldTasteGate_single_carrier_alignment_decode A,
        CauchyRealFieldTasteGate_single_carrier_alignment_decode M,
        CauchyRealFieldTasteGate_single_carrier_alignment_decode I,
        CauchyRealFieldTasteGate_single_carrier_alignment_decode O,
        CauchyRealFieldTasteGate_single_carrier_alignment_decode H,
        CauchyRealFieldTasteGate_single_carrier_alignment_decode C,
        CauchyRealFieldTasteGate_single_carrier_alignment_decode P,
        CauchyRealFieldTasteGate_single_carrier_alignment_decode N]

private theorem CauchyRealFieldTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyRealFieldUp} :
    cauchyRealFieldToEventFlow x = cauchyRealFieldToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyRealFieldFromEventFlow (cauchyRealFieldToEventFlow x) =
        cauchyRealFieldFromEventFlow (cauchyRealFieldToEventFlow y) :=
    congrArg cauchyRealFieldFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyRealFieldTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CauchyRealFieldTasteGate_single_carrier_alignment_round_trip y)))

private theorem cauchyRealField_field_faithful :
    ∀ x y : CauchyRealFieldUp,
      cauchyRealFieldFields x = cauchyRealFieldFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x
  cases y
  cases hfields
  rfl

instance cauchyRealFieldBHistCarrier : BHistCarrier CauchyRealFieldUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyRealFieldToEventFlow
  fromEventFlow := cauchyRealFieldFromEventFlow

instance cauchyRealFieldChapterTasteGate : ChapterTasteGate CauchyRealFieldUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyRealFieldFromEventFlow (cauchyRealFieldToEventFlow x) = some x
    exact CauchyRealFieldTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyRealFieldTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance cauchyRealFieldFieldFaithful :
    FieldFaithful CauchyRealFieldUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyRealFieldFields
  field_faithful := cauchyRealField_field_faithful

instance cauchyRealFieldNontrivial : Nontrivial CauchyRealFieldUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyRealFieldUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyRealFieldUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchyRealFieldUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyRealFieldChapterTasteGate

theorem CauchyRealFieldTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchyRealFieldDecodeBHist (cauchyRealFieldEncodeBHist h) = h) ∧
      (∀ x : CauchyRealFieldUp,
        cauchyRealFieldFromEventFlow (cauchyRealFieldToEventFlow x) = some x) ∧
        (∀ x y : CauchyRealFieldUp,
          cauchyRealFieldToEventFlow x = cauchyRealFieldToEventFlow y → x = y) ∧
          cauchyRealFieldEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨CauchyRealFieldTasteGate_single_carrier_alignment_decode,
      CauchyRealFieldTasteGate_single_carrier_alignment_round_trip,
      by
        intro x y heq
        exact CauchyRealFieldTasteGate_single_carrier_alignment_toEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.CauchyRealFieldUp
