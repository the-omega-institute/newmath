import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyRealFieldUp.TasteGate

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

private theorem cauchyRealFieldDecode_encode_bhist :
    ∀ h : BHist, cauchyRealFieldDecodeBHist (cauchyRealFieldEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cauchyRealFieldFields : CauchyRealFieldUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyRealFieldUp.mk R S D Z A M I O H C P N =>
      [R, S, D, Z, A, M, I, O, H, C, P, N]

def cauchyRealFieldToEventFlow : CauchyRealFieldUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyRealFieldFields x).map cauchyRealFieldEncodeBHist

def cauchyRealFieldFromEventFlow : EventFlow → Option CauchyRealFieldUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | r :: rest0 =>
      match rest0 with
      | [] => none
      | s :: rest1 =>
          match rest1 with
          | [] => none
          | d :: rest2 =>
              match rest2 with
              | [] => none
              | z :: rest3 =>
                  match rest3 with
                  | [] => none
                  | a :: rest4 =>
                      match rest4 with
                      | [] => none
                      | m :: rest5 =>
                          match rest5 with
                          | [] => none
                          | i :: rest6 =>
                              match rest6 with
                              | [] => none
                              | o :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | h :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | c :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | p :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | n :: rest11 =>
                                                  match rest11 with
                                                  | [] =>
                                                      some (CauchyRealFieldUp.mk (cauchyRealFieldDecodeBHist r) (cauchyRealFieldDecodeBHist s) (cauchyRealFieldDecodeBHist d) (cauchyRealFieldDecodeBHist z) (cauchyRealFieldDecodeBHist a) (cauchyRealFieldDecodeBHist m) (cauchyRealFieldDecodeBHist i) (cauchyRealFieldDecodeBHist o) (cauchyRealFieldDecodeBHist h) (cauchyRealFieldDecodeBHist c) (cauchyRealFieldDecodeBHist p) (cauchyRealFieldDecodeBHist n))
                                                  | _ :: _ => none
private theorem cauchyRealField_round_trip :
    ∀ x : CauchyRealFieldUp,
      cauchyRealFieldFromEventFlow (cauchyRealFieldToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R S D Z A M I O H C P N =>
      change
        some (CauchyRealFieldUp.mk (cauchyRealFieldDecodeBHist (cauchyRealFieldEncodeBHist R)) (cauchyRealFieldDecodeBHist (cauchyRealFieldEncodeBHist S)) (cauchyRealFieldDecodeBHist (cauchyRealFieldEncodeBHist D)) (cauchyRealFieldDecodeBHist (cauchyRealFieldEncodeBHist Z)) (cauchyRealFieldDecodeBHist (cauchyRealFieldEncodeBHist A)) (cauchyRealFieldDecodeBHist (cauchyRealFieldEncodeBHist M)) (cauchyRealFieldDecodeBHist (cauchyRealFieldEncodeBHist I)) (cauchyRealFieldDecodeBHist (cauchyRealFieldEncodeBHist O)) (cauchyRealFieldDecodeBHist (cauchyRealFieldEncodeBHist H)) (cauchyRealFieldDecodeBHist (cauchyRealFieldEncodeBHist C)) (cauchyRealFieldDecodeBHist (cauchyRealFieldEncodeBHist P)) (cauchyRealFieldDecodeBHist (cauchyRealFieldEncodeBHist N))) =
          some (CauchyRealFieldUp.mk R S D Z A M I O H C P N)
      rw [cauchyRealFieldDecode_encode_bhist R,
        cauchyRealFieldDecode_encode_bhist S,
        cauchyRealFieldDecode_encode_bhist D,
        cauchyRealFieldDecode_encode_bhist Z,
        cauchyRealFieldDecode_encode_bhist A,
        cauchyRealFieldDecode_encode_bhist M,
        cauchyRealFieldDecode_encode_bhist I,
        cauchyRealFieldDecode_encode_bhist O,
        cauchyRealFieldDecode_encode_bhist H,
        cauchyRealFieldDecode_encode_bhist C,
        cauchyRealFieldDecode_encode_bhist P,
        cauchyRealFieldDecode_encode_bhist N]

private theorem cauchyRealFieldToEventFlow_injective
    {x y : CauchyRealFieldUp} :
    cauchyRealFieldToEventFlow x = cauchyRealFieldToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyRealFieldFromEventFlow (cauchyRealFieldToEventFlow x) =
        cauchyRealFieldFromEventFlow (cauchyRealFieldToEventFlow y) :=
    congrArg cauchyRealFieldFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyRealField_round_trip x).symm
      (Eq.trans hread (cauchyRealField_round_trip y)))

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

instance cauchyRealFieldChapterTasteGate :
    ChapterTasteGate CauchyRealFieldUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyRealFieldFromEventFlow (cauchyRealFieldToEventFlow x) = some x
    exact cauchyRealField_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyRealFieldToEventFlow_injective heq)

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

theorem CauchyRealFieldUpTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchyRealFieldDecodeBHist (cauchyRealFieldEncodeBHist h) = h) ∧
      (∀ x : CauchyRealFieldUp,
        cauchyRealFieldFromEventFlow (cauchyRealFieldToEventFlow x) = some x) ∧
        (∀ x y : CauchyRealFieldUp,
          cauchyRealFieldToEventFlow x = cauchyRealFieldToEventFlow y → x = y) ∧
          cauchyRealFieldEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨cauchyRealFieldDecode_encode_bhist,
      cauchyRealField_round_trip,
      (fun _ _ heq => cauchyRealFieldToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CauchyRealFieldUp.TasteGate
