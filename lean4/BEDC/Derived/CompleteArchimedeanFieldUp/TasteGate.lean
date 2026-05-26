import BEDC.Derived.CompleteArchimedeanFieldUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompleteArchimedeanFieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def completeArchimedeanFieldEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: completeArchimedeanFieldEncodeBHist h
  | BHist.e1 h => BMark.b1 :: completeArchimedeanFieldEncodeBHist h

def completeArchimedeanFieldDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (completeArchimedeanFieldDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (completeArchimedeanFieldDecodeBHist tail)

private theorem CompleteArchimedeanFieldTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      completeArchimedeanFieldDecodeBHist (completeArchimedeanFieldEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def completeArchimedeanFieldFields : BEDC.Derived.CompleteArchimedeanFieldUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompleteArchimedeanFieldUp.mk R O A D W Q K H C P N =>
      [R, O, A, D, W, Q, K, H, C, P, N]

def completeArchimedeanFieldToEventFlow :
    BEDC.Derived.CompleteArchimedeanFieldUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (completeArchimedeanFieldFields x).map completeArchimedeanFieldEncodeBHist

private def completeArchimedeanFieldEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _ => event
  | Nat.succ _, [] => []
  | Nat.succ index, _ :: rest => completeArchimedeanFieldEventAt index rest

def completeArchimedeanFieldFromEventFlow
    (ef : EventFlow) : Option BEDC.Derived.CompleteArchimedeanFieldUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CompleteArchimedeanFieldUp.mk
      (completeArchimedeanFieldDecodeBHist (completeArchimedeanFieldEventAt 0 ef))
      (completeArchimedeanFieldDecodeBHist (completeArchimedeanFieldEventAt 1 ef))
      (completeArchimedeanFieldDecodeBHist (completeArchimedeanFieldEventAt 2 ef))
      (completeArchimedeanFieldDecodeBHist (completeArchimedeanFieldEventAt 3 ef))
      (completeArchimedeanFieldDecodeBHist (completeArchimedeanFieldEventAt 4 ef))
      (completeArchimedeanFieldDecodeBHist (completeArchimedeanFieldEventAt 5 ef))
      (completeArchimedeanFieldDecodeBHist (completeArchimedeanFieldEventAt 6 ef))
      (completeArchimedeanFieldDecodeBHist (completeArchimedeanFieldEventAt 7 ef))
      (completeArchimedeanFieldDecodeBHist (completeArchimedeanFieldEventAt 8 ef))
      (completeArchimedeanFieldDecodeBHist (completeArchimedeanFieldEventAt 9 ef))
      (completeArchimedeanFieldDecodeBHist (completeArchimedeanFieldEventAt 10 ef)))

private theorem CompleteArchimedeanFieldTasteGate_single_carrier_alignment_round_trip
    (x : BEDC.Derived.CompleteArchimedeanFieldUp) :
    completeArchimedeanFieldFromEventFlow (completeArchimedeanFieldToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk R O A D W Q K H C P N =>
      change
        some
          (CompleteArchimedeanFieldUp.mk
            (completeArchimedeanFieldDecodeBHist (completeArchimedeanFieldEncodeBHist R))
            (completeArchimedeanFieldDecodeBHist (completeArchimedeanFieldEncodeBHist O))
            (completeArchimedeanFieldDecodeBHist (completeArchimedeanFieldEncodeBHist A))
            (completeArchimedeanFieldDecodeBHist (completeArchimedeanFieldEncodeBHist D))
            (completeArchimedeanFieldDecodeBHist (completeArchimedeanFieldEncodeBHist W))
            (completeArchimedeanFieldDecodeBHist (completeArchimedeanFieldEncodeBHist Q))
            (completeArchimedeanFieldDecodeBHist (completeArchimedeanFieldEncodeBHist K))
            (completeArchimedeanFieldDecodeBHist (completeArchimedeanFieldEncodeBHist H))
            (completeArchimedeanFieldDecodeBHist (completeArchimedeanFieldEncodeBHist C))
            (completeArchimedeanFieldDecodeBHist (completeArchimedeanFieldEncodeBHist P))
            (completeArchimedeanFieldDecodeBHist (completeArchimedeanFieldEncodeBHist N))) =
          some (CompleteArchimedeanFieldUp.mk R O A D W Q K H C P N)
      rw [CompleteArchimedeanFieldTasteGate_single_carrier_alignment_decode_encode R,
        CompleteArchimedeanFieldTasteGate_single_carrier_alignment_decode_encode O,
        CompleteArchimedeanFieldTasteGate_single_carrier_alignment_decode_encode A,
        CompleteArchimedeanFieldTasteGate_single_carrier_alignment_decode_encode D,
        CompleteArchimedeanFieldTasteGate_single_carrier_alignment_decode_encode W,
        CompleteArchimedeanFieldTasteGate_single_carrier_alignment_decode_encode Q,
        CompleteArchimedeanFieldTasteGate_single_carrier_alignment_decode_encode K,
        CompleteArchimedeanFieldTasteGate_single_carrier_alignment_decode_encode H,
        CompleteArchimedeanFieldTasteGate_single_carrier_alignment_decode_encode C,
        CompleteArchimedeanFieldTasteGate_single_carrier_alignment_decode_encode P,
        CompleteArchimedeanFieldTasteGate_single_carrier_alignment_decode_encode N]

private theorem CompleteArchimedeanFieldTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BEDC.Derived.CompleteArchimedeanFieldUp} :
    completeArchimedeanFieldToEventFlow x = completeArchimedeanFieldToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      completeArchimedeanFieldFromEventFlow (completeArchimedeanFieldToEventFlow x) =
        completeArchimedeanFieldFromEventFlow (completeArchimedeanFieldToEventFlow y) :=
    congrArg completeArchimedeanFieldFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CompleteArchimedeanFieldTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CompleteArchimedeanFieldTasteGate_single_carrier_alignment_round_trip y)))

private theorem CompleteArchimedeanFieldTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : BEDC.Derived.CompleteArchimedeanFieldUp,
      completeArchimedeanFieldFields x = completeArchimedeanFieldFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk R₁ O₁ A₁ D₁ W₁ Q₁ K₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk R₂ O₂ A₂ D₂ W₂ Q₂ K₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance completeArchimedeanFieldBHistCarrier :
    BHistCarrier BEDC.Derived.CompleteArchimedeanFieldUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := completeArchimedeanFieldToEventFlow
  fromEventFlow := completeArchimedeanFieldFromEventFlow

instance completeArchimedeanFieldChapterTasteGate :
    ChapterTasteGate BEDC.Derived.CompleteArchimedeanFieldUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change completeArchimedeanFieldFromEventFlow (completeArchimedeanFieldToEventFlow x) =
      some x
    exact CompleteArchimedeanFieldTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CompleteArchimedeanFieldTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance completeArchimedeanFieldFieldFaithful :
    FieldFaithful BEDC.Derived.CompleteArchimedeanFieldUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := completeArchimedeanFieldFields
  field_faithful := CompleteArchimedeanFieldTasteGate_single_carrier_alignment_fields_faithful

instance completeArchimedeanFieldNontrivial :
    Nontrivial BEDC.Derived.CompleteArchimedeanFieldUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CompleteArchimedeanFieldUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      CompleteArchimedeanFieldUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BEDC.Derived.CompleteArchimedeanFieldUp :=
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  completeArchimedeanFieldChapterTasteGate

theorem CompleteArchimedeanFieldTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier CompleteArchimedeanFieldUp) ∧
      Nonempty (ChapterTasteGate CompleteArchimedeanFieldUp) ∧
        Nonempty (FieldFaithful CompleteArchimedeanFieldUp) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨⟨completeArchimedeanFieldBHistCarrier⟩,
      ⟨⟨completeArchimedeanFieldChapterTasteGate⟩,
        ⟨completeArchimedeanFieldFieldFaithful⟩⟩⟩

end BEDC.Derived.CompleteArchimedeanFieldUp
