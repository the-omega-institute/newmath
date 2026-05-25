import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyRealOrderedFieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyRealOrderedFieldUp : Type where
  | mk (F O A B Z H C P N : BHist) : CauchyRealOrderedFieldUp
  deriving DecidableEq

def cauchyRealOrderedFieldEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyRealOrderedFieldEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyRealOrderedFieldEncodeBHist h

def cauchyRealOrderedFieldDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyRealOrderedFieldDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyRealOrderedFieldDecodeBHist tail)

private theorem CauchyRealOrderedFieldTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      cauchyRealOrderedFieldDecodeBHist (cauchyRealOrderedFieldEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cauchyRealOrderedFieldFields : CauchyRealOrderedFieldUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyRealOrderedFieldUp.mk F O A B Z H C P N => [F, O, A, B, Z, H, C, P, N]

def cauchyRealOrderedFieldToEventFlow : CauchyRealOrderedFieldUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyRealOrderedFieldFields x).map cauchyRealOrderedFieldEncodeBHist

private def CauchyRealOrderedFieldTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      CauchyRealOrderedFieldTasteGate_single_carrier_alignment_eventAt index rest

def cauchyRealOrderedFieldFromEventFlow (ef : EventFlow) : Option CauchyRealOrderedFieldUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyRealOrderedFieldUp.mk
      (cauchyRealOrderedFieldDecodeBHist
        (CauchyRealOrderedFieldTasteGate_single_carrier_alignment_eventAt 0 ef))
      (cauchyRealOrderedFieldDecodeBHist
        (CauchyRealOrderedFieldTasteGate_single_carrier_alignment_eventAt 1 ef))
      (cauchyRealOrderedFieldDecodeBHist
        (CauchyRealOrderedFieldTasteGate_single_carrier_alignment_eventAt 2 ef))
      (cauchyRealOrderedFieldDecodeBHist
        (CauchyRealOrderedFieldTasteGate_single_carrier_alignment_eventAt 3 ef))
      (cauchyRealOrderedFieldDecodeBHist
        (CauchyRealOrderedFieldTasteGate_single_carrier_alignment_eventAt 4 ef))
      (cauchyRealOrderedFieldDecodeBHist
        (CauchyRealOrderedFieldTasteGate_single_carrier_alignment_eventAt 5 ef))
      (cauchyRealOrderedFieldDecodeBHist
        (CauchyRealOrderedFieldTasteGate_single_carrier_alignment_eventAt 6 ef))
      (cauchyRealOrderedFieldDecodeBHist
        (CauchyRealOrderedFieldTasteGate_single_carrier_alignment_eventAt 7 ef))
      (cauchyRealOrderedFieldDecodeBHist
        (CauchyRealOrderedFieldTasteGate_single_carrier_alignment_eventAt 8 ef)))

private theorem CauchyRealOrderedFieldTasteGate_single_carrier_alignment_round_trip
    (x : CauchyRealOrderedFieldUp) :
    cauchyRealOrderedFieldFromEventFlow (cauchyRealOrderedFieldToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk F O A B Z H C P N =>
      change
        some
          (CauchyRealOrderedFieldUp.mk
            (cauchyRealOrderedFieldDecodeBHist (cauchyRealOrderedFieldEncodeBHist F))
            (cauchyRealOrderedFieldDecodeBHist (cauchyRealOrderedFieldEncodeBHist O))
            (cauchyRealOrderedFieldDecodeBHist (cauchyRealOrderedFieldEncodeBHist A))
            (cauchyRealOrderedFieldDecodeBHist (cauchyRealOrderedFieldEncodeBHist B))
            (cauchyRealOrderedFieldDecodeBHist (cauchyRealOrderedFieldEncodeBHist Z))
            (cauchyRealOrderedFieldDecodeBHist (cauchyRealOrderedFieldEncodeBHist H))
            (cauchyRealOrderedFieldDecodeBHist (cauchyRealOrderedFieldEncodeBHist C))
            (cauchyRealOrderedFieldDecodeBHist (cauchyRealOrderedFieldEncodeBHist P))
            (cauchyRealOrderedFieldDecodeBHist (cauchyRealOrderedFieldEncodeBHist N))) =
          some (CauchyRealOrderedFieldUp.mk F O A B Z H C P N)
      rw [CauchyRealOrderedFieldTasteGate_single_carrier_alignment_decode_encode F,
        CauchyRealOrderedFieldTasteGate_single_carrier_alignment_decode_encode O,
        CauchyRealOrderedFieldTasteGate_single_carrier_alignment_decode_encode A,
        CauchyRealOrderedFieldTasteGate_single_carrier_alignment_decode_encode B,
        CauchyRealOrderedFieldTasteGate_single_carrier_alignment_decode_encode Z,
        CauchyRealOrderedFieldTasteGate_single_carrier_alignment_decode_encode H,
        CauchyRealOrderedFieldTasteGate_single_carrier_alignment_decode_encode C,
        CauchyRealOrderedFieldTasteGate_single_carrier_alignment_decode_encode P,
        CauchyRealOrderedFieldTasteGate_single_carrier_alignment_decode_encode N]

private theorem CauchyRealOrderedFieldTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyRealOrderedFieldUp} :
    cauchyRealOrderedFieldToEventFlow x = cauchyRealOrderedFieldToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyRealOrderedFieldFromEventFlow (cauchyRealOrderedFieldToEventFlow x) =
        cauchyRealOrderedFieldFromEventFlow (cauchyRealOrderedFieldToEventFlow y) :=
    congrArg cauchyRealOrderedFieldFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyRealOrderedFieldTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyRealOrderedFieldTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyRealOrderedFieldBHistCarrier : BHistCarrier CauchyRealOrderedFieldUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyRealOrderedFieldToEventFlow
  fromEventFlow := cauchyRealOrderedFieldFromEventFlow

instance cauchyRealOrderedFieldChapterTasteGate :
    ChapterTasteGate CauchyRealOrderedFieldUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyRealOrderedFieldFromEventFlow (cauchyRealOrderedFieldToEventFlow x) = some x
    exact CauchyRealOrderedFieldTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchyRealOrderedFieldTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate CauchyRealOrderedFieldUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyRealOrderedFieldChapterTasteGate

theorem CauchyRealOrderedFieldTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyRealOrderedFieldDecodeBHist (cauchyRealOrderedFieldEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier CauchyRealOrderedFieldUp) ∧
        Nonempty (ChapterTasteGate CauchyRealOrderedFieldUp) ∧
          cauchyRealOrderedFieldEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CauchyRealOrderedFieldTasteGate_single_carrier_alignment_decode_encode,
      ⟨⟨cauchyRealOrderedFieldBHistCarrier⟩,
        ⟨⟨cauchyRealOrderedFieldChapterTasteGate⟩, rfl⟩⟩⟩

end BEDC.Derived.CauchyRealOrderedFieldUp
