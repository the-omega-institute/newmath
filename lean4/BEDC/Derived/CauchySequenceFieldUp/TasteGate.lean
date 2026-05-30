import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchySequenceFieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchySequenceFieldUp : Type where
  | mk (S M E Z O A N I C F : BHist) : CauchySequenceFieldUp
  deriving DecidableEq

def cauchySequenceFieldEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchySequenceFieldEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchySequenceFieldEncodeBHist h

def cauchySequenceFieldDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchySequenceFieldDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchySequenceFieldDecodeBHist tail)

private theorem CauchySequenceFieldTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, cauchySequenceFieldDecodeBHist (cauchySequenceFieldEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchySequenceFieldFields : CauchySequenceFieldUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchySequenceFieldUp.mk S M E Z O A N I C F => [S, M, E, Z, O, A, N, I, C, F]

def cauchySequenceFieldToEventFlow : CauchySequenceFieldUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchySequenceFieldFields x).map cauchySequenceFieldEncodeBHist

private def cauchySequenceFieldEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchySequenceFieldEventAt index rest

def cauchySequenceFieldFromEventFlow (ef : EventFlow) : Option CauchySequenceFieldUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchySequenceFieldUp.mk
      (cauchySequenceFieldDecodeBHist (cauchySequenceFieldEventAt 0 ef))
      (cauchySequenceFieldDecodeBHist (cauchySequenceFieldEventAt 1 ef))
      (cauchySequenceFieldDecodeBHist (cauchySequenceFieldEventAt 2 ef))
      (cauchySequenceFieldDecodeBHist (cauchySequenceFieldEventAt 3 ef))
      (cauchySequenceFieldDecodeBHist (cauchySequenceFieldEventAt 4 ef))
      (cauchySequenceFieldDecodeBHist (cauchySequenceFieldEventAt 5 ef))
      (cauchySequenceFieldDecodeBHist (cauchySequenceFieldEventAt 6 ef))
      (cauchySequenceFieldDecodeBHist (cauchySequenceFieldEventAt 7 ef))
      (cauchySequenceFieldDecodeBHist (cauchySequenceFieldEventAt 8 ef))
      (cauchySequenceFieldDecodeBHist (cauchySequenceFieldEventAt 9 ef)))

private theorem CauchySequenceFieldTasteGate_single_carrier_alignment_round_trip
    (x : CauchySequenceFieldUp) :
    cauchySequenceFieldFromEventFlow (cauchySequenceFieldToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S M E Z O A N I C F =>
      change
        some
          (CauchySequenceFieldUp.mk
            (cauchySequenceFieldDecodeBHist (cauchySequenceFieldEncodeBHist S))
            (cauchySequenceFieldDecodeBHist (cauchySequenceFieldEncodeBHist M))
            (cauchySequenceFieldDecodeBHist (cauchySequenceFieldEncodeBHist E))
            (cauchySequenceFieldDecodeBHist (cauchySequenceFieldEncodeBHist Z))
            (cauchySequenceFieldDecodeBHist (cauchySequenceFieldEncodeBHist O))
            (cauchySequenceFieldDecodeBHist (cauchySequenceFieldEncodeBHist A))
            (cauchySequenceFieldDecodeBHist (cauchySequenceFieldEncodeBHist N))
            (cauchySequenceFieldDecodeBHist (cauchySequenceFieldEncodeBHist I))
            (cauchySequenceFieldDecodeBHist (cauchySequenceFieldEncodeBHist C))
            (cauchySequenceFieldDecodeBHist (cauchySequenceFieldEncodeBHist F))) =
          some (CauchySequenceFieldUp.mk S M E Z O A N I C F)
      rw [CauchySequenceFieldTasteGate_single_carrier_alignment_decode_encode S,
        CauchySequenceFieldTasteGate_single_carrier_alignment_decode_encode M,
        CauchySequenceFieldTasteGate_single_carrier_alignment_decode_encode E,
        CauchySequenceFieldTasteGate_single_carrier_alignment_decode_encode Z,
        CauchySequenceFieldTasteGate_single_carrier_alignment_decode_encode O,
        CauchySequenceFieldTasteGate_single_carrier_alignment_decode_encode A,
        CauchySequenceFieldTasteGate_single_carrier_alignment_decode_encode N,
        CauchySequenceFieldTasteGate_single_carrier_alignment_decode_encode I,
        CauchySequenceFieldTasteGate_single_carrier_alignment_decode_encode C,
        CauchySequenceFieldTasteGate_single_carrier_alignment_decode_encode F]

private theorem CauchySequenceFieldTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchySequenceFieldUp} :
    cauchySequenceFieldToEventFlow x = cauchySequenceFieldToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchySequenceFieldFromEventFlow (cauchySequenceFieldToEventFlow x) =
        cauchySequenceFieldFromEventFlow (cauchySequenceFieldToEventFlow y) :=
    congrArg cauchySequenceFieldFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchySequenceFieldTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchySequenceFieldTasteGate_single_carrier_alignment_round_trip y)))

instance cauchySequenceFieldBHistCarrier : BHistCarrier CauchySequenceFieldUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchySequenceFieldToEventFlow
  fromEventFlow := cauchySequenceFieldFromEventFlow

instance cauchySequenceFieldChapterTasteGate : ChapterTasteGate CauchySequenceFieldUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchySequenceFieldFromEventFlow (cauchySequenceFieldToEventFlow x) = some x
    exact CauchySequenceFieldTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchySequenceFieldTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem CauchySequenceFieldTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier CauchySequenceFieldUp) ∧
      Nonempty (ChapterTasteGate CauchySequenceFieldUp) ∧
        (∀ h : BHist,
          cauchySequenceFieldDecodeBHist (cauchySequenceFieldEncodeBHist h) = h) ∧
          cauchySequenceFieldEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨cauchySequenceFieldBHistCarrier⟩, ⟨cauchySequenceFieldChapterTasteGate⟩,
      CauchySequenceFieldTasteGate_single_carrier_alignment_decode_encode, rfl⟩

end BEDC.Derived.CauchySequenceFieldUp
