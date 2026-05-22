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

private theorem CauchyRealFieldUpTasteGate_single_carrier_alignment_decode_encode :
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
  | x => (cauchyRealFieldFields x).map cauchyRealFieldEncodeBHist

private def cauchyRealFieldEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyRealFieldEventAt index rest

def cauchyRealFieldFromEventFlow (ef : EventFlow) : Option CauchyRealFieldUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyRealFieldUp.mk
      (cauchyRealFieldDecodeBHist (cauchyRealFieldEventAt 0 ef))
      (cauchyRealFieldDecodeBHist (cauchyRealFieldEventAt 1 ef))
      (cauchyRealFieldDecodeBHist (cauchyRealFieldEventAt 2 ef))
      (cauchyRealFieldDecodeBHist (cauchyRealFieldEventAt 3 ef))
      (cauchyRealFieldDecodeBHist (cauchyRealFieldEventAt 4 ef))
      (cauchyRealFieldDecodeBHist (cauchyRealFieldEventAt 5 ef))
      (cauchyRealFieldDecodeBHist (cauchyRealFieldEventAt 6 ef))
      (cauchyRealFieldDecodeBHist (cauchyRealFieldEventAt 7 ef))
      (cauchyRealFieldDecodeBHist (cauchyRealFieldEventAt 8 ef))
      (cauchyRealFieldDecodeBHist (cauchyRealFieldEventAt 9 ef))
      (cauchyRealFieldDecodeBHist (cauchyRealFieldEventAt 10 ef))
      (cauchyRealFieldDecodeBHist (cauchyRealFieldEventAt 11 ef)))

private theorem CauchyRealFieldUpTasteGate_single_carrier_alignment_round_trip
    (x : CauchyRealFieldUp) :
    cauchyRealFieldFromEventFlow (cauchyRealFieldToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
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
      rw [CauchyRealFieldUpTasteGate_single_carrier_alignment_decode_encode R,
        CauchyRealFieldUpTasteGate_single_carrier_alignment_decode_encode S,
        CauchyRealFieldUpTasteGate_single_carrier_alignment_decode_encode D,
        CauchyRealFieldUpTasteGate_single_carrier_alignment_decode_encode Z,
        CauchyRealFieldUpTasteGate_single_carrier_alignment_decode_encode A,
        CauchyRealFieldUpTasteGate_single_carrier_alignment_decode_encode M,
        CauchyRealFieldUpTasteGate_single_carrier_alignment_decode_encode I,
        CauchyRealFieldUpTasteGate_single_carrier_alignment_decode_encode O,
        CauchyRealFieldUpTasteGate_single_carrier_alignment_decode_encode H,
        CauchyRealFieldUpTasteGate_single_carrier_alignment_decode_encode C,
        CauchyRealFieldUpTasteGate_single_carrier_alignment_decode_encode P,
        CauchyRealFieldUpTasteGate_single_carrier_alignment_decode_encode N]

private theorem CauchyRealFieldUpTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyRealFieldUp} :
    cauchyRealFieldToEventFlow x = cauchyRealFieldToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyRealFieldFromEventFlow (cauchyRealFieldToEventFlow x) =
        cauchyRealFieldFromEventFlow (cauchyRealFieldToEventFlow y) :=
    congrArg cauchyRealFieldFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyRealFieldUpTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CauchyRealFieldUpTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyRealFieldBHistCarrier : BHistCarrier CauchyRealFieldUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyRealFieldToEventFlow
  fromEventFlow := cauchyRealFieldFromEventFlow

instance cauchyRealFieldChapterTasteGate : ChapterTasteGate CauchyRealFieldUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyRealFieldFromEventFlow (cauchyRealFieldToEventFlow x) = some x
    exact CauchyRealFieldUpTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyRealFieldUpTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem CauchyRealFieldUpTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchyRealFieldDecodeBHist (cauchyRealFieldEncodeBHist h) = h) ∧
      (∀ x : CauchyRealFieldUp,
        cauchyRealFieldFromEventFlow (cauchyRealFieldToEventFlow x) = some x) ∧
        (∀ x y : CauchyRealFieldUp,
          cauchyRealFieldToEventFlow x = cauchyRealFieldToEventFlow y → x = y) ∧
          cauchyRealFieldEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CauchyRealFieldUpTasteGate_single_carrier_alignment_decode_encode,
      CauchyRealFieldUpTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        CauchyRealFieldUpTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CauchyRealFieldUp
