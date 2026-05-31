import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyFilterModulusTransferUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyFilterModulusTransferUp : Type where
  | mk (F B L J S R D E H C P N : BHist) : CauchyFilterModulusTransferUp
  deriving DecidableEq

def cauchyFilterModulusTransferEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyFilterModulusTransferEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyFilterModulusTransferEncodeBHist h

def cauchyFilterModulusTransferDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyFilterModulusTransferDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyFilterModulusTransferDecodeBHist tail)

private theorem CauchyFilterModulusTransferTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      cauchyFilterModulusTransferDecodeBHist
        (cauchyFilterModulusTransferEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyFilterModulusTransferFields : CauchyFilterModulusTransferUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyFilterModulusTransferUp.mk F B L J S R D E H C P N =>
      [F, B, L, J, S, R, D, E, H, C, P, N]

def cauchyFilterModulusTransferToEventFlow :
    CauchyFilterModulusTransferUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyFilterModulusTransferFields x).map cauchyFilterModulusTransferEncodeBHist

private def cauchyFilterModulusTransferEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyFilterModulusTransferEventAt index rest

def cauchyFilterModulusTransferFromEventFlow (ef : EventFlow) :
    Option CauchyFilterModulusTransferUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyFilterModulusTransferUp.mk
      (cauchyFilterModulusTransferDecodeBHist (cauchyFilterModulusTransferEventAt 0 ef))
      (cauchyFilterModulusTransferDecodeBHist (cauchyFilterModulusTransferEventAt 1 ef))
      (cauchyFilterModulusTransferDecodeBHist (cauchyFilterModulusTransferEventAt 2 ef))
      (cauchyFilterModulusTransferDecodeBHist (cauchyFilterModulusTransferEventAt 3 ef))
      (cauchyFilterModulusTransferDecodeBHist (cauchyFilterModulusTransferEventAt 4 ef))
      (cauchyFilterModulusTransferDecodeBHist (cauchyFilterModulusTransferEventAt 5 ef))
      (cauchyFilterModulusTransferDecodeBHist (cauchyFilterModulusTransferEventAt 6 ef))
      (cauchyFilterModulusTransferDecodeBHist (cauchyFilterModulusTransferEventAt 7 ef))
      (cauchyFilterModulusTransferDecodeBHist (cauchyFilterModulusTransferEventAt 8 ef))
      (cauchyFilterModulusTransferDecodeBHist (cauchyFilterModulusTransferEventAt 9 ef))
      (cauchyFilterModulusTransferDecodeBHist (cauchyFilterModulusTransferEventAt 10 ef))
      (cauchyFilterModulusTransferDecodeBHist (cauchyFilterModulusTransferEventAt 11 ef)))

private theorem CauchyFilterModulusTransferTasteGate_single_carrier_alignment_round_trip
    (x : CauchyFilterModulusTransferUp) :
    cauchyFilterModulusTransferFromEventFlow (cauchyFilterModulusTransferToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk F B L J S R D E H C P N =>
      change
        some
          (CauchyFilterModulusTransferUp.mk
            (cauchyFilterModulusTransferDecodeBHist
              (cauchyFilterModulusTransferEncodeBHist F))
            (cauchyFilterModulusTransferDecodeBHist
              (cauchyFilterModulusTransferEncodeBHist B))
            (cauchyFilterModulusTransferDecodeBHist
              (cauchyFilterModulusTransferEncodeBHist L))
            (cauchyFilterModulusTransferDecodeBHist
              (cauchyFilterModulusTransferEncodeBHist J))
            (cauchyFilterModulusTransferDecodeBHist
              (cauchyFilterModulusTransferEncodeBHist S))
            (cauchyFilterModulusTransferDecodeBHist
              (cauchyFilterModulusTransferEncodeBHist R))
            (cauchyFilterModulusTransferDecodeBHist
              (cauchyFilterModulusTransferEncodeBHist D))
            (cauchyFilterModulusTransferDecodeBHist
              (cauchyFilterModulusTransferEncodeBHist E))
            (cauchyFilterModulusTransferDecodeBHist
              (cauchyFilterModulusTransferEncodeBHist H))
            (cauchyFilterModulusTransferDecodeBHist
              (cauchyFilterModulusTransferEncodeBHist C))
            (cauchyFilterModulusTransferDecodeBHist
              (cauchyFilterModulusTransferEncodeBHist P))
            (cauchyFilterModulusTransferDecodeBHist
              (cauchyFilterModulusTransferEncodeBHist N))) =
          some (CauchyFilterModulusTransferUp.mk F B L J S R D E H C P N)
      rw [CauchyFilterModulusTransferTasteGate_single_carrier_alignment_decode_encode F,
        CauchyFilterModulusTransferTasteGate_single_carrier_alignment_decode_encode B,
        CauchyFilterModulusTransferTasteGate_single_carrier_alignment_decode_encode L,
        CauchyFilterModulusTransferTasteGate_single_carrier_alignment_decode_encode J,
        CauchyFilterModulusTransferTasteGate_single_carrier_alignment_decode_encode S,
        CauchyFilterModulusTransferTasteGate_single_carrier_alignment_decode_encode R,
        CauchyFilterModulusTransferTasteGate_single_carrier_alignment_decode_encode D,
        CauchyFilterModulusTransferTasteGate_single_carrier_alignment_decode_encode E,
        CauchyFilterModulusTransferTasteGate_single_carrier_alignment_decode_encode H,
        CauchyFilterModulusTransferTasteGate_single_carrier_alignment_decode_encode C,
        CauchyFilterModulusTransferTasteGate_single_carrier_alignment_decode_encode P,
        CauchyFilterModulusTransferTasteGate_single_carrier_alignment_decode_encode N]

private theorem CauchyFilterModulusTransferTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyFilterModulusTransferUp} :
    cauchyFilterModulusTransferToEventFlow x =
      cauchyFilterModulusTransferToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyFilterModulusTransferFromEventFlow (cauchyFilterModulusTransferToEventFlow x) =
        cauchyFilterModulusTransferFromEventFlow (cauchyFilterModulusTransferToEventFlow y) :=
    congrArg cauchyFilterModulusTransferFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyFilterModulusTransferTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyFilterModulusTransferTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyFilterModulusTransferBHistCarrier :
    BHistCarrier CauchyFilterModulusTransferUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyFilterModulusTransferToEventFlow
  fromEventFlow := cauchyFilterModulusTransferFromEventFlow

instance cauchyFilterModulusTransferChapterTasteGate :
    ChapterTasteGate CauchyFilterModulusTransferUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyFilterModulusTransferFromEventFlow
        (cauchyFilterModulusTransferToEventFlow x) = some x
    exact CauchyFilterModulusTransferTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchyFilterModulusTransferTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem CauchyFilterModulusTransferTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyFilterModulusTransferDecodeBHist
        (cauchyFilterModulusTransferEncodeBHist h) = h) ∧
      (∀ x : CauchyFilterModulusTransferUp,
        cauchyFilterModulusTransferFromEventFlow
          (cauchyFilterModulusTransferToEventFlow x) = some x) ∧
        (∀ x y : CauchyFilterModulusTransferUp,
          cauchyFilterModulusTransferToEventFlow x =
            cauchyFilterModulusTransferToEventFlow y → x = y) ∧
          cauchyFilterModulusTransferEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CauchyFilterModulusTransferTasteGate_single_carrier_alignment_decode_encode,
      CauchyFilterModulusTransferTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        CauchyFilterModulusTransferTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CauchyFilterModulusTransferUp
