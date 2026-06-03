import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TensorAlgebraUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TensorAlgebraUp : Type where
  | mk (R V W Q U A H C P N : BHist) : TensorAlgebraUp
  deriving DecidableEq

def tensorAlgebraEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: tensorAlgebraEncodeBHist h
  | BHist.e1 h => BMark.b1 :: tensorAlgebraEncodeBHist h

def tensorAlgebraDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (tensorAlgebraDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (tensorAlgebraDecodeBHist tail)

private theorem TensorAlgebraTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, tensorAlgebraDecodeBHist (tensorAlgebraEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def tensorAlgebraFields : TensorAlgebraUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | TensorAlgebraUp.mk R V W Q U A H C P N => [R, V, W, Q, U, A, H, C, P, N]

def tensorAlgebraToEventFlow : TensorAlgebraUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (tensorAlgebraFields x).map tensorAlgebraEncodeBHist

private def TensorAlgebraTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      TensorAlgebraTasteGate_single_carrier_alignment_eventAt index rest

def tensorAlgebraFromEventFlow (ef : EventFlow) : Option TensorAlgebraUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (TensorAlgebraUp.mk
      (tensorAlgebraDecodeBHist
        (TensorAlgebraTasteGate_single_carrier_alignment_eventAt 0 ef))
      (tensorAlgebraDecodeBHist
        (TensorAlgebraTasteGate_single_carrier_alignment_eventAt 1 ef))
      (tensorAlgebraDecodeBHist
        (TensorAlgebraTasteGate_single_carrier_alignment_eventAt 2 ef))
      (tensorAlgebraDecodeBHist
        (TensorAlgebraTasteGate_single_carrier_alignment_eventAt 3 ef))
      (tensorAlgebraDecodeBHist
        (TensorAlgebraTasteGate_single_carrier_alignment_eventAt 4 ef))
      (tensorAlgebraDecodeBHist
        (TensorAlgebraTasteGate_single_carrier_alignment_eventAt 5 ef))
      (tensorAlgebraDecodeBHist
        (TensorAlgebraTasteGate_single_carrier_alignment_eventAt 6 ef))
      (tensorAlgebraDecodeBHist
        (TensorAlgebraTasteGate_single_carrier_alignment_eventAt 7 ef))
      (tensorAlgebraDecodeBHist
        (TensorAlgebraTasteGate_single_carrier_alignment_eventAt 8 ef))
      (tensorAlgebraDecodeBHist
        (TensorAlgebraTasteGate_single_carrier_alignment_eventAt 9 ef)))

private theorem TensorAlgebraTasteGate_single_carrier_alignment_round_trip
    (x : TensorAlgebraUp) :
    tensorAlgebraFromEventFlow (tensorAlgebraToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk R V W Q U A H C P N =>
      change
        some
          (TensorAlgebraUp.mk
            (tensorAlgebraDecodeBHist (tensorAlgebraEncodeBHist R))
            (tensorAlgebraDecodeBHist (tensorAlgebraEncodeBHist V))
            (tensorAlgebraDecodeBHist (tensorAlgebraEncodeBHist W))
            (tensorAlgebraDecodeBHist (tensorAlgebraEncodeBHist Q))
            (tensorAlgebraDecodeBHist (tensorAlgebraEncodeBHist U))
            (tensorAlgebraDecodeBHist (tensorAlgebraEncodeBHist A))
            (tensorAlgebraDecodeBHist (tensorAlgebraEncodeBHist H))
            (tensorAlgebraDecodeBHist (tensorAlgebraEncodeBHist C))
            (tensorAlgebraDecodeBHist (tensorAlgebraEncodeBHist P))
            (tensorAlgebraDecodeBHist (tensorAlgebraEncodeBHist N))) =
          some (TensorAlgebraUp.mk R V W Q U A H C P N)
      rw [TensorAlgebraTasteGate_single_carrier_alignment_decode_encode R,
        TensorAlgebraTasteGate_single_carrier_alignment_decode_encode V,
        TensorAlgebraTasteGate_single_carrier_alignment_decode_encode W,
        TensorAlgebraTasteGate_single_carrier_alignment_decode_encode Q,
        TensorAlgebraTasteGate_single_carrier_alignment_decode_encode U,
        TensorAlgebraTasteGate_single_carrier_alignment_decode_encode A,
        TensorAlgebraTasteGate_single_carrier_alignment_decode_encode H,
        TensorAlgebraTasteGate_single_carrier_alignment_decode_encode C,
        TensorAlgebraTasteGate_single_carrier_alignment_decode_encode P,
        TensorAlgebraTasteGate_single_carrier_alignment_decode_encode N]

private theorem TensorAlgebraTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : TensorAlgebraUp} :
    tensorAlgebraToEventFlow x = tensorAlgebraToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      tensorAlgebraFromEventFlow (tensorAlgebraToEventFlow x) =
        tensorAlgebraFromEventFlow (tensorAlgebraToEventFlow y) :=
    congrArg tensorAlgebraFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (TensorAlgebraTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (TensorAlgebraTasteGate_single_carrier_alignment_round_trip y)))

instance tensorAlgebraBHistCarrier : BHistCarrier TensorAlgebraUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := tensorAlgebraToEventFlow
  fromEventFlow := tensorAlgebraFromEventFlow

instance tensorAlgebraChapterTasteGate : ChapterTasteGate TensorAlgebraUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change tensorAlgebraFromEventFlow (tensorAlgebraToEventFlow x) = some x
    exact TensorAlgebraTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (TensorAlgebraTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem TensorAlgebraTasteGate_single_carrier_alignment :
    (tensorAlgebraEncodeBHist BHist.Empty = ([] : RawEvent)) ∧
      (tensorAlgebraDecodeBHist [BMark.b0] = BHist.e0 BHist.Empty) ∧
        (∀ h : BHist, tensorAlgebraDecodeBHist (tensorAlgebraEncodeBHist h) = h) ∧
          Nonempty (BHistCarrier TensorAlgebraUp) ∧
            Nonempty (ChapterTasteGate TensorAlgebraUp) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨rfl, rfl, TensorAlgebraTasteGate_single_carrier_alignment_decode_encode,
      ⟨tensorAlgebraBHistCarrier⟩, ⟨tensorAlgebraChapterTasteGate⟩⟩

end BEDC.Derived.TensorAlgebraUp
