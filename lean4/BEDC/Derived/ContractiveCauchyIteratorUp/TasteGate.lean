import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ContractiveCauchyIteratorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ContractiveCauchyIteratorUp : Type where
  | mk (M T B I W Q D E H C : BHist) : ContractiveCauchyIteratorUp
  deriving DecidableEq

def contractiveCauchyIteratorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: contractiveCauchyIteratorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: contractiveCauchyIteratorEncodeBHist h

def contractiveCauchyIteratorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (contractiveCauchyIteratorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (contractiveCauchyIteratorDecodeBHist tail)

private theorem ContractiveCauchyIteratorTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      contractiveCauchyIteratorDecodeBHist (contractiveCauchyIteratorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def contractiveCauchyIteratorFields : ContractiveCauchyIteratorUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ContractiveCauchyIteratorUp.mk M T B I W Q D E H C => [M, T, B, I, W, Q, D, E, H, C]

def contractiveCauchyIteratorToEventFlow : ContractiveCauchyIteratorUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (contractiveCauchyIteratorFields x).map contractiveCauchyIteratorEncodeBHist

private def contractiveCauchyIteratorEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => contractiveCauchyIteratorEventAt index rest

def contractiveCauchyIteratorFromEventFlow (ef : EventFlow) :
    Option ContractiveCauchyIteratorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ContractiveCauchyIteratorUp.mk
      (contractiveCauchyIteratorDecodeBHist (contractiveCauchyIteratorEventAt 0 ef))
      (contractiveCauchyIteratorDecodeBHist (contractiveCauchyIteratorEventAt 1 ef))
      (contractiveCauchyIteratorDecodeBHist (contractiveCauchyIteratorEventAt 2 ef))
      (contractiveCauchyIteratorDecodeBHist (contractiveCauchyIteratorEventAt 3 ef))
      (contractiveCauchyIteratorDecodeBHist (contractiveCauchyIteratorEventAt 4 ef))
      (contractiveCauchyIteratorDecodeBHist (contractiveCauchyIteratorEventAt 5 ef))
      (contractiveCauchyIteratorDecodeBHist (contractiveCauchyIteratorEventAt 6 ef))
      (contractiveCauchyIteratorDecodeBHist (contractiveCauchyIteratorEventAt 7 ef))
      (contractiveCauchyIteratorDecodeBHist (contractiveCauchyIteratorEventAt 8 ef))
      (contractiveCauchyIteratorDecodeBHist (contractiveCauchyIteratorEventAt 9 ef)))

private theorem ContractiveCauchyIteratorTasteGate_single_carrier_alignment_round_trip
    (x : ContractiveCauchyIteratorUp) :
    contractiveCauchyIteratorFromEventFlow (contractiveCauchyIteratorToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk M T B I W Q D E H C =>
      change
        some
          (ContractiveCauchyIteratorUp.mk
            (contractiveCauchyIteratorDecodeBHist (contractiveCauchyIteratorEncodeBHist M))
            (contractiveCauchyIteratorDecodeBHist (contractiveCauchyIteratorEncodeBHist T))
            (contractiveCauchyIteratorDecodeBHist (contractiveCauchyIteratorEncodeBHist B))
            (contractiveCauchyIteratorDecodeBHist (contractiveCauchyIteratorEncodeBHist I))
            (contractiveCauchyIteratorDecodeBHist (contractiveCauchyIteratorEncodeBHist W))
            (contractiveCauchyIteratorDecodeBHist (contractiveCauchyIteratorEncodeBHist Q))
            (contractiveCauchyIteratorDecodeBHist (contractiveCauchyIteratorEncodeBHist D))
            (contractiveCauchyIteratorDecodeBHist (contractiveCauchyIteratorEncodeBHist E))
            (contractiveCauchyIteratorDecodeBHist (contractiveCauchyIteratorEncodeBHist H))
            (contractiveCauchyIteratorDecodeBHist (contractiveCauchyIteratorEncodeBHist C))) =
          some (ContractiveCauchyIteratorUp.mk M T B I W Q D E H C)
      rw [ContractiveCauchyIteratorTasteGate_single_carrier_alignment_decode_encode M,
        ContractiveCauchyIteratorTasteGate_single_carrier_alignment_decode_encode T,
        ContractiveCauchyIteratorTasteGate_single_carrier_alignment_decode_encode B,
        ContractiveCauchyIteratorTasteGate_single_carrier_alignment_decode_encode I,
        ContractiveCauchyIteratorTasteGate_single_carrier_alignment_decode_encode W,
        ContractiveCauchyIteratorTasteGate_single_carrier_alignment_decode_encode Q,
        ContractiveCauchyIteratorTasteGate_single_carrier_alignment_decode_encode D,
        ContractiveCauchyIteratorTasteGate_single_carrier_alignment_decode_encode E,
        ContractiveCauchyIteratorTasteGate_single_carrier_alignment_decode_encode H,
        ContractiveCauchyIteratorTasteGate_single_carrier_alignment_decode_encode C]

private theorem ContractiveCauchyIteratorTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ContractiveCauchyIteratorUp} :
    contractiveCauchyIteratorToEventFlow x = contractiveCauchyIteratorToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      contractiveCauchyIteratorFromEventFlow (contractiveCauchyIteratorToEventFlow x) =
        contractiveCauchyIteratorFromEventFlow (contractiveCauchyIteratorToEventFlow y) :=
    congrArg contractiveCauchyIteratorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ContractiveCauchyIteratorTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ContractiveCauchyIteratorTasteGate_single_carrier_alignment_round_trip y)))

instance contractiveCauchyIteratorBHistCarrier : BHistCarrier ContractiveCauchyIteratorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := contractiveCauchyIteratorToEventFlow
  fromEventFlow := contractiveCauchyIteratorFromEventFlow

instance contractiveCauchyIteratorChapterTasteGate :
    ChapterTasteGate ContractiveCauchyIteratorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change contractiveCauchyIteratorFromEventFlow (contractiveCauchyIteratorToEventFlow x) =
      some x
    exact ContractiveCauchyIteratorTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (ContractiveCauchyIteratorTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem ContractiveCauchyIteratorTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      contractiveCauchyIteratorDecodeBHist (contractiveCauchyIteratorEncodeBHist h) = h) ∧
      contractiveCauchyIteratorFromEventFlow
          (contractiveCauchyIteratorToEventFlow
            (ContractiveCauchyIteratorUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty)) =
        some
          (ContractiveCauchyIteratorUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨ContractiveCauchyIteratorTasteGate_single_carrier_alignment_decode_encode,
      ContractiveCauchyIteratorTasteGate_single_carrier_alignment_round_trip
        (ContractiveCauchyIteratorUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty)⟩

end BEDC.Derived.ContractiveCauchyIteratorUp
