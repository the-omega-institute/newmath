import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BanachSteinhausUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BanachSteinhausUp : Type where
  | mk (B M N F U L W H C P K : BHist) : BanachSteinhausUp
  deriving DecidableEq

def banachSteinhausEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: banachSteinhausEncodeBHist h
  | BHist.e1 h => BMark.b1 :: banachSteinhausEncodeBHist h

def banachSteinhausDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (banachSteinhausDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (banachSteinhausDecodeBHist tail)

private theorem BanachSteinhausTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, banachSteinhausDecodeBHist (banachSteinhausEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def banachSteinhausToEventFlow : BanachSteinhausUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BanachSteinhausUp.mk B M N F U L W H C P K =>
      [[BMark.b0],
        banachSteinhausEncodeBHist B,
        [BMark.b1, BMark.b0],
        banachSteinhausEncodeBHist M,
        [BMark.b1, BMark.b1, BMark.b0],
        banachSteinhausEncodeBHist N,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        banachSteinhausEncodeBHist F,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        banachSteinhausEncodeBHist U,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        banachSteinhausEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        banachSteinhausEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        banachSteinhausEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        banachSteinhausEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        banachSteinhausEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        banachSteinhausEncodeBHist K]

private def banachSteinhausEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => banachSteinhausEventAtDefault index rest

def banachSteinhausFromEventFlow (ef : EventFlow) : Option BanachSteinhausUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BanachSteinhausUp.mk
      (banachSteinhausDecodeBHist (banachSteinhausEventAtDefault 1 ef))
      (banachSteinhausDecodeBHist (banachSteinhausEventAtDefault 3 ef))
      (banachSteinhausDecodeBHist (banachSteinhausEventAtDefault 5 ef))
      (banachSteinhausDecodeBHist (banachSteinhausEventAtDefault 7 ef))
      (banachSteinhausDecodeBHist (banachSteinhausEventAtDefault 9 ef))
      (banachSteinhausDecodeBHist (banachSteinhausEventAtDefault 11 ef))
      (banachSteinhausDecodeBHist (banachSteinhausEventAtDefault 13 ef))
      (banachSteinhausDecodeBHist (banachSteinhausEventAtDefault 15 ef))
      (banachSteinhausDecodeBHist (banachSteinhausEventAtDefault 17 ef))
      (banachSteinhausDecodeBHist (banachSteinhausEventAtDefault 19 ef))
      (banachSteinhausDecodeBHist (banachSteinhausEventAtDefault 21 ef)))

private theorem BanachSteinhausTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BanachSteinhausUp,
      banachSteinhausFromEventFlow (banachSteinhausToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B M N F U L W H C P K =>
      change
        some
          (BanachSteinhausUp.mk
            (banachSteinhausDecodeBHist (banachSteinhausEncodeBHist B))
            (banachSteinhausDecodeBHist (banachSteinhausEncodeBHist M))
            (banachSteinhausDecodeBHist (banachSteinhausEncodeBHist N))
            (banachSteinhausDecodeBHist (banachSteinhausEncodeBHist F))
            (banachSteinhausDecodeBHist (banachSteinhausEncodeBHist U))
            (banachSteinhausDecodeBHist (banachSteinhausEncodeBHist L))
            (banachSteinhausDecodeBHist (banachSteinhausEncodeBHist W))
            (banachSteinhausDecodeBHist (banachSteinhausEncodeBHist H))
            (banachSteinhausDecodeBHist (banachSteinhausEncodeBHist C))
            (banachSteinhausDecodeBHist (banachSteinhausEncodeBHist P))
            (banachSteinhausDecodeBHist (banachSteinhausEncodeBHist K))) =
          some (BanachSteinhausUp.mk B M N F U L W H C P K)
      rw [BanachSteinhausTasteGate_single_carrier_alignment_decode_encode B,
        BanachSteinhausTasteGate_single_carrier_alignment_decode_encode M,
        BanachSteinhausTasteGate_single_carrier_alignment_decode_encode N,
        BanachSteinhausTasteGate_single_carrier_alignment_decode_encode F,
        BanachSteinhausTasteGate_single_carrier_alignment_decode_encode U,
        BanachSteinhausTasteGate_single_carrier_alignment_decode_encode L,
        BanachSteinhausTasteGate_single_carrier_alignment_decode_encode W,
        BanachSteinhausTasteGate_single_carrier_alignment_decode_encode H,
        BanachSteinhausTasteGate_single_carrier_alignment_decode_encode C,
        BanachSteinhausTasteGate_single_carrier_alignment_decode_encode P,
        BanachSteinhausTasteGate_single_carrier_alignment_decode_encode K]

private theorem BanachSteinhausTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BanachSteinhausUp} :
    banachSteinhausToEventFlow x = banachSteinhausToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      banachSteinhausFromEventFlow (banachSteinhausToEventFlow x) =
        banachSteinhausFromEventFlow (banachSteinhausToEventFlow y) :=
    congrArg banachSteinhausFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BanachSteinhausTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (BanachSteinhausTasteGate_single_carrier_alignment_round_trip y)))

instance banachSteinhausBHistCarrier : BHistCarrier BanachSteinhausUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := banachSteinhausToEventFlow
  fromEventFlow := banachSteinhausFromEventFlow

instance banachSteinhausChapterTasteGate : ChapterTasteGate BanachSteinhausUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change banachSteinhausFromEventFlow (banachSteinhausToEventFlow x) = some x
    exact BanachSteinhausTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BanachSteinhausTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate BanachSteinhausUp :=
  -- BEDC touchpoint anchor: BHist BMark
  banachSteinhausChapterTasteGate

theorem BanachSteinhausTasteGate_single_carrier_alignment :
    (∀ h : BHist, banachSteinhausDecodeBHist (banachSteinhausEncodeBHist h) = h) ∧
      (∀ x : BanachSteinhausUp,
        banachSteinhausFromEventFlow (banachSteinhausToEventFlow x) = some x) ∧
        (∀ x y : BanachSteinhausUp,
          banachSteinhausToEventFlow x = banachSteinhausToEventFlow y → x = y) ∧
          banachSteinhausEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨BanachSteinhausTasteGate_single_carrier_alignment_decode_encode,
      BanachSteinhausTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => BanachSteinhausTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.BanachSteinhausUp
