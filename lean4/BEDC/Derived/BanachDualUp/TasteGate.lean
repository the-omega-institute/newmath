import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BanachDualUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BanachDualUp : Type where
  | mk (C L K H R P N : BHist) : BanachDualUp
  deriving DecidableEq

def banachDualEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: banachDualEncodeBHist h
  | BHist.e1 h => BMark.b1 :: banachDualEncodeBHist h

def banachDualDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (banachDualDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (banachDualDecodeBHist tail)

private theorem BanachDualTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, banachDualDecodeBHist (banachDualEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def banachDualFields : BanachDualUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BanachDualUp.mk C L K H R P N => [C, L, K, H, R, P, N]

def banachDualToEventFlow : BanachDualUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (banachDualFields x).map banachDualEncodeBHist

private def banachDualEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => banachDualEventAt index rest

def banachDualFromEventFlow (ef : EventFlow) : Option BanachDualUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BanachDualUp.mk
      (banachDualDecodeBHist (banachDualEventAt 0 ef))
      (banachDualDecodeBHist (banachDualEventAt 1 ef))
      (banachDualDecodeBHist (banachDualEventAt 2 ef))
      (banachDualDecodeBHist (banachDualEventAt 3 ef))
      (banachDualDecodeBHist (banachDualEventAt 4 ef))
      (banachDualDecodeBHist (banachDualEventAt 5 ef))
      (banachDualDecodeBHist (banachDualEventAt 6 ef)))

private theorem BanachDualTasteGate_single_carrier_alignment_round_trip
    (x : BanachDualUp) :
    banachDualFromEventFlow (banachDualToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk C L K H R P N =>
      change
        some
          (BanachDualUp.mk
            (banachDualDecodeBHist (banachDualEncodeBHist C))
            (banachDualDecodeBHist (banachDualEncodeBHist L))
            (banachDualDecodeBHist (banachDualEncodeBHist K))
            (banachDualDecodeBHist (banachDualEncodeBHist H))
            (banachDualDecodeBHist (banachDualEncodeBHist R))
            (banachDualDecodeBHist (banachDualEncodeBHist P))
            (banachDualDecodeBHist (banachDualEncodeBHist N))) =
          some (BanachDualUp.mk C L K H R P N)
      rw [BanachDualTasteGate_single_carrier_alignment_decode_encode C,
        BanachDualTasteGate_single_carrier_alignment_decode_encode L,
        BanachDualTasteGate_single_carrier_alignment_decode_encode K,
        BanachDualTasteGate_single_carrier_alignment_decode_encode H,
        BanachDualTasteGate_single_carrier_alignment_decode_encode R,
        BanachDualTasteGate_single_carrier_alignment_decode_encode P,
        BanachDualTasteGate_single_carrier_alignment_decode_encode N]

private theorem BanachDualTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BanachDualUp} :
    banachDualToEventFlow x = banachDualToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      banachDualFromEventFlow (banachDualToEventFlow x) =
        banachDualFromEventFlow (banachDualToEventFlow y) :=
    congrArg banachDualFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BanachDualTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (BanachDualTasteGate_single_carrier_alignment_round_trip y)))

instance banachDualBHistCarrier : BHistCarrier BanachDualUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := banachDualToEventFlow
  fromEventFlow := banachDualFromEventFlow

instance banachDualChapterTasteGate : ChapterTasteGate BanachDualUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change banachDualFromEventFlow (banachDualToEventFlow x) = some x
    exact BanachDualTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BanachDualTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem BanachDualTasteGate_single_carrier_alignment :
    (∀ h : BHist, banachDualDecodeBHist (banachDualEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier BanachDualUp) ∧
        Nonempty (ChapterTasteGate BanachDualUp) ∧
          banachDualEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨BanachDualTasteGate_single_carrier_alignment_decode_encode,
      ⟨banachDualBHistCarrier⟩,
      ⟨banachDualChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.BanachDualUp
