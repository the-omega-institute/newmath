import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BanachFixedPointModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BanachFixedPointModulusUp : Type where
  | mk (B T L I M R C E H Q P N : BHist) : BanachFixedPointModulusUp
  deriving DecidableEq

def banachFixedPointModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: banachFixedPointModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: banachFixedPointModulusEncodeBHist h

def banachFixedPointModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (banachFixedPointModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (banachFixedPointModulusDecodeBHist tail)

private theorem BanachFixedPointModulusTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      banachFixedPointModulusDecodeBHist (banachFixedPointModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def banachFixedPointModulusFields : BanachFixedPointModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BanachFixedPointModulusUp.mk B T L I M R C E H Q P N =>
      [B, T, L, I, M, R, C, E, H, Q, P, N]

def banachFixedPointModulusToEventFlow : BanachFixedPointModulusUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (banachFixedPointModulusFields x).map banachFixedPointModulusEncodeBHist

private def banachFixedPointModulusEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => banachFixedPointModulusEventAtDefault index rest

def banachFixedPointModulusFromEventFlow (ef : EventFlow) :
    Option BanachFixedPointModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BanachFixedPointModulusUp.mk
      (banachFixedPointModulusDecodeBHist (banachFixedPointModulusEventAtDefault 0 ef))
      (banachFixedPointModulusDecodeBHist (banachFixedPointModulusEventAtDefault 1 ef))
      (banachFixedPointModulusDecodeBHist (banachFixedPointModulusEventAtDefault 2 ef))
      (banachFixedPointModulusDecodeBHist (banachFixedPointModulusEventAtDefault 3 ef))
      (banachFixedPointModulusDecodeBHist (banachFixedPointModulusEventAtDefault 4 ef))
      (banachFixedPointModulusDecodeBHist (banachFixedPointModulusEventAtDefault 5 ef))
      (banachFixedPointModulusDecodeBHist (banachFixedPointModulusEventAtDefault 6 ef))
      (banachFixedPointModulusDecodeBHist (banachFixedPointModulusEventAtDefault 7 ef))
      (banachFixedPointModulusDecodeBHist (banachFixedPointModulusEventAtDefault 8 ef))
      (banachFixedPointModulusDecodeBHist (banachFixedPointModulusEventAtDefault 9 ef))
      (banachFixedPointModulusDecodeBHist (banachFixedPointModulusEventAtDefault 10 ef))
      (banachFixedPointModulusDecodeBHist (banachFixedPointModulusEventAtDefault 11 ef)))

private theorem BanachFixedPointModulusTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BanachFixedPointModulusUp,
      banachFixedPointModulusFromEventFlow (banachFixedPointModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B T L I M R C E H Q P N =>
      change
        some
          (BanachFixedPointModulusUp.mk
            (banachFixedPointModulusDecodeBHist (banachFixedPointModulusEncodeBHist B))
            (banachFixedPointModulusDecodeBHist (banachFixedPointModulusEncodeBHist T))
            (banachFixedPointModulusDecodeBHist (banachFixedPointModulusEncodeBHist L))
            (banachFixedPointModulusDecodeBHist (banachFixedPointModulusEncodeBHist I))
            (banachFixedPointModulusDecodeBHist (banachFixedPointModulusEncodeBHist M))
            (banachFixedPointModulusDecodeBHist (banachFixedPointModulusEncodeBHist R))
            (banachFixedPointModulusDecodeBHist (banachFixedPointModulusEncodeBHist C))
            (banachFixedPointModulusDecodeBHist (banachFixedPointModulusEncodeBHist E))
            (banachFixedPointModulusDecodeBHist (banachFixedPointModulusEncodeBHist H))
            (banachFixedPointModulusDecodeBHist (banachFixedPointModulusEncodeBHist Q))
            (banachFixedPointModulusDecodeBHist (banachFixedPointModulusEncodeBHist P))
            (banachFixedPointModulusDecodeBHist (banachFixedPointModulusEncodeBHist N))) =
          some (BanachFixedPointModulusUp.mk B T L I M R C E H Q P N)
      rw [BanachFixedPointModulusTasteGate_single_carrier_alignment_decode B,
        BanachFixedPointModulusTasteGate_single_carrier_alignment_decode T,
        BanachFixedPointModulusTasteGate_single_carrier_alignment_decode L,
        BanachFixedPointModulusTasteGate_single_carrier_alignment_decode I,
        BanachFixedPointModulusTasteGate_single_carrier_alignment_decode M,
        BanachFixedPointModulusTasteGate_single_carrier_alignment_decode R,
        BanachFixedPointModulusTasteGate_single_carrier_alignment_decode C,
        BanachFixedPointModulusTasteGate_single_carrier_alignment_decode E,
        BanachFixedPointModulusTasteGate_single_carrier_alignment_decode H,
        BanachFixedPointModulusTasteGate_single_carrier_alignment_decode Q,
        BanachFixedPointModulusTasteGate_single_carrier_alignment_decode P,
        BanachFixedPointModulusTasteGate_single_carrier_alignment_decode N]

private theorem banachFixedPointModulusToEventFlow_injective
    {x y : BanachFixedPointModulusUp} :
    banachFixedPointModulusToEventFlow x = banachFixedPointModulusToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      banachFixedPointModulusFromEventFlow (banachFixedPointModulusToEventFlow x) =
        banachFixedPointModulusFromEventFlow (banachFixedPointModulusToEventFlow y) :=
    congrArg banachFixedPointModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BanachFixedPointModulusTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BanachFixedPointModulusTasteGate_single_carrier_alignment_round_trip y)))

instance banachFixedPointModulusBHistCarrier : BHistCarrier BanachFixedPointModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := banachFixedPointModulusToEventFlow
  fromEventFlow := banachFixedPointModulusFromEventFlow

instance banachFixedPointModulusChapterTasteGate :
    ChapterTasteGate BanachFixedPointModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change banachFixedPointModulusFromEventFlow (banachFixedPointModulusToEventFlow x) =
      some x
    exact BanachFixedPointModulusTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (banachFixedPointModulusToEventFlow_injective heq)

theorem BanachFixedPointModulusTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        banachFixedPointModulusDecodeBHist (banachFixedPointModulusEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier BanachFixedPointModulusUp) ∧
        Nonempty (ChapterTasteGate BanachFixedPointModulusUp) ∧
          banachFixedPointModulusEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨BanachFixedPointModulusTasteGate_single_carrier_alignment_decode,
      ⟨banachFixedPointModulusBHistCarrier⟩,
      ⟨banachFixedPointModulusChapterTasteGate⟩, rfl⟩

end BEDC.Derived.BanachFixedPointModulusUp
