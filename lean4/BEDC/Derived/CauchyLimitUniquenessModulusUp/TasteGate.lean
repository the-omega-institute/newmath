import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyLimitUniquenessModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyLimitUniquenessModulusUp : Type where
  | mk (L0 L1 B W R U E H C P N : BHist) : CauchyLimitUniquenessModulusUp
  deriving DecidableEq

def cauchyLimitUniquenessModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyLimitUniquenessModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyLimitUniquenessModulusEncodeBHist h

def cauchyLimitUniquenessModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyLimitUniquenessModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyLimitUniquenessModulusDecodeBHist tail)

private theorem CauchyLimitUniquenessModulusTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      cauchyLimitUniquenessModulusDecodeBHist
          (cauchyLimitUniquenessModulusEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyLimitUniquenessModulusFields :
    CauchyLimitUniquenessModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyLimitUniquenessModulusUp.mk L0 L1 B W R U E H C P N =>
      [L0, L1, B, W, R, U, E, H, C, P, N]

def cauchyLimitUniquenessModulusToEventFlow :
    CauchyLimitUniquenessModulusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyLimitUniquenessModulusFields x).map cauchyLimitUniquenessModulusEncodeBHist

private def cauchyLimitUniquenessModulusEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyLimitUniquenessModulusEventAt index rest

def cauchyLimitUniquenessModulusFromEventFlow (ef : EventFlow) :
    Option CauchyLimitUniquenessModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyLimitUniquenessModulusUp.mk
      (cauchyLimitUniquenessModulusDecodeBHist (cauchyLimitUniquenessModulusEventAt 0 ef))
      (cauchyLimitUniquenessModulusDecodeBHist (cauchyLimitUniquenessModulusEventAt 1 ef))
      (cauchyLimitUniquenessModulusDecodeBHist (cauchyLimitUniquenessModulusEventAt 2 ef))
      (cauchyLimitUniquenessModulusDecodeBHist (cauchyLimitUniquenessModulusEventAt 3 ef))
      (cauchyLimitUniquenessModulusDecodeBHist (cauchyLimitUniquenessModulusEventAt 4 ef))
      (cauchyLimitUniquenessModulusDecodeBHist (cauchyLimitUniquenessModulusEventAt 5 ef))
      (cauchyLimitUniquenessModulusDecodeBHist (cauchyLimitUniquenessModulusEventAt 6 ef))
      (cauchyLimitUniquenessModulusDecodeBHist (cauchyLimitUniquenessModulusEventAt 7 ef))
      (cauchyLimitUniquenessModulusDecodeBHist (cauchyLimitUniquenessModulusEventAt 8 ef))
      (cauchyLimitUniquenessModulusDecodeBHist (cauchyLimitUniquenessModulusEventAt 9 ef))
      (cauchyLimitUniquenessModulusDecodeBHist (cauchyLimitUniquenessModulusEventAt 10 ef)))

private theorem CauchyLimitUniquenessModulusTasteGate_single_carrier_alignment_round_trip
    (x : CauchyLimitUniquenessModulusUp) :
    cauchyLimitUniquenessModulusFromEventFlow
        (cauchyLimitUniquenessModulusToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk L0 L1 B W R U E H C P N =>
      change
        some
          (CauchyLimitUniquenessModulusUp.mk
            (cauchyLimitUniquenessModulusDecodeBHist
              (cauchyLimitUniquenessModulusEncodeBHist L0))
            (cauchyLimitUniquenessModulusDecodeBHist
              (cauchyLimitUniquenessModulusEncodeBHist L1))
            (cauchyLimitUniquenessModulusDecodeBHist
              (cauchyLimitUniquenessModulusEncodeBHist B))
            (cauchyLimitUniquenessModulusDecodeBHist
              (cauchyLimitUniquenessModulusEncodeBHist W))
            (cauchyLimitUniquenessModulusDecodeBHist
              (cauchyLimitUniquenessModulusEncodeBHist R))
            (cauchyLimitUniquenessModulusDecodeBHist
              (cauchyLimitUniquenessModulusEncodeBHist U))
            (cauchyLimitUniquenessModulusDecodeBHist
              (cauchyLimitUniquenessModulusEncodeBHist E))
            (cauchyLimitUniquenessModulusDecodeBHist
              (cauchyLimitUniquenessModulusEncodeBHist H))
            (cauchyLimitUniquenessModulusDecodeBHist
              (cauchyLimitUniquenessModulusEncodeBHist C))
            (cauchyLimitUniquenessModulusDecodeBHist
              (cauchyLimitUniquenessModulusEncodeBHist P))
            (cauchyLimitUniquenessModulusDecodeBHist
              (cauchyLimitUniquenessModulusEncodeBHist N))) =
          some (CauchyLimitUniquenessModulusUp.mk L0 L1 B W R U E H C P N)
      rw [CauchyLimitUniquenessModulusTasteGate_single_carrier_alignment_decode L0,
        CauchyLimitUniquenessModulusTasteGate_single_carrier_alignment_decode L1,
        CauchyLimitUniquenessModulusTasteGate_single_carrier_alignment_decode B,
        CauchyLimitUniquenessModulusTasteGate_single_carrier_alignment_decode W,
        CauchyLimitUniquenessModulusTasteGate_single_carrier_alignment_decode R,
        CauchyLimitUniquenessModulusTasteGate_single_carrier_alignment_decode U,
        CauchyLimitUniquenessModulusTasteGate_single_carrier_alignment_decode E,
        CauchyLimitUniquenessModulusTasteGate_single_carrier_alignment_decode H,
        CauchyLimitUniquenessModulusTasteGate_single_carrier_alignment_decode C,
        CauchyLimitUniquenessModulusTasteGate_single_carrier_alignment_decode P,
        CauchyLimitUniquenessModulusTasteGate_single_carrier_alignment_decode N]

private theorem CauchyLimitUniquenessModulusTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyLimitUniquenessModulusUp} :
    cauchyLimitUniquenessModulusToEventFlow x =
        cauchyLimitUniquenessModulusToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyLimitUniquenessModulusFromEventFlow
          (cauchyLimitUniquenessModulusToEventFlow x) =
        cauchyLimitUniquenessModulusFromEventFlow
          (cauchyLimitUniquenessModulusToEventFlow y) :=
    congrArg cauchyLimitUniquenessModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyLimitUniquenessModulusTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyLimitUniquenessModulusTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyLimitUniquenessModulusBHistCarrier :
    BHistCarrier CauchyLimitUniquenessModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyLimitUniquenessModulusToEventFlow
  fromEventFlow := cauchyLimitUniquenessModulusFromEventFlow

instance cauchyLimitUniquenessModulusChapterTasteGate :
    ChapterTasteGate CauchyLimitUniquenessModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyLimitUniquenessModulusFromEventFlow
          (cauchyLimitUniquenessModulusToEventFlow x) =
        some x
    exact CauchyLimitUniquenessModulusTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchyLimitUniquenessModulusTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem CauchyLimitUniquenessModulusTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier CauchyLimitUniquenessModulusUp) ∧
      Nonempty (ChapterTasteGate CauchyLimitUniquenessModulusUp) ∧
        (∀ h : BHist,
          cauchyLimitUniquenessModulusDecodeBHist
              (cauchyLimitUniquenessModulusEncodeBHist h) =
            h) ∧
          (∀ x : CauchyLimitUniquenessModulusUp,
            cauchyLimitUniquenessModulusFromEventFlow
                (cauchyLimitUniquenessModulusToEventFlow x) =
              some x) ∧
            cauchyLimitUniquenessModulusEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨cauchyLimitUniquenessModulusBHistCarrier⟩,
      ⟨cauchyLimitUniquenessModulusChapterTasteGate⟩,
      CauchyLimitUniquenessModulusTasteGate_single_carrier_alignment_decode,
      CauchyLimitUniquenessModulusTasteGate_single_carrier_alignment_round_trip,
      rfl⟩

end BEDC.Derived.CauchyLimitUniquenessModulusUp
