import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactRealUniformModulusUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactRealUniformModulusUp : Type where
  | mk (R M U K W A S T C P N : BHist) : CompactRealUniformModulusUp
  deriving DecidableEq

def compactRealUniformModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactRealUniformModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactRealUniformModulusEncodeBHist h

def compactRealUniformModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactRealUniformModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactRealUniformModulusDecodeBHist tail)

private theorem compactRealUniformModulus_decode_encode :
    ∀ h : BHist,
      compactRealUniformModulusDecodeBHist (compactRealUniformModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactRealUniformModulusFields : CompactRealUniformModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactRealUniformModulusUp.mk R M U K W A S T C P N =>
      [R, M, U, K, W, A, S, T, C, P, N]

def compactRealUniformModulusToEventFlow : CompactRealUniformModulusUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (compactRealUniformModulusFields x).map compactRealUniformModulusEncodeBHist

def compactRealUniformModulusFromEventFlow : EventFlow → Option CompactRealUniformModulusUp
  -- BEDC touchpoint anchor: BHist BMark
  | [R, M, U, K, W, A, S, T, C, P, N] =>
      some
        (CompactRealUniformModulusUp.mk
          (compactRealUniformModulusDecodeBHist R)
          (compactRealUniformModulusDecodeBHist M)
          (compactRealUniformModulusDecodeBHist U)
          (compactRealUniformModulusDecodeBHist K)
          (compactRealUniformModulusDecodeBHist W)
          (compactRealUniformModulusDecodeBHist A)
          (compactRealUniformModulusDecodeBHist S)
          (compactRealUniformModulusDecodeBHist T)
          (compactRealUniformModulusDecodeBHist C)
          (compactRealUniformModulusDecodeBHist P)
          (compactRealUniformModulusDecodeBHist N))
  | _ => none

private theorem compactRealUniformModulus_round_trip :
    ∀ x : CompactRealUniformModulusUp,
      compactRealUniformModulusFromEventFlow
          (compactRealUniformModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R M U K W A S T C P N =>
      change
        some
          (CompactRealUniformModulusUp.mk
            (compactRealUniformModulusDecodeBHist (compactRealUniformModulusEncodeBHist R))
            (compactRealUniformModulusDecodeBHist (compactRealUniformModulusEncodeBHist M))
            (compactRealUniformModulusDecodeBHist (compactRealUniformModulusEncodeBHist U))
            (compactRealUniformModulusDecodeBHist (compactRealUniformModulusEncodeBHist K))
            (compactRealUniformModulusDecodeBHist (compactRealUniformModulusEncodeBHist W))
            (compactRealUniformModulusDecodeBHist (compactRealUniformModulusEncodeBHist A))
            (compactRealUniformModulusDecodeBHist (compactRealUniformModulusEncodeBHist S))
            (compactRealUniformModulusDecodeBHist (compactRealUniformModulusEncodeBHist T))
            (compactRealUniformModulusDecodeBHist (compactRealUniformModulusEncodeBHist C))
            (compactRealUniformModulusDecodeBHist (compactRealUniformModulusEncodeBHist P))
            (compactRealUniformModulusDecodeBHist (compactRealUniformModulusEncodeBHist N))) =
          some (CompactRealUniformModulusUp.mk R M U K W A S T C P N)
      rw [compactRealUniformModulus_decode_encode R,
        compactRealUniformModulus_decode_encode M,
        compactRealUniformModulus_decode_encode U,
        compactRealUniformModulus_decode_encode K,
        compactRealUniformModulus_decode_encode W,
        compactRealUniformModulus_decode_encode A,
        compactRealUniformModulus_decode_encode S,
        compactRealUniformModulus_decode_encode T,
        compactRealUniformModulus_decode_encode C,
        compactRealUniformModulus_decode_encode P,
        compactRealUniformModulus_decode_encode N]

private theorem compactRealUniformModulusToEventFlow_injective
    {x y : CompactRealUniformModulusUp} :
    compactRealUniformModulusToEventFlow x =
        compactRealUniformModulusToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactRealUniformModulusFromEventFlow (compactRealUniformModulusToEventFlow x) =
        compactRealUniformModulusFromEventFlow (compactRealUniformModulusToEventFlow y) :=
    congrArg compactRealUniformModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (compactRealUniformModulus_round_trip x).symm
      (Eq.trans hread (compactRealUniformModulus_round_trip y)))

instance compactRealUniformModulusBHistCarrier :
    BHistCarrier CompactRealUniformModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactRealUniformModulusToEventFlow
  fromEventFlow := compactRealUniformModulusFromEventFlow

instance compactRealUniformModulusChapterTasteGate :
    ChapterTasteGate CompactRealUniformModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      compactRealUniformModulusFromEventFlow (compactRealUniformModulusToEventFlow x) =
        some x
    exact compactRealUniformModulus_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (compactRealUniformModulusToEventFlow_injective heq)

theorem CompactRealUniformModulusTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      compactRealUniformModulusDecodeBHist (compactRealUniformModulusEncodeBHist h) = h) ∧
      (∀ x : CompactRealUniformModulusUp,
        compactRealUniformModulusFromEventFlow
            (compactRealUniformModulusToEventFlow x) = some x) ∧
        (∀ x y : CompactRealUniformModulusUp,
          compactRealUniformModulusToEventFlow x =
              compactRealUniformModulusToEventFlow y →
            x = y) ∧
          compactRealUniformModulusEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨compactRealUniformModulus_decode_encode,
      compactRealUniformModulus_round_trip,
      (fun _ _ h => compactRealUniformModulusToEventFlow_injective h),
      rfl⟩

end BEDC.Derived.CompactRealUniformModulusUp.TasteGate
