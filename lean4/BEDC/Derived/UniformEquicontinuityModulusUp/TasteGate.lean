import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformEquicontinuityModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniformEquicontinuityModulusUp : Type where
  | mk (K T F W M H C P N : BHist) : UniformEquicontinuityModulusUp
  deriving DecidableEq

def uniformEquicontinuityModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformEquicontinuityModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformEquicontinuityModulusEncodeBHist h

def uniformEquicontinuityModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformEquicontinuityModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformEquicontinuityModulusDecodeBHist tail)

private theorem UniformEquicontinuityModulusTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      uniformEquicontinuityModulusDecodeBHist
          (uniformEquicontinuityModulusEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def uniformEquicontinuityModulusFields :
    UniformEquicontinuityModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UniformEquicontinuityModulusUp.mk K T F W M H C P N => [K, T, F, W, M, H, C, P, N]

def uniformEquicontinuityModulusToEventFlow :
    UniformEquicontinuityModulusUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (uniformEquicontinuityModulusFields x).map uniformEquicontinuityModulusEncodeBHist

private def uniformEquicontinuityModulusEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      uniformEquicontinuityModulusEventAtDefault index rest

def uniformEquicontinuityModulusFromEventFlow
    (ef : EventFlow) : Option UniformEquicontinuityModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (UniformEquicontinuityModulusUp.mk
      (uniformEquicontinuityModulusDecodeBHist
        (uniformEquicontinuityModulusEventAtDefault 0 ef))
      (uniformEquicontinuityModulusDecodeBHist
        (uniformEquicontinuityModulusEventAtDefault 1 ef))
      (uniformEquicontinuityModulusDecodeBHist
        (uniformEquicontinuityModulusEventAtDefault 2 ef))
      (uniformEquicontinuityModulusDecodeBHist
        (uniformEquicontinuityModulusEventAtDefault 3 ef))
      (uniformEquicontinuityModulusDecodeBHist
        (uniformEquicontinuityModulusEventAtDefault 4 ef))
      (uniformEquicontinuityModulusDecodeBHist
        (uniformEquicontinuityModulusEventAtDefault 5 ef))
      (uniformEquicontinuityModulusDecodeBHist
        (uniformEquicontinuityModulusEventAtDefault 6 ef))
      (uniformEquicontinuityModulusDecodeBHist
        (uniformEquicontinuityModulusEventAtDefault 7 ef))
      (uniformEquicontinuityModulusDecodeBHist
        (uniformEquicontinuityModulusEventAtDefault 8 ef)))

private theorem uniformEquicontinuityModulus_round_trip :
    ∀ x : UniformEquicontinuityModulusUp,
      uniformEquicontinuityModulusFromEventFlow
          (uniformEquicontinuityModulusToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K T F W M H C P N =>
      change
        some
            (UniformEquicontinuityModulusUp.mk
              (uniformEquicontinuityModulusDecodeBHist
                (uniformEquicontinuityModulusEncodeBHist K))
              (uniformEquicontinuityModulusDecodeBHist
                (uniformEquicontinuityModulusEncodeBHist T))
              (uniformEquicontinuityModulusDecodeBHist
                (uniformEquicontinuityModulusEncodeBHist F))
              (uniformEquicontinuityModulusDecodeBHist
                (uniformEquicontinuityModulusEncodeBHist W))
              (uniformEquicontinuityModulusDecodeBHist
                (uniformEquicontinuityModulusEncodeBHist M))
              (uniformEquicontinuityModulusDecodeBHist
                (uniformEquicontinuityModulusEncodeBHist H))
              (uniformEquicontinuityModulusDecodeBHist
                (uniformEquicontinuityModulusEncodeBHist C))
              (uniformEquicontinuityModulusDecodeBHist
                (uniformEquicontinuityModulusEncodeBHist P))
              (uniformEquicontinuityModulusDecodeBHist
                (uniformEquicontinuityModulusEncodeBHist N))) =
          some (UniformEquicontinuityModulusUp.mk K T F W M H C P N)
      rw [UniformEquicontinuityModulusTasteGate_single_carrier_alignment_decode K,
        UniformEquicontinuityModulusTasteGate_single_carrier_alignment_decode T,
        UniformEquicontinuityModulusTasteGate_single_carrier_alignment_decode F,
        UniformEquicontinuityModulusTasteGate_single_carrier_alignment_decode W,
        UniformEquicontinuityModulusTasteGate_single_carrier_alignment_decode M,
        UniformEquicontinuityModulusTasteGate_single_carrier_alignment_decode H,
        UniformEquicontinuityModulusTasteGate_single_carrier_alignment_decode C,
        UniformEquicontinuityModulusTasteGate_single_carrier_alignment_decode P,
        UniformEquicontinuityModulusTasteGate_single_carrier_alignment_decode N]

private theorem uniformEquicontinuityModulusToEventFlow_injective
    {x y : UniformEquicontinuityModulusUp} :
    uniformEquicontinuityModulusToEventFlow x =
        uniformEquicontinuityModulusToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      uniformEquicontinuityModulusFromEventFlow
          (uniformEquicontinuityModulusToEventFlow x) =
        uniformEquicontinuityModulusFromEventFlow
          (uniformEquicontinuityModulusToEventFlow y) :=
    congrArg uniformEquicontinuityModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (uniformEquicontinuityModulus_round_trip x).symm
      (Eq.trans hread (uniformEquicontinuityModulus_round_trip y)))

instance uniformEquicontinuityModulusBHistCarrier :
    BHistCarrier UniformEquicontinuityModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformEquicontinuityModulusToEventFlow
  fromEventFlow := uniformEquicontinuityModulusFromEventFlow

instance uniformEquicontinuityModulusChapterTasteGate :
    ChapterTasteGate UniformEquicontinuityModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      uniformEquicontinuityModulusFromEventFlow
          (uniformEquicontinuityModulusToEventFlow x) =
        some x
    exact uniformEquicontinuityModulus_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (uniformEquicontinuityModulusToEventFlow_injective heq)

theorem UniformEquicontinuityModulusTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      uniformEquicontinuityModulusDecodeBHist
          (uniformEquicontinuityModulusEncodeBHist h) =
        h) ∧
      (∀ x : UniformEquicontinuityModulusUp,
        uniformEquicontinuityModulusFromEventFlow
            (uniformEquicontinuityModulusToEventFlow x) =
          some x) ∧
        (∀ x y : UniformEquicontinuityModulusUp,
          uniformEquicontinuityModulusToEventFlow x =
              uniformEquicontinuityModulusToEventFlow y →
            x = y) ∧
          uniformEquicontinuityModulusEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact UniformEquicontinuityModulusTasteGate_single_carrier_alignment_decode
  · constructor
    · exact uniformEquicontinuityModulus_round_trip
    · constructor
      · intro x y heq
        exact uniformEquicontinuityModulusToEventFlow_injective heq
      · rfl

end BEDC.Derived.UniformEquicontinuityModulusUp
