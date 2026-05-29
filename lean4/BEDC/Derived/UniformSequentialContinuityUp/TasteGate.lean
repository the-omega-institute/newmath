import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformSequentialContinuityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniformSequentialContinuityUp : Type where
  | mk
      (F M S W_X W_Y R_X R_Y D_X D_Y E_X E_Y H C P N : BHist) :
      UniformSequentialContinuityUp
  deriving DecidableEq

def uniformSequentialContinuityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformSequentialContinuityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformSequentialContinuityEncodeBHist h

def uniformSequentialContinuityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformSequentialContinuityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformSequentialContinuityDecodeBHist tail)

private theorem UniformSequentialContinuityTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      uniformSequentialContinuityDecodeBHist
        (uniformSequentialContinuityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def uniformSequentialContinuityFields :
    UniformSequentialContinuityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UniformSequentialContinuityUp.mk
      F M S W_X W_Y R_X R_Y D_X D_Y E_X E_Y H C P N =>
      [F, M, S, W_X, W_Y, R_X, R_Y, D_X, D_Y, E_X, E_Y, H, C, P, N]

def uniformSequentialContinuityToEventFlow :
    UniformSequentialContinuityUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (uniformSequentialContinuityFields x).map uniformSequentialContinuityEncodeBHist

def uniformSequentialContinuityEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      uniformSequentialContinuityEventAtDefault index rest

def uniformSequentialContinuityFromEventFlow :
    EventFlow → Option UniformSequentialContinuityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (UniformSequentialContinuityUp.mk
        (uniformSequentialContinuityDecodeBHist
          (uniformSequentialContinuityEventAtDefault 0 ef))
        (uniformSequentialContinuityDecodeBHist
          (uniformSequentialContinuityEventAtDefault 1 ef))
        (uniformSequentialContinuityDecodeBHist
          (uniformSequentialContinuityEventAtDefault 2 ef))
        (uniformSequentialContinuityDecodeBHist
          (uniformSequentialContinuityEventAtDefault 3 ef))
        (uniformSequentialContinuityDecodeBHist
          (uniformSequentialContinuityEventAtDefault 4 ef))
        (uniformSequentialContinuityDecodeBHist
          (uniformSequentialContinuityEventAtDefault 5 ef))
        (uniformSequentialContinuityDecodeBHist
          (uniformSequentialContinuityEventAtDefault 6 ef))
        (uniformSequentialContinuityDecodeBHist
          (uniformSequentialContinuityEventAtDefault 7 ef))
        (uniformSequentialContinuityDecodeBHist
          (uniformSequentialContinuityEventAtDefault 8 ef))
        (uniformSequentialContinuityDecodeBHist
          (uniformSequentialContinuityEventAtDefault 9 ef))
        (uniformSequentialContinuityDecodeBHist
          (uniformSequentialContinuityEventAtDefault 10 ef))
        (uniformSequentialContinuityDecodeBHist
          (uniformSequentialContinuityEventAtDefault 11 ef))
        (uniformSequentialContinuityDecodeBHist
          (uniformSequentialContinuityEventAtDefault 12 ef))
        (uniformSequentialContinuityDecodeBHist
          (uniformSequentialContinuityEventAtDefault 13 ef))
        (uniformSequentialContinuityDecodeBHist
          (uniformSequentialContinuityEventAtDefault 14 ef)))

private theorem UniformSequentialContinuityTasteGate_single_carrier_alignment_round_trip :
    ∀ x : UniformSequentialContinuityUp,
      uniformSequentialContinuityFromEventFlow
        (uniformSequentialContinuityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F M S W_X W_Y R_X R_Y D_X D_Y E_X E_Y H C P N =>
      change
        some
          (UniformSequentialContinuityUp.mk
            (uniformSequentialContinuityDecodeBHist
              (uniformSequentialContinuityEncodeBHist F))
            (uniformSequentialContinuityDecodeBHist
              (uniformSequentialContinuityEncodeBHist M))
            (uniformSequentialContinuityDecodeBHist
              (uniformSequentialContinuityEncodeBHist S))
            (uniformSequentialContinuityDecodeBHist
              (uniformSequentialContinuityEncodeBHist W_X))
            (uniformSequentialContinuityDecodeBHist
              (uniformSequentialContinuityEncodeBHist W_Y))
            (uniformSequentialContinuityDecodeBHist
              (uniformSequentialContinuityEncodeBHist R_X))
            (uniformSequentialContinuityDecodeBHist
              (uniformSequentialContinuityEncodeBHist R_Y))
            (uniformSequentialContinuityDecodeBHist
              (uniformSequentialContinuityEncodeBHist D_X))
            (uniformSequentialContinuityDecodeBHist
              (uniformSequentialContinuityEncodeBHist D_Y))
            (uniformSequentialContinuityDecodeBHist
              (uniformSequentialContinuityEncodeBHist E_X))
            (uniformSequentialContinuityDecodeBHist
              (uniformSequentialContinuityEncodeBHist E_Y))
            (uniformSequentialContinuityDecodeBHist
              (uniformSequentialContinuityEncodeBHist H))
            (uniformSequentialContinuityDecodeBHist
              (uniformSequentialContinuityEncodeBHist C))
            (uniformSequentialContinuityDecodeBHist
              (uniformSequentialContinuityEncodeBHist P))
            (uniformSequentialContinuityDecodeBHist
              (uniformSequentialContinuityEncodeBHist N))) =
          some (UniformSequentialContinuityUp.mk
            F M S W_X W_Y R_X R_Y D_X D_Y E_X E_Y H C P N)
      rw [UniformSequentialContinuityTasteGate_single_carrier_alignment_decode F,
        UniformSequentialContinuityTasteGate_single_carrier_alignment_decode M,
        UniformSequentialContinuityTasteGate_single_carrier_alignment_decode S,
        UniformSequentialContinuityTasteGate_single_carrier_alignment_decode W_X,
        UniformSequentialContinuityTasteGate_single_carrier_alignment_decode W_Y,
        UniformSequentialContinuityTasteGate_single_carrier_alignment_decode R_X,
        UniformSequentialContinuityTasteGate_single_carrier_alignment_decode R_Y,
        UniformSequentialContinuityTasteGate_single_carrier_alignment_decode D_X,
        UniformSequentialContinuityTasteGate_single_carrier_alignment_decode D_Y,
        UniformSequentialContinuityTasteGate_single_carrier_alignment_decode E_X,
        UniformSequentialContinuityTasteGate_single_carrier_alignment_decode E_Y,
        UniformSequentialContinuityTasteGate_single_carrier_alignment_decode H,
        UniformSequentialContinuityTasteGate_single_carrier_alignment_decode C,
        UniformSequentialContinuityTasteGate_single_carrier_alignment_decode P,
        UniformSequentialContinuityTasteGate_single_carrier_alignment_decode N]

private theorem UniformSequentialContinuityTasteGate_single_carrier_alignment_injective
    {x y : UniformSequentialContinuityUp} :
    uniformSequentialContinuityToEventFlow x =
      uniformSequentialContinuityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      uniformSequentialContinuityFromEventFlow
          (uniformSequentialContinuityToEventFlow x) =
        uniformSequentialContinuityFromEventFlow
          (uniformSequentialContinuityToEventFlow y) :=
    congrArg uniformSequentialContinuityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (UniformSequentialContinuityTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (UniformSequentialContinuityTasteGate_single_carrier_alignment_round_trip y)))

instance uniformSequentialContinuityBHistCarrier :
    BHistCarrier UniformSequentialContinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformSequentialContinuityToEventFlow
  fromEventFlow := uniformSequentialContinuityFromEventFlow

instance uniformSequentialContinuityChapterTasteGate :
    ChapterTasteGate UniformSequentialContinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      uniformSequentialContinuityFromEventFlow
        (uniformSequentialContinuityToEventFlow x) = some x
    exact UniformSequentialContinuityTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (UniformSequentialContinuityTasteGate_single_carrier_alignment_injective heq)

theorem UniformSequentialContinuityTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      uniformSequentialContinuityDecodeBHist
        (uniformSequentialContinuityEncodeBHist h) = h) ∧
      (∀ x : UniformSequentialContinuityUp,
        uniformSequentialContinuityFromEventFlow
          (uniformSequentialContinuityToEventFlow x) = some x) ∧
      (∀ x y : UniformSequentialContinuityUp,
        uniformSequentialContinuityToEventFlow x =
          uniformSequentialContinuityToEventFlow y → x = y) ∧
      uniformSequentialContinuityEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact UniformSequentialContinuityTasteGate_single_carrier_alignment_decode
  constructor
  · exact UniformSequentialContinuityTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact UniformSequentialContinuityTasteGate_single_carrier_alignment_injective heq
  · rfl

end BEDC.Derived.UniformSequentialContinuityUp
