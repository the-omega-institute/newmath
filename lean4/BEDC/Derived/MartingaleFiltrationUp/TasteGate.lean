import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MartingaleFiltrationUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MartingaleFiltrationUp : Type where
  | mk (Omega W A C S B T R P N : BHist) : MartingaleFiltrationUp

def martingaleFiltrationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: martingaleFiltrationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: martingaleFiltrationEncodeBHist h

def martingaleFiltrationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (martingaleFiltrationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (martingaleFiltrationDecodeBHist tail)

private theorem MartingaleFiltrationTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      martingaleFiltrationDecodeBHist (martingaleFiltrationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def martingaleFiltrationFields : MartingaleFiltrationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MartingaleFiltrationUp.mk Omega W A C S B T R P N =>
      [Omega, W, A, C, S, B, T, R, P, N]

def martingaleFiltrationToEventFlow : MartingaleFiltrationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (martingaleFiltrationFields x).map martingaleFiltrationEncodeBHist

private def martingaleFiltrationEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => martingaleFiltrationEventAtDefault index rest

def martingaleFiltrationFromEventFlow :
    EventFlow → Option MartingaleFiltrationUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (MartingaleFiltrationUp.mk
          (martingaleFiltrationDecodeBHist (martingaleFiltrationEventAtDefault 0 ef))
          (martingaleFiltrationDecodeBHist (martingaleFiltrationEventAtDefault 1 ef))
          (martingaleFiltrationDecodeBHist (martingaleFiltrationEventAtDefault 2 ef))
          (martingaleFiltrationDecodeBHist (martingaleFiltrationEventAtDefault 3 ef))
          (martingaleFiltrationDecodeBHist (martingaleFiltrationEventAtDefault 4 ef))
          (martingaleFiltrationDecodeBHist (martingaleFiltrationEventAtDefault 5 ef))
          (martingaleFiltrationDecodeBHist (martingaleFiltrationEventAtDefault 6 ef))
          (martingaleFiltrationDecodeBHist (martingaleFiltrationEventAtDefault 7 ef))
          (martingaleFiltrationDecodeBHist (martingaleFiltrationEventAtDefault 8 ef))
          (martingaleFiltrationDecodeBHist (martingaleFiltrationEventAtDefault 9 ef)))

private theorem MartingaleFiltrationTasteGate_single_carrier_alignment_round_trip
    (x : MartingaleFiltrationUp) :
    martingaleFiltrationFromEventFlow (martingaleFiltrationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk Omega W A C S B T R P N =>
      change
        some
          (MartingaleFiltrationUp.mk
            (martingaleFiltrationDecodeBHist (martingaleFiltrationEncodeBHist Omega))
            (martingaleFiltrationDecodeBHist (martingaleFiltrationEncodeBHist W))
            (martingaleFiltrationDecodeBHist (martingaleFiltrationEncodeBHist A))
            (martingaleFiltrationDecodeBHist (martingaleFiltrationEncodeBHist C))
            (martingaleFiltrationDecodeBHist (martingaleFiltrationEncodeBHist S))
            (martingaleFiltrationDecodeBHist (martingaleFiltrationEncodeBHist B))
            (martingaleFiltrationDecodeBHist (martingaleFiltrationEncodeBHist T))
            (martingaleFiltrationDecodeBHist (martingaleFiltrationEncodeBHist R))
            (martingaleFiltrationDecodeBHist (martingaleFiltrationEncodeBHist P))
            (martingaleFiltrationDecodeBHist (martingaleFiltrationEncodeBHist N))) =
          some (MartingaleFiltrationUp.mk Omega W A C S B T R P N)
      rw [MartingaleFiltrationTasteGate_single_carrier_alignment_decode Omega,
        MartingaleFiltrationTasteGate_single_carrier_alignment_decode W,
        MartingaleFiltrationTasteGate_single_carrier_alignment_decode A,
        MartingaleFiltrationTasteGate_single_carrier_alignment_decode C,
        MartingaleFiltrationTasteGate_single_carrier_alignment_decode S,
        MartingaleFiltrationTasteGate_single_carrier_alignment_decode B,
        MartingaleFiltrationTasteGate_single_carrier_alignment_decode T,
        MartingaleFiltrationTasteGate_single_carrier_alignment_decode R,
        MartingaleFiltrationTasteGate_single_carrier_alignment_decode P,
        MartingaleFiltrationTasteGate_single_carrier_alignment_decode N]

private theorem MartingaleFiltrationTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : MartingaleFiltrationUp} :
    martingaleFiltrationToEventFlow x = martingaleFiltrationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      martingaleFiltrationFromEventFlow (martingaleFiltrationToEventFlow x) =
        martingaleFiltrationFromEventFlow (martingaleFiltrationToEventFlow y) :=
    congrArg martingaleFiltrationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (MartingaleFiltrationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (MartingaleFiltrationTasteGate_single_carrier_alignment_round_trip y)))

instance martingaleFiltrationBHistCarrier :
    BHistCarrier MartingaleFiltrationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := martingaleFiltrationToEventFlow
  fromEventFlow := martingaleFiltrationFromEventFlow

instance martingaleFiltrationChapterTasteGate :
    ChapterTasteGate MartingaleFiltrationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change martingaleFiltrationFromEventFlow (martingaleFiltrationToEventFlow x) = some x
    exact MartingaleFiltrationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (MartingaleFiltrationTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate MartingaleFiltrationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  martingaleFiltrationChapterTasteGate

theorem MartingaleFiltrationTasteGate_single_carrier_alignment :
    (∀ h : BHist, martingaleFiltrationDecodeBHist (martingaleFiltrationEncodeBHist h) = h) ∧
      (∀ x : MartingaleFiltrationUp,
        martingaleFiltrationFromEventFlow (martingaleFiltrationToEventFlow x) = some x) ∧
        (∀ x y : MartingaleFiltrationUp,
          martingaleFiltrationToEventFlow x = martingaleFiltrationToEventFlow y → x = y) ∧
          martingaleFiltrationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact MartingaleFiltrationTasteGate_single_carrier_alignment_decode
  · constructor
    · exact MartingaleFiltrationTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact MartingaleFiltrationTasteGate_single_carrier_alignment_toEventFlow_injective heq
      · rfl

end BEDC.Derived.MartingaleFiltrationUp.TasteGate
