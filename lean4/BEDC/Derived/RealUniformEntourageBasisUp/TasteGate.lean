import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealUniformEntourageBasisUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealUniformEntourageBasisUp : Type where
  | mk (R M U S F W Q H C P N : BHist) : RealUniformEntourageBasisUp
  deriving DecidableEq

def realUniformEntourageBasisEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realUniformEntourageBasisEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realUniformEntourageBasisEncodeBHist h

def realUniformEntourageBasisDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realUniformEntourageBasisDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realUniformEntourageBasisDecodeBHist tail)

private theorem RealUniformEntourageBasisTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      realUniformEntourageBasisDecodeBHist (realUniformEntourageBasisEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realUniformEntourageBasisFields : RealUniformEntourageBasisUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealUniformEntourageBasisUp.mk R M U S F W Q H C P N => [R, M, U, S, F, W, Q, H, C, P, N]

def realUniformEntourageBasisToEventFlow : RealUniformEntourageBasisUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (realUniformEntourageBasisFields x).map realUniformEntourageBasisEncodeBHist

private def realUniformEntourageBasisEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realUniformEntourageBasisEventAtDefault index rest

def realUniformEntourageBasisFromEventFlow (ef : EventFlow) :
    Option RealUniformEntourageBasisUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealUniformEntourageBasisUp.mk
      (realUniformEntourageBasisDecodeBHist (realUniformEntourageBasisEventAtDefault 0 ef))
      (realUniformEntourageBasisDecodeBHist (realUniformEntourageBasisEventAtDefault 1 ef))
      (realUniformEntourageBasisDecodeBHist (realUniformEntourageBasisEventAtDefault 2 ef))
      (realUniformEntourageBasisDecodeBHist (realUniformEntourageBasisEventAtDefault 3 ef))
      (realUniformEntourageBasisDecodeBHist (realUniformEntourageBasisEventAtDefault 4 ef))
      (realUniformEntourageBasisDecodeBHist (realUniformEntourageBasisEventAtDefault 5 ef))
      (realUniformEntourageBasisDecodeBHist (realUniformEntourageBasisEventAtDefault 6 ef))
      (realUniformEntourageBasisDecodeBHist (realUniformEntourageBasisEventAtDefault 7 ef))
      (realUniformEntourageBasisDecodeBHist (realUniformEntourageBasisEventAtDefault 8 ef))
      (realUniformEntourageBasisDecodeBHist (realUniformEntourageBasisEventAtDefault 9 ef))
      (realUniformEntourageBasisDecodeBHist (realUniformEntourageBasisEventAtDefault 10 ef)))

private theorem RealUniformEntourageBasisTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RealUniformEntourageBasisUp,
      realUniformEntourageBasisFromEventFlow (realUniformEntourageBasisToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R M U S F W Q H C P N =>
      change
        some
          (RealUniformEntourageBasisUp.mk
            (realUniformEntourageBasisDecodeBHist (realUniformEntourageBasisEncodeBHist R))
            (realUniformEntourageBasisDecodeBHist (realUniformEntourageBasisEncodeBHist M))
            (realUniformEntourageBasisDecodeBHist (realUniformEntourageBasisEncodeBHist U))
            (realUniformEntourageBasisDecodeBHist (realUniformEntourageBasisEncodeBHist S))
            (realUniformEntourageBasisDecodeBHist (realUniformEntourageBasisEncodeBHist F))
            (realUniformEntourageBasisDecodeBHist (realUniformEntourageBasisEncodeBHist W))
            (realUniformEntourageBasisDecodeBHist (realUniformEntourageBasisEncodeBHist Q))
            (realUniformEntourageBasisDecodeBHist (realUniformEntourageBasisEncodeBHist H))
            (realUniformEntourageBasisDecodeBHist (realUniformEntourageBasisEncodeBHist C))
            (realUniformEntourageBasisDecodeBHist (realUniformEntourageBasisEncodeBHist P))
            (realUniformEntourageBasisDecodeBHist (realUniformEntourageBasisEncodeBHist N))) =
          some (RealUniformEntourageBasisUp.mk R M U S F W Q H C P N)
      rw [RealUniformEntourageBasisTasteGate_single_carrier_alignment_decode R,
        RealUniformEntourageBasisTasteGate_single_carrier_alignment_decode M,
        RealUniformEntourageBasisTasteGate_single_carrier_alignment_decode U,
        RealUniformEntourageBasisTasteGate_single_carrier_alignment_decode S,
        RealUniformEntourageBasisTasteGate_single_carrier_alignment_decode F,
        RealUniformEntourageBasisTasteGate_single_carrier_alignment_decode W,
        RealUniformEntourageBasisTasteGate_single_carrier_alignment_decode Q,
        RealUniformEntourageBasisTasteGate_single_carrier_alignment_decode H,
        RealUniformEntourageBasisTasteGate_single_carrier_alignment_decode C,
        RealUniformEntourageBasisTasteGate_single_carrier_alignment_decode P,
        RealUniformEntourageBasisTasteGate_single_carrier_alignment_decode N]

private theorem RealUniformEntourageBasisTasteGate_single_carrier_alignment_injective
    {x y : RealUniformEntourageBasisUp} :
    realUniformEntourageBasisToEventFlow x = realUniformEntourageBasisToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realUniformEntourageBasisFromEventFlow (realUniformEntourageBasisToEventFlow x) =
        realUniformEntourageBasisFromEventFlow (realUniformEntourageBasisToEventFlow y) :=
    congrArg realUniformEntourageBasisFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RealUniformEntourageBasisTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RealUniformEntourageBasisTasteGate_single_carrier_alignment_round_trip y)))

instance realUniformEntourageBasisBHistCarrier : BHistCarrier RealUniformEntourageBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realUniformEntourageBasisToEventFlow
  fromEventFlow := realUniformEntourageBasisFromEventFlow

instance realUniformEntourageBasisChapterTasteGate :
    ChapterTasteGate RealUniformEntourageBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realUniformEntourageBasisFromEventFlow (realUniformEntourageBasisToEventFlow x) = some x
    exact RealUniformEntourageBasisTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RealUniformEntourageBasisTasteGate_single_carrier_alignment_injective heq)

theorem RealUniformEntourageBasisTasteGate_single_carrier_alignment :
    (forall h : BHist, realUniformEntourageBasisDecodeBHist
      (realUniformEntourageBasisEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier RealUniformEntourageBasisUp) ∧
        Nonempty (ChapterTasteGate RealUniformEntourageBasisUp) ∧
          realUniformEntourageBasisEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨RealUniformEntourageBasisTasteGate_single_carrier_alignment_decode,
      ⟨⟨realUniformEntourageBasisBHistCarrier⟩,
        ⟨realUniformEntourageBasisChapterTasteGate⟩,
        rfl⟩⟩

end BEDC.Derived.RealUniformEntourageBasisUp
