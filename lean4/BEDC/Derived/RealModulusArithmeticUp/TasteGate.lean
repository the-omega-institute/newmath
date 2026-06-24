import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealModulusArithmeticUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealModulusArithmeticUp : Type where
  | mk
      (X0 X1 Mu0 Mu1 A U D W R Sum Product E H C P N : BHist) :
      RealModulusArithmeticUp
  deriving DecidableEq

def realModulusArithmeticEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realModulusArithmeticEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realModulusArithmeticEncodeBHist h

def realModulusArithmeticDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realModulusArithmeticDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realModulusArithmeticDecodeBHist tail)

private theorem RealModulusArithmeticUpTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      realModulusArithmeticDecodeBHist (realModulusArithmeticEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realModulusArithmeticFields : RealModulusArithmeticUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealModulusArithmeticUp.mk X0 X1 Mu0 Mu1 A U D W R Sum Product E H C P N =>
      [X0, X1, Mu0, Mu1, A, U, D, W, R, Sum, Product, E, H, C, P, N]

def realModulusArithmeticToEventFlow : RealModulusArithmeticUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map realModulusArithmeticEncodeBHist (realModulusArithmeticFields x)

private def realModulusArithmeticEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realModulusArithmeticEventAtDefault index rest

def realModulusArithmeticFromEventFlow
    (ef : EventFlow) : Option RealModulusArithmeticUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealModulusArithmeticUp.mk
      (realModulusArithmeticDecodeBHist (realModulusArithmeticEventAtDefault 0 ef))
      (realModulusArithmeticDecodeBHist (realModulusArithmeticEventAtDefault 1 ef))
      (realModulusArithmeticDecodeBHist (realModulusArithmeticEventAtDefault 2 ef))
      (realModulusArithmeticDecodeBHist (realModulusArithmeticEventAtDefault 3 ef))
      (realModulusArithmeticDecodeBHist (realModulusArithmeticEventAtDefault 4 ef))
      (realModulusArithmeticDecodeBHist (realModulusArithmeticEventAtDefault 5 ef))
      (realModulusArithmeticDecodeBHist (realModulusArithmeticEventAtDefault 6 ef))
      (realModulusArithmeticDecodeBHist (realModulusArithmeticEventAtDefault 7 ef))
      (realModulusArithmeticDecodeBHist (realModulusArithmeticEventAtDefault 8 ef))
      (realModulusArithmeticDecodeBHist (realModulusArithmeticEventAtDefault 9 ef))
      (realModulusArithmeticDecodeBHist (realModulusArithmeticEventAtDefault 10 ef))
      (realModulusArithmeticDecodeBHist (realModulusArithmeticEventAtDefault 11 ef))
      (realModulusArithmeticDecodeBHist (realModulusArithmeticEventAtDefault 12 ef))
      (realModulusArithmeticDecodeBHist (realModulusArithmeticEventAtDefault 13 ef))
      (realModulusArithmeticDecodeBHist (realModulusArithmeticEventAtDefault 14 ef))
      (realModulusArithmeticDecodeBHist (realModulusArithmeticEventAtDefault 15 ef)))

private theorem RealModulusArithmeticUpTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RealModulusArithmeticUp,
      realModulusArithmeticFromEventFlow (realModulusArithmeticToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X0 X1 Mu0 Mu1 A U D W R Sum Product E H C P N =>
      change
        some
          (RealModulusArithmeticUp.mk
            (realModulusArithmeticDecodeBHist (realModulusArithmeticEncodeBHist X0))
            (realModulusArithmeticDecodeBHist (realModulusArithmeticEncodeBHist X1))
            (realModulusArithmeticDecodeBHist (realModulusArithmeticEncodeBHist Mu0))
            (realModulusArithmeticDecodeBHist (realModulusArithmeticEncodeBHist Mu1))
            (realModulusArithmeticDecodeBHist (realModulusArithmeticEncodeBHist A))
            (realModulusArithmeticDecodeBHist (realModulusArithmeticEncodeBHist U))
            (realModulusArithmeticDecodeBHist (realModulusArithmeticEncodeBHist D))
            (realModulusArithmeticDecodeBHist (realModulusArithmeticEncodeBHist W))
            (realModulusArithmeticDecodeBHist (realModulusArithmeticEncodeBHist R))
            (realModulusArithmeticDecodeBHist (realModulusArithmeticEncodeBHist Sum))
            (realModulusArithmeticDecodeBHist (realModulusArithmeticEncodeBHist Product))
            (realModulusArithmeticDecodeBHist (realModulusArithmeticEncodeBHist E))
            (realModulusArithmeticDecodeBHist (realModulusArithmeticEncodeBHist H))
            (realModulusArithmeticDecodeBHist (realModulusArithmeticEncodeBHist C))
            (realModulusArithmeticDecodeBHist (realModulusArithmeticEncodeBHist P))
            (realModulusArithmeticDecodeBHist (realModulusArithmeticEncodeBHist N))) =
          some (RealModulusArithmeticUp.mk X0 X1 Mu0 Mu1 A U D W R Sum Product E H C P N)
      rw [RealModulusArithmeticUpTasteGate_single_carrier_alignment_decode X0,
        RealModulusArithmeticUpTasteGate_single_carrier_alignment_decode X1,
        RealModulusArithmeticUpTasteGate_single_carrier_alignment_decode Mu0,
        RealModulusArithmeticUpTasteGate_single_carrier_alignment_decode Mu1,
        RealModulusArithmeticUpTasteGate_single_carrier_alignment_decode A,
        RealModulusArithmeticUpTasteGate_single_carrier_alignment_decode U,
        RealModulusArithmeticUpTasteGate_single_carrier_alignment_decode D,
        RealModulusArithmeticUpTasteGate_single_carrier_alignment_decode W,
        RealModulusArithmeticUpTasteGate_single_carrier_alignment_decode R,
        RealModulusArithmeticUpTasteGate_single_carrier_alignment_decode Sum,
        RealModulusArithmeticUpTasteGate_single_carrier_alignment_decode Product,
        RealModulusArithmeticUpTasteGate_single_carrier_alignment_decode E,
        RealModulusArithmeticUpTasteGate_single_carrier_alignment_decode H,
        RealModulusArithmeticUpTasteGate_single_carrier_alignment_decode C,
        RealModulusArithmeticUpTasteGate_single_carrier_alignment_decode P,
        RealModulusArithmeticUpTasteGate_single_carrier_alignment_decode N]

private theorem realModulusArithmeticToEventFlow_injective
    {x y : RealModulusArithmeticUp} :
    realModulusArithmeticToEventFlow x = realModulusArithmeticToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realModulusArithmeticFromEventFlow (realModulusArithmeticToEventFlow x) =
        realModulusArithmeticFromEventFlow (realModulusArithmeticToEventFlow y) :=
    congrArg realModulusArithmeticFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RealModulusArithmeticUpTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RealModulusArithmeticUpTasteGate_single_carrier_alignment_round_trip y)))

instance realModulusArithmeticBHistCarrier : BHistCarrier RealModulusArithmeticUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realModulusArithmeticToEventFlow
  fromEventFlow := realModulusArithmeticFromEventFlow

instance realModulusArithmeticChapterTasteGate :
    ChapterTasteGate RealModulusArithmeticUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realModulusArithmeticFromEventFlow (realModulusArithmeticToEventFlow x) = some x
    exact RealModulusArithmeticUpTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realModulusArithmeticToEventFlow_injective heq)

theorem RealModulusArithmeticUpTasteGate_single_carrier_alignment :
    (∀ h : BHist, realModulusArithmeticDecodeBHist (realModulusArithmeticEncodeBHist h) = h) ∧
      (∀ x : RealModulusArithmeticUp,
        realModulusArithmeticFromEventFlow (realModulusArithmeticToEventFlow x) = some x) ∧
        (∀ x y : RealModulusArithmeticUp,
          realModulusArithmeticToEventFlow x = realModulusArithmeticToEventFlow y → x = y) ∧
          realModulusArithmeticEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨RealModulusArithmeticUpTasteGate_single_carrier_alignment_decode,
      RealModulusArithmeticUpTasteGate_single_carrier_alignment_round_trip,
      by
        intro x y heq
        exact realModulusArithmeticToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.RealModulusArithmeticUp
