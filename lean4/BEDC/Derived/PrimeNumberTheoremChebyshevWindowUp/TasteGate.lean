import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PrimeNumberTheoremChebyshevWindowUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PrimeNumberTheoremChebyshevWindowUp : Type where
  | mk (A P W L R D Y E O Q N : BHist) : PrimeNumberTheoremChebyshevWindowUp
  deriving DecidableEq

def primeNumberTheoremChebyshevWindowEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: primeNumberTheoremChebyshevWindowEncodeBHist h
  | BHist.e1 h => BMark.b1 :: primeNumberTheoremChebyshevWindowEncodeBHist h

def primeNumberTheoremChebyshevWindowDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (primeNumberTheoremChebyshevWindowDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (primeNumberTheoremChebyshevWindowDecodeBHist tail)

private theorem PrimeNumberTheoremChebyshevWindowTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      primeNumberTheoremChebyshevWindowDecodeBHist
        (primeNumberTheoremChebyshevWindowEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def primeNumberTheoremChebyshevWindowFields :
    PrimeNumberTheoremChebyshevWindowUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PrimeNumberTheoremChebyshevWindowUp.mk A P W L R D Y E O Q N =>
      [A, P, W, L, R, D, Y, E, O, Q, N]

def primeNumberTheoremChebyshevWindowToEventFlow :
    PrimeNumberTheoremChebyshevWindowUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (primeNumberTheoremChebyshevWindowFields x).map
      primeNumberTheoremChebyshevWindowEncodeBHist

private def primeNumberTheoremChebyshevWindowEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      primeNumberTheoremChebyshevWindowEventAtDefault index rest

def primeNumberTheoremChebyshevWindowFromEventFlow
    (ef : EventFlow) : Option PrimeNumberTheoremChebyshevWindowUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (PrimeNumberTheoremChebyshevWindowUp.mk
      (primeNumberTheoremChebyshevWindowDecodeBHist
        (primeNumberTheoremChebyshevWindowEventAtDefault 0 ef))
      (primeNumberTheoremChebyshevWindowDecodeBHist
        (primeNumberTheoremChebyshevWindowEventAtDefault 1 ef))
      (primeNumberTheoremChebyshevWindowDecodeBHist
        (primeNumberTheoremChebyshevWindowEventAtDefault 2 ef))
      (primeNumberTheoremChebyshevWindowDecodeBHist
        (primeNumberTheoremChebyshevWindowEventAtDefault 3 ef))
      (primeNumberTheoremChebyshevWindowDecodeBHist
        (primeNumberTheoremChebyshevWindowEventAtDefault 4 ef))
      (primeNumberTheoremChebyshevWindowDecodeBHist
        (primeNumberTheoremChebyshevWindowEventAtDefault 5 ef))
      (primeNumberTheoremChebyshevWindowDecodeBHist
        (primeNumberTheoremChebyshevWindowEventAtDefault 6 ef))
      (primeNumberTheoremChebyshevWindowDecodeBHist
        (primeNumberTheoremChebyshevWindowEventAtDefault 7 ef))
      (primeNumberTheoremChebyshevWindowDecodeBHist
        (primeNumberTheoremChebyshevWindowEventAtDefault 8 ef))
      (primeNumberTheoremChebyshevWindowDecodeBHist
        (primeNumberTheoremChebyshevWindowEventAtDefault 9 ef))
      (primeNumberTheoremChebyshevWindowDecodeBHist
        (primeNumberTheoremChebyshevWindowEventAtDefault 10 ef)))

private theorem PrimeNumberTheoremChebyshevWindowTasteGate_single_carrier_alignment_round_trip :
    ∀ x : PrimeNumberTheoremChebyshevWindowUp,
      primeNumberTheoremChebyshevWindowFromEventFlow
        (primeNumberTheoremChebyshevWindowToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A P W L R D Y E O Q N =>
      change
        some
          (PrimeNumberTheoremChebyshevWindowUp.mk
            (primeNumberTheoremChebyshevWindowDecodeBHist
              (primeNumberTheoremChebyshevWindowEncodeBHist A))
            (primeNumberTheoremChebyshevWindowDecodeBHist
              (primeNumberTheoremChebyshevWindowEncodeBHist P))
            (primeNumberTheoremChebyshevWindowDecodeBHist
              (primeNumberTheoremChebyshevWindowEncodeBHist W))
            (primeNumberTheoremChebyshevWindowDecodeBHist
              (primeNumberTheoremChebyshevWindowEncodeBHist L))
            (primeNumberTheoremChebyshevWindowDecodeBHist
              (primeNumberTheoremChebyshevWindowEncodeBHist R))
            (primeNumberTheoremChebyshevWindowDecodeBHist
              (primeNumberTheoremChebyshevWindowEncodeBHist D))
            (primeNumberTheoremChebyshevWindowDecodeBHist
              (primeNumberTheoremChebyshevWindowEncodeBHist Y))
            (primeNumberTheoremChebyshevWindowDecodeBHist
              (primeNumberTheoremChebyshevWindowEncodeBHist E))
            (primeNumberTheoremChebyshevWindowDecodeBHist
              (primeNumberTheoremChebyshevWindowEncodeBHist O))
            (primeNumberTheoremChebyshevWindowDecodeBHist
              (primeNumberTheoremChebyshevWindowEncodeBHist Q))
            (primeNumberTheoremChebyshevWindowDecodeBHist
              (primeNumberTheoremChebyshevWindowEncodeBHist N))) =
          some (PrimeNumberTheoremChebyshevWindowUp.mk A P W L R D Y E O Q N)
      rw [PrimeNumberTheoremChebyshevWindowTasteGate_single_carrier_alignment_decode A,
        PrimeNumberTheoremChebyshevWindowTasteGate_single_carrier_alignment_decode P,
        PrimeNumberTheoremChebyshevWindowTasteGate_single_carrier_alignment_decode W,
        PrimeNumberTheoremChebyshevWindowTasteGate_single_carrier_alignment_decode L,
        PrimeNumberTheoremChebyshevWindowTasteGate_single_carrier_alignment_decode R,
        PrimeNumberTheoremChebyshevWindowTasteGate_single_carrier_alignment_decode D,
        PrimeNumberTheoremChebyshevWindowTasteGate_single_carrier_alignment_decode Y,
        PrimeNumberTheoremChebyshevWindowTasteGate_single_carrier_alignment_decode E,
        PrimeNumberTheoremChebyshevWindowTasteGate_single_carrier_alignment_decode O,
        PrimeNumberTheoremChebyshevWindowTasteGate_single_carrier_alignment_decode Q,
        PrimeNumberTheoremChebyshevWindowTasteGate_single_carrier_alignment_decode N]

private theorem PrimeNumberTheoremChebyshevWindowTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : PrimeNumberTheoremChebyshevWindowUp} :
    primeNumberTheoremChebyshevWindowToEventFlow x =
      primeNumberTheoremChebyshevWindowToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      primeNumberTheoremChebyshevWindowFromEventFlow
          (primeNumberTheoremChebyshevWindowToEventFlow x) =
        primeNumberTheoremChebyshevWindowFromEventFlow
          (primeNumberTheoremChebyshevWindowToEventFlow y) :=
    congrArg primeNumberTheoremChebyshevWindowFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (PrimeNumberTheoremChebyshevWindowTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (PrimeNumberTheoremChebyshevWindowTasteGate_single_carrier_alignment_round_trip y)))

instance primeNumberTheoremChebyshevWindowBHistCarrier :
    BHistCarrier PrimeNumberTheoremChebyshevWindowUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := primeNumberTheoremChebyshevWindowToEventFlow
  fromEventFlow := primeNumberTheoremChebyshevWindowFromEventFlow

instance primeNumberTheoremChebyshevWindowChapterTasteGate :
    ChapterTasteGate PrimeNumberTheoremChebyshevWindowUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      primeNumberTheoremChebyshevWindowFromEventFlow
        (primeNumberTheoremChebyshevWindowToEventFlow x) = some x
    exact PrimeNumberTheoremChebyshevWindowTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro _x _y hxy heq
    exact hxy
      (PrimeNumberTheoremChebyshevWindowTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

def taste_gate : ChapterTasteGate PrimeNumberTheoremChebyshevWindowUp :=
  -- BEDC touchpoint anchor: BHist BMark
  primeNumberTheoremChebyshevWindowChapterTasteGate

theorem PrimeNumberTheoremChebyshevWindowTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      primeNumberTheoremChebyshevWindowDecodeBHist
        (primeNumberTheoremChebyshevWindowEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier PrimeNumberTheoremChebyshevWindowUp) ∧
        Nonempty (ChapterTasteGate PrimeNumberTheoremChebyshevWindowUp) ∧
          primeNumberTheoremChebyshevWindowEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨PrimeNumberTheoremChebyshevWindowTasteGate_single_carrier_alignment_decode,
      ⟨primeNumberTheoremChebyshevWindowBHistCarrier⟩,
      ⟨primeNumberTheoremChebyshevWindowChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.PrimeNumberTheoremChebyshevWindowUp
