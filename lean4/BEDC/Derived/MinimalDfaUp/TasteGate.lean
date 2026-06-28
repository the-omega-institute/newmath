import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MinimalDfaUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MinimalDfaUp : Type where
  | mk (Sigma L E C W Q delta q0 F A alpha eta kappa H R P N : BHist) : MinimalDfaUp
  deriving DecidableEq

def minimalDfaFields : MinimalDfaUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MinimalDfaUp.mk Sigma L E C W Q delta q0 F A alpha eta kappa H R P N =>
      [Sigma, L, E, C, W, Q, delta, q0, F, A, alpha, eta, kappa, H, R, P, N]

def minimalDfaEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: minimalDfaEncodeBHist h
  | BHist.e1 h => BMark.b1 :: minimalDfaEncodeBHist h

def minimalDfaDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (minimalDfaDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (minimalDfaDecodeBHist tail)

private theorem MinimalDfaTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, minimalDfaDecodeBHist (minimalDfaEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def minimalDfaToEventFlow : MinimalDfaUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (minimalDfaFields x).map minimalDfaEncodeBHist

private def minimalDfaEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => minimalDfaEventAtDefault index rest

def minimalDfaFromEventFlow (ef : EventFlow) : Option MinimalDfaUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MinimalDfaUp.mk
      (minimalDfaDecodeBHist (minimalDfaEventAtDefault 0 ef))
      (minimalDfaDecodeBHist (minimalDfaEventAtDefault 1 ef))
      (minimalDfaDecodeBHist (minimalDfaEventAtDefault 2 ef))
      (minimalDfaDecodeBHist (minimalDfaEventAtDefault 3 ef))
      (minimalDfaDecodeBHist (minimalDfaEventAtDefault 4 ef))
      (minimalDfaDecodeBHist (minimalDfaEventAtDefault 5 ef))
      (minimalDfaDecodeBHist (minimalDfaEventAtDefault 6 ef))
      (minimalDfaDecodeBHist (minimalDfaEventAtDefault 7 ef))
      (minimalDfaDecodeBHist (minimalDfaEventAtDefault 8 ef))
      (minimalDfaDecodeBHist (minimalDfaEventAtDefault 9 ef))
      (minimalDfaDecodeBHist (minimalDfaEventAtDefault 10 ef))
      (minimalDfaDecodeBHist (minimalDfaEventAtDefault 11 ef))
      (minimalDfaDecodeBHist (minimalDfaEventAtDefault 12 ef))
      (minimalDfaDecodeBHist (minimalDfaEventAtDefault 13 ef))
      (minimalDfaDecodeBHist (minimalDfaEventAtDefault 14 ef))
      (minimalDfaDecodeBHist (minimalDfaEventAtDefault 15 ef))
      (minimalDfaDecodeBHist (minimalDfaEventAtDefault 16 ef)))

private theorem MinimalDfaTasteGate_single_carrier_alignment_round_trip :
    ∀ x : MinimalDfaUp, minimalDfaFromEventFlow (minimalDfaToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Sigma L E C W Q delta q0 F A alpha eta kappa H R P N =>
      change
        some
          (MinimalDfaUp.mk
            (minimalDfaDecodeBHist (minimalDfaEncodeBHist Sigma))
            (minimalDfaDecodeBHist (minimalDfaEncodeBHist L))
            (minimalDfaDecodeBHist (minimalDfaEncodeBHist E))
            (minimalDfaDecodeBHist (minimalDfaEncodeBHist C))
            (minimalDfaDecodeBHist (minimalDfaEncodeBHist W))
            (minimalDfaDecodeBHist (minimalDfaEncodeBHist Q))
            (minimalDfaDecodeBHist (minimalDfaEncodeBHist delta))
            (minimalDfaDecodeBHist (minimalDfaEncodeBHist q0))
            (minimalDfaDecodeBHist (minimalDfaEncodeBHist F))
            (minimalDfaDecodeBHist (minimalDfaEncodeBHist A))
            (minimalDfaDecodeBHist (minimalDfaEncodeBHist alpha))
            (minimalDfaDecodeBHist (minimalDfaEncodeBHist eta))
            (minimalDfaDecodeBHist (minimalDfaEncodeBHist kappa))
            (minimalDfaDecodeBHist (minimalDfaEncodeBHist H))
            (minimalDfaDecodeBHist (minimalDfaEncodeBHist R))
            (minimalDfaDecodeBHist (minimalDfaEncodeBHist P))
            (minimalDfaDecodeBHist (minimalDfaEncodeBHist N))) =
          some (MinimalDfaUp.mk Sigma L E C W Q delta q0 F A alpha eta kappa H R P N)
      rw [MinimalDfaTasteGate_single_carrier_alignment_decode Sigma,
        MinimalDfaTasteGate_single_carrier_alignment_decode L,
        MinimalDfaTasteGate_single_carrier_alignment_decode E,
        MinimalDfaTasteGate_single_carrier_alignment_decode C,
        MinimalDfaTasteGate_single_carrier_alignment_decode W,
        MinimalDfaTasteGate_single_carrier_alignment_decode Q,
        MinimalDfaTasteGate_single_carrier_alignment_decode delta,
        MinimalDfaTasteGate_single_carrier_alignment_decode q0,
        MinimalDfaTasteGate_single_carrier_alignment_decode F,
        MinimalDfaTasteGate_single_carrier_alignment_decode A,
        MinimalDfaTasteGate_single_carrier_alignment_decode alpha,
        MinimalDfaTasteGate_single_carrier_alignment_decode eta,
        MinimalDfaTasteGate_single_carrier_alignment_decode kappa,
        MinimalDfaTasteGate_single_carrier_alignment_decode H,
        MinimalDfaTasteGate_single_carrier_alignment_decode R,
        MinimalDfaTasteGate_single_carrier_alignment_decode P,
        MinimalDfaTasteGate_single_carrier_alignment_decode N]

private theorem MinimalDfaTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : MinimalDfaUp} :
    minimalDfaToEventFlow x = minimalDfaToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      minimalDfaFromEventFlow (minimalDfaToEventFlow x) =
        minimalDfaFromEventFlow (minimalDfaToEventFlow y) :=
    congrArg minimalDfaFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (MinimalDfaTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (MinimalDfaTasteGate_single_carrier_alignment_round_trip y)))

instance minimalDfaBHistCarrier : BHistCarrier MinimalDfaUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := minimalDfaToEventFlow
  fromEventFlow := minimalDfaFromEventFlow

instance minimalDfaChapterTasteGate : ChapterTasteGate MinimalDfaUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change minimalDfaFromEventFlow (minimalDfaToEventFlow x) = some x
    exact MinimalDfaTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (MinimalDfaTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate MinimalDfaUp :=
  -- BEDC touchpoint anchor: BHist BMark
  minimalDfaChapterTasteGate

theorem MinimalDfaTasteGate_single_carrier_alignment :
    (forall h : BHist, minimalDfaDecodeBHist (minimalDfaEncodeBHist h) = h) ∧
      (forall x : MinimalDfaUp, minimalDfaFromEventFlow (minimalDfaToEventFlow x) = some x) ∧
        (forall x y : MinimalDfaUp, minimalDfaToEventFlow x = minimalDfaToEventFlow y -> x = y) ∧
          minimalDfaEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact MinimalDfaTasteGate_single_carrier_alignment_decode
  constructor
  · exact MinimalDfaTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact MinimalDfaTasteGate_single_carrier_alignment_toEventFlow_injective heq
  · rfl

end BEDC.Derived.MinimalDfaUp
