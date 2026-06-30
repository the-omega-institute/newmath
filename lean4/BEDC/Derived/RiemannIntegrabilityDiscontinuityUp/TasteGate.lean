import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RiemannIntegrabilityDiscontinuityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RiemannIntegrabilityDiscontinuityUp : Type where
  | mk (I F L C U V G R E H Q P N : BHist) : RiemannIntegrabilityDiscontinuityUp
  deriving DecidableEq

def riemannIntegrabilityDiscontinuityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: riemannIntegrabilityDiscontinuityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: riemannIntegrabilityDiscontinuityEncodeBHist h

def riemannIntegrabilityDiscontinuityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (riemannIntegrabilityDiscontinuityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (riemannIntegrabilityDiscontinuityDecodeBHist tail)

private theorem RiemannIntegrabilityDiscontinuityTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      riemannIntegrabilityDiscontinuityDecodeBHist
        (riemannIntegrabilityDiscontinuityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def riemannIntegrabilityDiscontinuityFields :
    RiemannIntegrabilityDiscontinuityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RiemannIntegrabilityDiscontinuityUp.mk I F L C U V G R E H Q P N =>
      [I, F, L, C, U, V, G, R, E, H, Q, P, N]

def riemannIntegrabilityDiscontinuityToEventFlow :
    RiemannIntegrabilityDiscontinuityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (riemannIntegrabilityDiscontinuityFields x).map
      riemannIntegrabilityDiscontinuityEncodeBHist

private def riemannIntegrabilityDiscontinuityEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      riemannIntegrabilityDiscontinuityEventAtDefault index rest

def riemannIntegrabilityDiscontinuityFromEventFlow
    (ef : EventFlow) : Option RiemannIntegrabilityDiscontinuityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RiemannIntegrabilityDiscontinuityUp.mk
      (riemannIntegrabilityDiscontinuityDecodeBHist
        (riemannIntegrabilityDiscontinuityEventAtDefault 0 ef))
      (riemannIntegrabilityDiscontinuityDecodeBHist
        (riemannIntegrabilityDiscontinuityEventAtDefault 1 ef))
      (riemannIntegrabilityDiscontinuityDecodeBHist
        (riemannIntegrabilityDiscontinuityEventAtDefault 2 ef))
      (riemannIntegrabilityDiscontinuityDecodeBHist
        (riemannIntegrabilityDiscontinuityEventAtDefault 3 ef))
      (riemannIntegrabilityDiscontinuityDecodeBHist
        (riemannIntegrabilityDiscontinuityEventAtDefault 4 ef))
      (riemannIntegrabilityDiscontinuityDecodeBHist
        (riemannIntegrabilityDiscontinuityEventAtDefault 5 ef))
      (riemannIntegrabilityDiscontinuityDecodeBHist
        (riemannIntegrabilityDiscontinuityEventAtDefault 6 ef))
      (riemannIntegrabilityDiscontinuityDecodeBHist
        (riemannIntegrabilityDiscontinuityEventAtDefault 7 ef))
      (riemannIntegrabilityDiscontinuityDecodeBHist
        (riemannIntegrabilityDiscontinuityEventAtDefault 8 ef))
      (riemannIntegrabilityDiscontinuityDecodeBHist
        (riemannIntegrabilityDiscontinuityEventAtDefault 9 ef))
      (riemannIntegrabilityDiscontinuityDecodeBHist
        (riemannIntegrabilityDiscontinuityEventAtDefault 10 ef))
      (riemannIntegrabilityDiscontinuityDecodeBHist
        (riemannIntegrabilityDiscontinuityEventAtDefault 11 ef))
      (riemannIntegrabilityDiscontinuityDecodeBHist
        (riemannIntegrabilityDiscontinuityEventAtDefault 12 ef)))

private theorem RiemannIntegrabilityDiscontinuityTasteGate_single_carrier_alignment_round_trip
    (x : RiemannIntegrabilityDiscontinuityUp) :
    riemannIntegrabilityDiscontinuityFromEventFlow
      (riemannIntegrabilityDiscontinuityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk I F L C U V G R E H Q P N =>
      change
        some
          (RiemannIntegrabilityDiscontinuityUp.mk
            (riemannIntegrabilityDiscontinuityDecodeBHist
              (riemannIntegrabilityDiscontinuityEncodeBHist I))
            (riemannIntegrabilityDiscontinuityDecodeBHist
              (riemannIntegrabilityDiscontinuityEncodeBHist F))
            (riemannIntegrabilityDiscontinuityDecodeBHist
              (riemannIntegrabilityDiscontinuityEncodeBHist L))
            (riemannIntegrabilityDiscontinuityDecodeBHist
              (riemannIntegrabilityDiscontinuityEncodeBHist C))
            (riemannIntegrabilityDiscontinuityDecodeBHist
              (riemannIntegrabilityDiscontinuityEncodeBHist U))
            (riemannIntegrabilityDiscontinuityDecodeBHist
              (riemannIntegrabilityDiscontinuityEncodeBHist V))
            (riemannIntegrabilityDiscontinuityDecodeBHist
              (riemannIntegrabilityDiscontinuityEncodeBHist G))
            (riemannIntegrabilityDiscontinuityDecodeBHist
              (riemannIntegrabilityDiscontinuityEncodeBHist R))
            (riemannIntegrabilityDiscontinuityDecodeBHist
              (riemannIntegrabilityDiscontinuityEncodeBHist E))
            (riemannIntegrabilityDiscontinuityDecodeBHist
              (riemannIntegrabilityDiscontinuityEncodeBHist H))
            (riemannIntegrabilityDiscontinuityDecodeBHist
              (riemannIntegrabilityDiscontinuityEncodeBHist Q))
            (riemannIntegrabilityDiscontinuityDecodeBHist
              (riemannIntegrabilityDiscontinuityEncodeBHist P))
            (riemannIntegrabilityDiscontinuityDecodeBHist
              (riemannIntegrabilityDiscontinuityEncodeBHist N))) =
          some (RiemannIntegrabilityDiscontinuityUp.mk I F L C U V G R E H Q P N)
      rw
        [RiemannIntegrabilityDiscontinuityTasteGate_single_carrier_alignment_decode_encode I,
          RiemannIntegrabilityDiscontinuityTasteGate_single_carrier_alignment_decode_encode F,
          RiemannIntegrabilityDiscontinuityTasteGate_single_carrier_alignment_decode_encode L,
          RiemannIntegrabilityDiscontinuityTasteGate_single_carrier_alignment_decode_encode C,
          RiemannIntegrabilityDiscontinuityTasteGate_single_carrier_alignment_decode_encode U,
          RiemannIntegrabilityDiscontinuityTasteGate_single_carrier_alignment_decode_encode V,
          RiemannIntegrabilityDiscontinuityTasteGate_single_carrier_alignment_decode_encode G,
          RiemannIntegrabilityDiscontinuityTasteGate_single_carrier_alignment_decode_encode R,
          RiemannIntegrabilityDiscontinuityTasteGate_single_carrier_alignment_decode_encode E,
          RiemannIntegrabilityDiscontinuityTasteGate_single_carrier_alignment_decode_encode H,
          RiemannIntegrabilityDiscontinuityTasteGate_single_carrier_alignment_decode_encode Q,
          RiemannIntegrabilityDiscontinuityTasteGate_single_carrier_alignment_decode_encode P,
          RiemannIntegrabilityDiscontinuityTasteGate_single_carrier_alignment_decode_encode N]

private theorem RiemannIntegrabilityDiscontinuityTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RiemannIntegrabilityDiscontinuityUp} :
    riemannIntegrabilityDiscontinuityToEventFlow x =
      riemannIntegrabilityDiscontinuityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      riemannIntegrabilityDiscontinuityFromEventFlow
          (riemannIntegrabilityDiscontinuityToEventFlow x) =
        riemannIntegrabilityDiscontinuityFromEventFlow
          (riemannIntegrabilityDiscontinuityToEventFlow y) :=
    congrArg riemannIntegrabilityDiscontinuityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RiemannIntegrabilityDiscontinuityTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RiemannIntegrabilityDiscontinuityTasteGate_single_carrier_alignment_round_trip y)))

instance riemannIntegrabilityDiscontinuityBHistCarrier :
    BHistCarrier RiemannIntegrabilityDiscontinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := riemannIntegrabilityDiscontinuityToEventFlow
  fromEventFlow := riemannIntegrabilityDiscontinuityFromEventFlow

instance riemannIntegrabilityDiscontinuityChapterTasteGate :
    ChapterTasteGate RiemannIntegrabilityDiscontinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      riemannIntegrabilityDiscontinuityFromEventFlow
        (riemannIntegrabilityDiscontinuityToEventFlow x) = some x
    exact RiemannIntegrabilityDiscontinuityTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RiemannIntegrabilityDiscontinuityTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

theorem RiemannIntegrabilityDiscontinuityTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      riemannIntegrabilityDiscontinuityDecodeBHist
        (riemannIntegrabilityDiscontinuityEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier RiemannIntegrabilityDiscontinuityUp) ∧
        Nonempty (ChapterTasteGate RiemannIntegrabilityDiscontinuityUp) ∧
          riemannIntegrabilityDiscontinuityEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨RiemannIntegrabilityDiscontinuityTasteGate_single_carrier_alignment_decode_encode,
      ⟨riemannIntegrabilityDiscontinuityBHistCarrier⟩,
      ⟨riemannIntegrabilityDiscontinuityChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.RiemannIntegrabilityDiscontinuityUp
