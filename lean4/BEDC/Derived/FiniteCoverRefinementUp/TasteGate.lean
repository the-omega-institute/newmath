import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteCoverRefinementUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteCoverRefinementUp : Type where
  | mk (K D F Q U W H C P N : BHist) : FiniteCoverRefinementUp
  deriving DecidableEq

def finiteCoverRefinementEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteCoverRefinementEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteCoverRefinementEncodeBHist h

def finiteCoverRefinementDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteCoverRefinementDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteCoverRefinementDecodeBHist tail)

private theorem finiteCoverRefinementDecode_encode_bhist :
    ∀ h : BHist,
      finiteCoverRefinementDecodeBHist (finiteCoverRefinementEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteCoverRefinementFields : FiniteCoverRefinementUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteCoverRefinementUp.mk K D F Q U W H C P N => [K, D, F, Q, U, W, H, C, P, N]

def finiteCoverRefinementToEventFlow : FiniteCoverRefinementUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (finiteCoverRefinementFields x).map finiteCoverRefinementEncodeBHist

private def finiteCoverRefinementEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => finiteCoverRefinementEventAtDefault index rest

def finiteCoverRefinementFromEventFlow : EventFlow → Option FiniteCoverRefinementUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (FiniteCoverRefinementUp.mk
        (finiteCoverRefinementDecodeBHist (finiteCoverRefinementEventAtDefault 0 ef))
        (finiteCoverRefinementDecodeBHist (finiteCoverRefinementEventAtDefault 1 ef))
        (finiteCoverRefinementDecodeBHist (finiteCoverRefinementEventAtDefault 2 ef))
        (finiteCoverRefinementDecodeBHist (finiteCoverRefinementEventAtDefault 3 ef))
        (finiteCoverRefinementDecodeBHist (finiteCoverRefinementEventAtDefault 4 ef))
        (finiteCoverRefinementDecodeBHist (finiteCoverRefinementEventAtDefault 5 ef))
        (finiteCoverRefinementDecodeBHist (finiteCoverRefinementEventAtDefault 6 ef))
        (finiteCoverRefinementDecodeBHist (finiteCoverRefinementEventAtDefault 7 ef))
        (finiteCoverRefinementDecodeBHist (finiteCoverRefinementEventAtDefault 8 ef))
        (finiteCoverRefinementDecodeBHist (finiteCoverRefinementEventAtDefault 9 ef)))

private theorem finiteCoverRefinement_round_trip :
    ∀ x : FiniteCoverRefinementUp,
      finiteCoverRefinementFromEventFlow (finiteCoverRefinementToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K D F Q U W H C P N =>
      change
        some
          (FiniteCoverRefinementUp.mk
            (finiteCoverRefinementDecodeBHist (finiteCoverRefinementEncodeBHist K))
            (finiteCoverRefinementDecodeBHist (finiteCoverRefinementEncodeBHist D))
            (finiteCoverRefinementDecodeBHist (finiteCoverRefinementEncodeBHist F))
            (finiteCoverRefinementDecodeBHist (finiteCoverRefinementEncodeBHist Q))
            (finiteCoverRefinementDecodeBHist (finiteCoverRefinementEncodeBHist U))
            (finiteCoverRefinementDecodeBHist (finiteCoverRefinementEncodeBHist W))
            (finiteCoverRefinementDecodeBHist (finiteCoverRefinementEncodeBHist H))
            (finiteCoverRefinementDecodeBHist (finiteCoverRefinementEncodeBHist C))
            (finiteCoverRefinementDecodeBHist (finiteCoverRefinementEncodeBHist P))
            (finiteCoverRefinementDecodeBHist (finiteCoverRefinementEncodeBHist N))) =
          some (FiniteCoverRefinementUp.mk K D F Q U W H C P N)
      rw [finiteCoverRefinementDecode_encode_bhist K, finiteCoverRefinementDecode_encode_bhist D,
        finiteCoverRefinementDecode_encode_bhist F, finiteCoverRefinementDecode_encode_bhist Q,
        finiteCoverRefinementDecode_encode_bhist U, finiteCoverRefinementDecode_encode_bhist W,
        finiteCoverRefinementDecode_encode_bhist H, finiteCoverRefinementDecode_encode_bhist C,
        finiteCoverRefinementDecode_encode_bhist P, finiteCoverRefinementDecode_encode_bhist N]

private theorem finiteCoverRefinementToEventFlow_injective {x y : FiniteCoverRefinementUp} :
    finiteCoverRefinementToEventFlow x = finiteCoverRefinementToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteCoverRefinementFromEventFlow (finiteCoverRefinementToEventFlow x) =
        finiteCoverRefinementFromEventFlow (finiteCoverRefinementToEventFlow y) :=
    congrArg finiteCoverRefinementFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (finiteCoverRefinement_round_trip x).symm
      (Eq.trans hread (finiteCoverRefinement_round_trip y)))

instance finiteCoverRefinementBHistCarrier : BHistCarrier FiniteCoverRefinementUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteCoverRefinementToEventFlow
  fromEventFlow := finiteCoverRefinementFromEventFlow

instance finiteCoverRefinementChapterTasteGate : ChapterTasteGate FiniteCoverRefinementUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finiteCoverRefinementFromEventFlow (finiteCoverRefinementToEventFlow x) = some x
    exact finiteCoverRefinement_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finiteCoverRefinementToEventFlow_injective heq)

theorem FiniteCoverRefinementTasteGate_single_carrier_alignment :
    (forall h : BHist,
      finiteCoverRefinementDecodeBHist (finiteCoverRefinementEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier FiniteCoverRefinementUp) ∧
        Nonempty (ChapterTasteGate FiniteCoverRefinementUp) ∧
          finiteCoverRefinementEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact finiteCoverRefinementDecode_encode_bhist
  · constructor
    · exact Nonempty.intro finiteCoverRefinementBHistCarrier
    · constructor
      · exact Nonempty.intro finiteCoverRefinementChapterTasteGate
      · rfl

end BEDC.Derived.FiniteCoverRefinementUp
