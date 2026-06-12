import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FormalBallBasisUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FormalBallBasisUp : Type where
  | mk (X d c r I R H C P N : BHist) : FormalBallBasisUp
  deriving DecidableEq

def formalBallBasisEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: formalBallBasisEncodeBHist h
  | BHist.e1 h => BMark.b1 :: formalBallBasisEncodeBHist h

def formalBallBasisDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (formalBallBasisDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (formalBallBasisDecodeBHist tail)

private theorem formalBallBasis_decode_encode_bhist :
    ∀ h : BHist, formalBallBasisDecodeBHist (formalBallBasisEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def formalBallBasisToEventFlow : FormalBallBasisUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FormalBallBasisUp.mk X d c r I R H C P N =>
      [formalBallBasisEncodeBHist X,
        formalBallBasisEncodeBHist d,
        formalBallBasisEncodeBHist c,
        formalBallBasisEncodeBHist r,
        formalBallBasisEncodeBHist I,
        formalBallBasisEncodeBHist R,
        formalBallBasisEncodeBHist H,
        formalBallBasisEncodeBHist C,
        formalBallBasisEncodeBHist P,
        formalBallBasisEncodeBHist N]

private def formalBallBasisEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => formalBallBasisEventAtDefault index rest

def formalBallBasisFromEventFlow (ef : EventFlow) : Option FormalBallBasisUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FormalBallBasisUp.mk
      (formalBallBasisDecodeBHist (formalBallBasisEventAtDefault 0 ef))
      (formalBallBasisDecodeBHist (formalBallBasisEventAtDefault 1 ef))
      (formalBallBasisDecodeBHist (formalBallBasisEventAtDefault 2 ef))
      (formalBallBasisDecodeBHist (formalBallBasisEventAtDefault 3 ef))
      (formalBallBasisDecodeBHist (formalBallBasisEventAtDefault 4 ef))
      (formalBallBasisDecodeBHist (formalBallBasisEventAtDefault 5 ef))
      (formalBallBasisDecodeBHist (formalBallBasisEventAtDefault 6 ef))
      (formalBallBasisDecodeBHist (formalBallBasisEventAtDefault 7 ef))
      (formalBallBasisDecodeBHist (formalBallBasisEventAtDefault 8 ef))
      (formalBallBasisDecodeBHist (formalBallBasisEventAtDefault 9 ef)))

private theorem formalBallBasis_round_trip :
    ∀ x : FormalBallBasisUp,
      formalBallBasisFromEventFlow (formalBallBasisToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X d c r I R H C P N =>
      change
        some
            (FormalBallBasisUp.mk
              (formalBallBasisDecodeBHist (formalBallBasisEncodeBHist X))
              (formalBallBasisDecodeBHist (formalBallBasisEncodeBHist d))
              (formalBallBasisDecodeBHist (formalBallBasisEncodeBHist c))
              (formalBallBasisDecodeBHist (formalBallBasisEncodeBHist r))
              (formalBallBasisDecodeBHist (formalBallBasisEncodeBHist I))
              (formalBallBasisDecodeBHist (formalBallBasisEncodeBHist R))
              (formalBallBasisDecodeBHist (formalBallBasisEncodeBHist H))
              (formalBallBasisDecodeBHist (formalBallBasisEncodeBHist C))
              (formalBallBasisDecodeBHist (formalBallBasisEncodeBHist P))
              (formalBallBasisDecodeBHist (formalBallBasisEncodeBHist N))) =
          some (FormalBallBasisUp.mk X d c r I R H C P N)
      rw [formalBallBasis_decode_encode_bhist X,
        formalBallBasis_decode_encode_bhist d,
        formalBallBasis_decode_encode_bhist c,
        formalBallBasis_decode_encode_bhist r,
        formalBallBasis_decode_encode_bhist I,
        formalBallBasis_decode_encode_bhist R,
        formalBallBasis_decode_encode_bhist H,
        formalBallBasis_decode_encode_bhist C,
        formalBallBasis_decode_encode_bhist P,
        formalBallBasis_decode_encode_bhist N]

private theorem formalBallBasisToEventFlow_injective {x y : FormalBallBasisUp} :
    formalBallBasisToEventFlow x = formalBallBasisToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      formalBallBasisFromEventFlow (formalBallBasisToEventFlow x) =
        formalBallBasisFromEventFlow (formalBallBasisToEventFlow y) :=
    congrArg formalBallBasisFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (formalBallBasis_round_trip x).symm
      (Eq.trans hread (formalBallBasis_round_trip y)))

instance formalBallBasisBHistCarrier : BHistCarrier FormalBallBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := formalBallBasisToEventFlow
  fromEventFlow := formalBallBasisFromEventFlow

instance formalBallBasisChapterTasteGate : ChapterTasteGate FormalBallBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change formalBallBasisFromEventFlow (formalBallBasisToEventFlow x) = some x
    exact formalBallBasis_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (formalBallBasisToEventFlow_injective heq)

def taste_gate : ChapterTasteGate FormalBallBasisUp :=
  -- BEDC touchpoint anchor: BHist BMark
  formalBallBasisChapterTasteGate

theorem FormalBallBasisTasteGate_single_carrier_alignment :
    formalBallBasisEncodeBHist BHist.Empty = ([] : List BMark) ∧
      (∀ h : BHist, formalBallBasisDecodeBHist (formalBallBasisEncodeBHist h) = h) ∧
      (∀ x : FormalBallBasisUp,
        formalBallBasisFromEventFlow (formalBallBasisToEventFlow x) = some x) ∧
      (∀ x y : FormalBallBasisUp,
        formalBallBasisToEventFlow x = formalBallBasisToEventFlow y → x = y) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨rfl,
      formalBallBasis_decode_encode_bhist,
      formalBallBasis_round_trip,
      fun _ _ heq => formalBallBasisToEventFlow_injective heq⟩

end BEDC.Derived.FormalBallBasisUp
