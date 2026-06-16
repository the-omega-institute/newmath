import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyLatticeOperationsUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyLatticeOperationsUp : Type where
  | mk (x y t d m a r e h c p n : BHist) : RegularCauchyLatticeOperationsUp
  deriving DecidableEq

def regularCauchyLatticeOperationsEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyLatticeOperationsEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyLatticeOperationsEncodeBHist h

def regularCauchyLatticeOperationsDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyLatticeOperationsDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyLatticeOperationsDecodeBHist tail)

private theorem regularCauchyLatticeOperations_decode_encode_bhist :
    forall h : BHist,
      regularCauchyLatticeOperationsDecodeBHist
          (regularCauchyLatticeOperationsEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def regularCauchyLatticeOperationsToEventFlow :
    RegularCauchyLatticeOperationsUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyLatticeOperationsUp.mk x y t d m a r e h c p n =>
      [[BMark.b0],
        regularCauchyLatticeOperationsEncodeBHist x,
        [BMark.b1, BMark.b0],
        regularCauchyLatticeOperationsEncodeBHist y,
        [BMark.b1, BMark.b1, BMark.b0],
        regularCauchyLatticeOperationsEncodeBHist t,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyLatticeOperationsEncodeBHist d,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyLatticeOperationsEncodeBHist m,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyLatticeOperationsEncodeBHist a,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyLatticeOperationsEncodeBHist r,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        regularCauchyLatticeOperationsEncodeBHist e,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        regularCauchyLatticeOperationsEncodeBHist h,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        regularCauchyLatticeOperationsEncodeBHist c,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyLatticeOperationsEncodeBHist p,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyLatticeOperationsEncodeBHist n]

private def regularCauchyLatticeOperationsEventAtDefault :
    Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      regularCauchyLatticeOperationsEventAtDefault index rest

def regularCauchyLatticeOperationsFromEventFlow
    (ef : EventFlow) : Option RegularCauchyLatticeOperationsUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyLatticeOperationsUp.mk
      (regularCauchyLatticeOperationsDecodeBHist
        (regularCauchyLatticeOperationsEventAtDefault 1 ef))
      (regularCauchyLatticeOperationsDecodeBHist
        (regularCauchyLatticeOperationsEventAtDefault 3 ef))
      (regularCauchyLatticeOperationsDecodeBHist
        (regularCauchyLatticeOperationsEventAtDefault 5 ef))
      (regularCauchyLatticeOperationsDecodeBHist
        (regularCauchyLatticeOperationsEventAtDefault 7 ef))
      (regularCauchyLatticeOperationsDecodeBHist
        (regularCauchyLatticeOperationsEventAtDefault 9 ef))
      (regularCauchyLatticeOperationsDecodeBHist
        (regularCauchyLatticeOperationsEventAtDefault 11 ef))
      (regularCauchyLatticeOperationsDecodeBHist
        (regularCauchyLatticeOperationsEventAtDefault 13 ef))
      (regularCauchyLatticeOperationsDecodeBHist
        (regularCauchyLatticeOperationsEventAtDefault 15 ef))
      (regularCauchyLatticeOperationsDecodeBHist
        (regularCauchyLatticeOperationsEventAtDefault 17 ef))
      (regularCauchyLatticeOperationsDecodeBHist
        (regularCauchyLatticeOperationsEventAtDefault 19 ef))
      (regularCauchyLatticeOperationsDecodeBHist
        (regularCauchyLatticeOperationsEventAtDefault 21 ef))
      (regularCauchyLatticeOperationsDecodeBHist
        (regularCauchyLatticeOperationsEventAtDefault 23 ef)))

private theorem regularCauchyLatticeOperations_round_trip :
    forall x : RegularCauchyLatticeOperationsUp,
      regularCauchyLatticeOperationsFromEventFlow
          (regularCauchyLatticeOperationsToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk x y t d m a r e h c p n =>
      change
        some
          (RegularCauchyLatticeOperationsUp.mk
            (regularCauchyLatticeOperationsDecodeBHist
              (regularCauchyLatticeOperationsEncodeBHist x))
            (regularCauchyLatticeOperationsDecodeBHist
              (regularCauchyLatticeOperationsEncodeBHist y))
            (regularCauchyLatticeOperationsDecodeBHist
              (regularCauchyLatticeOperationsEncodeBHist t))
            (regularCauchyLatticeOperationsDecodeBHist
              (regularCauchyLatticeOperationsEncodeBHist d))
            (regularCauchyLatticeOperationsDecodeBHist
              (regularCauchyLatticeOperationsEncodeBHist m))
            (regularCauchyLatticeOperationsDecodeBHist
              (regularCauchyLatticeOperationsEncodeBHist a))
            (regularCauchyLatticeOperationsDecodeBHist
              (regularCauchyLatticeOperationsEncodeBHist r))
            (regularCauchyLatticeOperationsDecodeBHist
              (regularCauchyLatticeOperationsEncodeBHist e))
            (regularCauchyLatticeOperationsDecodeBHist
              (regularCauchyLatticeOperationsEncodeBHist h))
            (regularCauchyLatticeOperationsDecodeBHist
              (regularCauchyLatticeOperationsEncodeBHist c))
            (regularCauchyLatticeOperationsDecodeBHist
              (regularCauchyLatticeOperationsEncodeBHist p))
            (regularCauchyLatticeOperationsDecodeBHist
              (regularCauchyLatticeOperationsEncodeBHist n))) =
          some (RegularCauchyLatticeOperationsUp.mk x y t d m a r e h c p n)
      rw [regularCauchyLatticeOperations_decode_encode_bhist x,
        regularCauchyLatticeOperations_decode_encode_bhist y,
        regularCauchyLatticeOperations_decode_encode_bhist t,
        regularCauchyLatticeOperations_decode_encode_bhist d,
        regularCauchyLatticeOperations_decode_encode_bhist m,
        regularCauchyLatticeOperations_decode_encode_bhist a,
        regularCauchyLatticeOperations_decode_encode_bhist r,
        regularCauchyLatticeOperations_decode_encode_bhist e,
        regularCauchyLatticeOperations_decode_encode_bhist h,
        regularCauchyLatticeOperations_decode_encode_bhist c,
        regularCauchyLatticeOperations_decode_encode_bhist p,
        regularCauchyLatticeOperations_decode_encode_bhist n]

private theorem regularCauchyLatticeOperationsToEventFlow_injective
    {x y : RegularCauchyLatticeOperationsUp} :
    regularCauchyLatticeOperationsToEventFlow x =
        regularCauchyLatticeOperationsToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyLatticeOperationsFromEventFlow
          (regularCauchyLatticeOperationsToEventFlow x) =
        regularCauchyLatticeOperationsFromEventFlow
          (regularCauchyLatticeOperationsToEventFlow y) :=
    congrArg regularCauchyLatticeOperationsFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyLatticeOperations_round_trip x).symm
      (Eq.trans hread (regularCauchyLatticeOperations_round_trip y)))

instance regularCauchyLatticeOperationsBHistCarrier :
    BHistCarrier RegularCauchyLatticeOperationsUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyLatticeOperationsToEventFlow
  fromEventFlow := regularCauchyLatticeOperationsFromEventFlow

instance regularCauchyLatticeOperationsChapterTasteGate :
    ChapterTasteGate RegularCauchyLatticeOperationsUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyLatticeOperationsFromEventFlow
          (regularCauchyLatticeOperationsToEventFlow x) =
        some x
    exact regularCauchyLatticeOperations_round_trip x
  layer_separation := by
    intro _x _y hxy heq
    exact hxy (regularCauchyLatticeOperationsToEventFlow_injective heq)

theorem RegularCauchyLatticeOperationsTasteGate_single_carrier_alignment :
    (forall h : BHist,
      regularCauchyLatticeOperationsDecodeBHist
          (regularCauchyLatticeOperationsEncodeBHist h) =
        h) ∧
      Nonempty (BHistCarrier RegularCauchyLatticeOperationsUp) ∧
        Nonempty (ChapterTasteGate RegularCauchyLatticeOperationsUp) ∧
          regularCauchyLatticeOperationsEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨regularCauchyLatticeOperations_decode_encode_bhist,
      Nonempty.intro regularCauchyLatticeOperationsBHistCarrier,
      Nonempty.intro regularCauchyLatticeOperationsChapterTasteGate,
      rfl⟩

end BEDC.Derived.RegularCauchyLatticeOperationsUp
