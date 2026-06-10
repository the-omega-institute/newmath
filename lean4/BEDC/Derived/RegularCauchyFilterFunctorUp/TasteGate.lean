import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyFilterFunctorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyFilterFunctorUp : Type where
  | mk (I B W D R E A H C P N : BHist) : RegularCauchyFilterFunctorUp
  deriving DecidableEq

def regularCauchyFilterFunctorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyFilterFunctorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyFilterFunctorEncodeBHist h

def regularCauchyFilterFunctorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyFilterFunctorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyFilterFunctorDecodeBHist tail)

private theorem regularCauchyFilterFunctor_decode_encode :
    ∀ h : BHist,
      regularCauchyFilterFunctorDecodeBHist
          (regularCauchyFilterFunctorEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def regularCauchyFilterFunctorFields :
    RegularCauchyFilterFunctorUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyFilterFunctorUp.mk I B W D R E A H C P N =>
      [I, B, W, D, R, E, A, H, C, P, N]

def regularCauchyFilterFunctorToEventFlow :
    RegularCauchyFilterFunctorUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | token =>
      (regularCauchyFilterFunctorFields token).map
        regularCauchyFilterFunctorEncodeBHist

private def regularCauchyFilterFunctorRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _n, [] => []
  | Nat.succ n, _event :: rest => regularCauchyFilterFunctorRawAt n rest

private def regularCauchyFilterFunctorLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _event :: _rest => false
  | Nat.succ _n, [] => false
  | Nat.succ n, _event :: rest => regularCauchyFilterFunctorLengthEq n rest

def regularCauchyFilterFunctorFromEventFlow :
    EventFlow → Option RegularCauchyFilterFunctorUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match regularCauchyFilterFunctorLengthEq 11 flow with
      | true =>
          some
            (RegularCauchyFilterFunctorUp.mk
              (regularCauchyFilterFunctorDecodeBHist
                (regularCauchyFilterFunctorRawAt 0 flow))
              (regularCauchyFilterFunctorDecodeBHist
                (regularCauchyFilterFunctorRawAt 1 flow))
              (regularCauchyFilterFunctorDecodeBHist
                (regularCauchyFilterFunctorRawAt 2 flow))
              (regularCauchyFilterFunctorDecodeBHist
                (regularCauchyFilterFunctorRawAt 3 flow))
              (regularCauchyFilterFunctorDecodeBHist
                (regularCauchyFilterFunctorRawAt 4 flow))
              (regularCauchyFilterFunctorDecodeBHist
                (regularCauchyFilterFunctorRawAt 5 flow))
              (regularCauchyFilterFunctorDecodeBHist
                (regularCauchyFilterFunctorRawAt 6 flow))
              (regularCauchyFilterFunctorDecodeBHist
                (regularCauchyFilterFunctorRawAt 7 flow))
              (regularCauchyFilterFunctorDecodeBHist
                (regularCauchyFilterFunctorRawAt 8 flow))
              (regularCauchyFilterFunctorDecodeBHist
                (regularCauchyFilterFunctorRawAt 9 flow))
              (regularCauchyFilterFunctorDecodeBHist
                (regularCauchyFilterFunctorRawAt 10 flow)))
      | false => none

private theorem regularCauchyFilterFunctor_round_trip :
    ∀ x : RegularCauchyFilterFunctorUp,
      regularCauchyFilterFunctorFromEventFlow
          (regularCauchyFilterFunctorToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I B W D R E A H C P N =>
      change
        some
          (RegularCauchyFilterFunctorUp.mk
            (regularCauchyFilterFunctorDecodeBHist
              (regularCauchyFilterFunctorEncodeBHist I))
            (regularCauchyFilterFunctorDecodeBHist
              (regularCauchyFilterFunctorEncodeBHist B))
            (regularCauchyFilterFunctorDecodeBHist
              (regularCauchyFilterFunctorEncodeBHist W))
            (regularCauchyFilterFunctorDecodeBHist
              (regularCauchyFilterFunctorEncodeBHist D))
            (regularCauchyFilterFunctorDecodeBHist
              (regularCauchyFilterFunctorEncodeBHist R))
            (regularCauchyFilterFunctorDecodeBHist
              (regularCauchyFilterFunctorEncodeBHist E))
            (regularCauchyFilterFunctorDecodeBHist
              (regularCauchyFilterFunctorEncodeBHist A))
            (regularCauchyFilterFunctorDecodeBHist
              (regularCauchyFilterFunctorEncodeBHist H))
            (regularCauchyFilterFunctorDecodeBHist
              (regularCauchyFilterFunctorEncodeBHist C))
            (regularCauchyFilterFunctorDecodeBHist
              (regularCauchyFilterFunctorEncodeBHist P))
            (regularCauchyFilterFunctorDecodeBHist
              (regularCauchyFilterFunctorEncodeBHist N))) =
          some (RegularCauchyFilterFunctorUp.mk I B W D R E A H C P N)
      rw [regularCauchyFilterFunctor_decode_encode I,
        regularCauchyFilterFunctor_decode_encode B,
        regularCauchyFilterFunctor_decode_encode W,
        regularCauchyFilterFunctor_decode_encode D,
        regularCauchyFilterFunctor_decode_encode R,
        regularCauchyFilterFunctor_decode_encode E,
        regularCauchyFilterFunctor_decode_encode A,
        regularCauchyFilterFunctor_decode_encode H,
        regularCauchyFilterFunctor_decode_encode C,
        regularCauchyFilterFunctor_decode_encode P,
        regularCauchyFilterFunctor_decode_encode N]

private theorem regularCauchyFilterFunctorToEventFlow_injective
    {x y : RegularCauchyFilterFunctorUp} :
    regularCauchyFilterFunctorToEventFlow x =
        regularCauchyFilterFunctorToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyFilterFunctorFromEventFlow
          (regularCauchyFilterFunctorToEventFlow x) =
        regularCauchyFilterFunctorFromEventFlow
          (regularCauchyFilterFunctorToEventFlow y) :=
    congrArg regularCauchyFilterFunctorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyFilterFunctor_round_trip x).symm
      (Eq.trans hread (regularCauchyFilterFunctor_round_trip y)))

instance regularCauchyFilterFunctorBHistCarrier :
    BHistCarrier RegularCauchyFilterFunctorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyFilterFunctorToEventFlow
  fromEventFlow := regularCauchyFilterFunctorFromEventFlow

instance regularCauchyFilterFunctorChapterTasteGate :
    ChapterTasteGate RegularCauchyFilterFunctorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyFilterFunctorFromEventFlow
          (regularCauchyFilterFunctorToEventFlow x) =
        some x
    exact regularCauchyFilterFunctor_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyFilterFunctorToEventFlow_injective heq)

theorem RegularCauchyFilterFunctorTasteGate_single_carrier_alignment :
    (∃ carrier : BHistCarrier RegularCauchyFilterFunctorUp,
        Nonempty (@ChapterTasteGate RegularCauchyFilterFunctorUp carrier)) ∧
      (∀ h : BHist,
        regularCauchyFilterFunctorDecodeBHist
            (regularCauchyFilterFunctorEncodeBHist h) =
          h) ∧
      (∀ x : RegularCauchyFilterFunctorUp,
        regularCauchyFilterFunctorFromEventFlow
            (regularCauchyFilterFunctorToEventFlow x) =
          some x) ∧
      regularCauchyFilterFunctorEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨regularCauchyFilterFunctorBHistCarrier,
        ⟨regularCauchyFilterFunctorChapterTasteGate⟩⟩,
      regularCauchyFilterFunctor_decode_encode,
      regularCauchyFilterFunctor_round_trip,
      rfl⟩

end BEDC.Derived.RegularCauchyFilterFunctorUp
