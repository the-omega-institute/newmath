import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ExtFunctorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ExtFunctorUp : Type where
  | mk (A X Y R H C Z B D T U P N : BHist) : ExtFunctorUp
  deriving DecidableEq

def extFunctorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: extFunctorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: extFunctorEncodeBHist h

def extFunctorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (extFunctorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (extFunctorDecodeBHist tail)

private theorem extFunctor_decode_encode_bhist :
    ∀ h : BHist, extFunctorDecodeBHist (extFunctorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def extFunctorFields : ExtFunctorUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ExtFunctorUp.mk A X Y R H C Z B D T U P N => [A, X, Y, R, H, C, Z, B, D, T, U, P, N]

def extFunctorToEventFlow : ExtFunctorUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (extFunctorFields x).map extFunctorEncodeBHist

private def extFunctorEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => extFunctorEventAt index rest

def extFunctorFromEventFlow (ef : EventFlow) : Option ExtFunctorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ExtFunctorUp.mk
      (extFunctorDecodeBHist (extFunctorEventAt 0 ef))
      (extFunctorDecodeBHist (extFunctorEventAt 1 ef))
      (extFunctorDecodeBHist (extFunctorEventAt 2 ef))
      (extFunctorDecodeBHist (extFunctorEventAt 3 ef))
      (extFunctorDecodeBHist (extFunctorEventAt 4 ef))
      (extFunctorDecodeBHist (extFunctorEventAt 5 ef))
      (extFunctorDecodeBHist (extFunctorEventAt 6 ef))
      (extFunctorDecodeBHist (extFunctorEventAt 7 ef))
      (extFunctorDecodeBHist (extFunctorEventAt 8 ef))
      (extFunctorDecodeBHist (extFunctorEventAt 9 ef))
      (extFunctorDecodeBHist (extFunctorEventAt 10 ef))
      (extFunctorDecodeBHist (extFunctorEventAt 11 ef))
      (extFunctorDecodeBHist (extFunctorEventAt 12 ef)))

private theorem extFunctor_round_trip (x : ExtFunctorUp) :
    extFunctorFromEventFlow (extFunctorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk A X Y R H C Z B D T U P N =>
      change
        some
          (ExtFunctorUp.mk
            (extFunctorDecodeBHist (extFunctorEncodeBHist A))
            (extFunctorDecodeBHist (extFunctorEncodeBHist X))
            (extFunctorDecodeBHist (extFunctorEncodeBHist Y))
            (extFunctorDecodeBHist (extFunctorEncodeBHist R))
            (extFunctorDecodeBHist (extFunctorEncodeBHist H))
            (extFunctorDecodeBHist (extFunctorEncodeBHist C))
            (extFunctorDecodeBHist (extFunctorEncodeBHist Z))
            (extFunctorDecodeBHist (extFunctorEncodeBHist B))
            (extFunctorDecodeBHist (extFunctorEncodeBHist D))
            (extFunctorDecodeBHist (extFunctorEncodeBHist T))
            (extFunctorDecodeBHist (extFunctorEncodeBHist U))
            (extFunctorDecodeBHist (extFunctorEncodeBHist P))
            (extFunctorDecodeBHist (extFunctorEncodeBHist N))) =
          some (ExtFunctorUp.mk A X Y R H C Z B D T U P N)
      rw [extFunctor_decode_encode_bhist A, extFunctor_decode_encode_bhist X,
        extFunctor_decode_encode_bhist Y, extFunctor_decode_encode_bhist R,
        extFunctor_decode_encode_bhist H, extFunctor_decode_encode_bhist C,
        extFunctor_decode_encode_bhist Z, extFunctor_decode_encode_bhist B,
        extFunctor_decode_encode_bhist D, extFunctor_decode_encode_bhist T,
        extFunctor_decode_encode_bhist U, extFunctor_decode_encode_bhist P,
        extFunctor_decode_encode_bhist N]

private theorem extFunctorToEventFlow_injective {x y : ExtFunctorUp} :
    extFunctorToEventFlow x = extFunctorToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      extFunctorFromEventFlow (extFunctorToEventFlow x) =
        extFunctorFromEventFlow (extFunctorToEventFlow y) :=
    congrArg extFunctorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (extFunctor_round_trip x).symm
      (Eq.trans hread (extFunctor_round_trip y)))

instance extFunctorBHistCarrier : BHistCarrier ExtFunctorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := extFunctorToEventFlow
  fromEventFlow := extFunctorFromEventFlow

instance extFunctorChapterTasteGate : ChapterTasteGate ExtFunctorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change extFunctorFromEventFlow (extFunctorToEventFlow x) = some x
    exact extFunctor_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (extFunctorToEventFlow_injective heq)

theorem ExtFunctorTasteGate_single_carrier_alignment :
    (∀ h : BHist, extFunctorDecodeBHist (extFunctorEncodeBHist h) = h) ∧
      (∀ x : ExtFunctorUp, extFunctorFromEventFlow (extFunctorToEventFlow x) = some x) ∧
        (∀ x y : ExtFunctorUp, extFunctorToEventFlow x = extFunctorToEventFlow y → x = y) ∧
          extFunctorEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact extFunctor_decode_encode_bhist
  · constructor
    · exact extFunctor_round_trip
    · constructor
      · intro x y heq
        exact extFunctorToEventFlow_injective heq
      · rfl

end BEDC.Derived.ExtFunctorUp
