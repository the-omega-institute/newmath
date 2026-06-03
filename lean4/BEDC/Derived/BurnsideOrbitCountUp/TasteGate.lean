import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BurnsideOrbitCountUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BurnsideOrbitCountUp : Type where
  | mk (G X A F O M H C P N : BHist) : BurnsideOrbitCountUp
  deriving DecidableEq

def burnsideOrbitCountEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: burnsideOrbitCountEncodeBHist h
  | BHist.e1 h => BMark.b1 :: burnsideOrbitCountEncodeBHist h

def burnsideOrbitCountDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (burnsideOrbitCountDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (burnsideOrbitCountDecodeBHist tail)

private theorem burnsideOrbitCount_decode_encode_bhist :
    ∀ h : BHist, burnsideOrbitCountDecodeBHist (burnsideOrbitCountEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def burnsideOrbitCountFields : BurnsideOrbitCountUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BurnsideOrbitCountUp.mk G X A F O M H C P N => [G, X, A, F, O, M, H, C, P, N]

def burnsideOrbitCountToEventFlow : BurnsideOrbitCountUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (burnsideOrbitCountFields x).map burnsideOrbitCountEncodeBHist

private def burnsideOrbitCountEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => burnsideOrbitCountEventAtDefault index rest

def burnsideOrbitCountFromEventFlow (ef : EventFlow) : Option BurnsideOrbitCountUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BurnsideOrbitCountUp.mk
      (burnsideOrbitCountDecodeBHist (burnsideOrbitCountEventAtDefault 0 ef))
      (burnsideOrbitCountDecodeBHist (burnsideOrbitCountEventAtDefault 1 ef))
      (burnsideOrbitCountDecodeBHist (burnsideOrbitCountEventAtDefault 2 ef))
      (burnsideOrbitCountDecodeBHist (burnsideOrbitCountEventAtDefault 3 ef))
      (burnsideOrbitCountDecodeBHist (burnsideOrbitCountEventAtDefault 4 ef))
      (burnsideOrbitCountDecodeBHist (burnsideOrbitCountEventAtDefault 5 ef))
      (burnsideOrbitCountDecodeBHist (burnsideOrbitCountEventAtDefault 6 ef))
      (burnsideOrbitCountDecodeBHist (burnsideOrbitCountEventAtDefault 7 ef))
      (burnsideOrbitCountDecodeBHist (burnsideOrbitCountEventAtDefault 8 ef))
      (burnsideOrbitCountDecodeBHist (burnsideOrbitCountEventAtDefault 9 ef)))

private theorem burnsideOrbitCount_round_trip :
    ∀ x : BurnsideOrbitCountUp,
      burnsideOrbitCountFromEventFlow (burnsideOrbitCountToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk G X A F O M H C P N =>
      change
        some
          (BurnsideOrbitCountUp.mk
            (burnsideOrbitCountDecodeBHist (burnsideOrbitCountEncodeBHist G))
            (burnsideOrbitCountDecodeBHist (burnsideOrbitCountEncodeBHist X))
            (burnsideOrbitCountDecodeBHist (burnsideOrbitCountEncodeBHist A))
            (burnsideOrbitCountDecodeBHist (burnsideOrbitCountEncodeBHist F))
            (burnsideOrbitCountDecodeBHist (burnsideOrbitCountEncodeBHist O))
            (burnsideOrbitCountDecodeBHist (burnsideOrbitCountEncodeBHist M))
            (burnsideOrbitCountDecodeBHist (burnsideOrbitCountEncodeBHist H))
            (burnsideOrbitCountDecodeBHist (burnsideOrbitCountEncodeBHist C))
            (burnsideOrbitCountDecodeBHist (burnsideOrbitCountEncodeBHist P))
            (burnsideOrbitCountDecodeBHist (burnsideOrbitCountEncodeBHist N))) =
          some (BurnsideOrbitCountUp.mk G X A F O M H C P N)
      rw [burnsideOrbitCount_decode_encode_bhist G, burnsideOrbitCount_decode_encode_bhist X,
        burnsideOrbitCount_decode_encode_bhist A, burnsideOrbitCount_decode_encode_bhist F,
        burnsideOrbitCount_decode_encode_bhist O, burnsideOrbitCount_decode_encode_bhist M,
        burnsideOrbitCount_decode_encode_bhist H, burnsideOrbitCount_decode_encode_bhist C,
        burnsideOrbitCount_decode_encode_bhist P, burnsideOrbitCount_decode_encode_bhist N]

private theorem burnsideOrbitCountToEventFlow_injective {x y : BurnsideOrbitCountUp} :
    burnsideOrbitCountToEventFlow x = burnsideOrbitCountToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      burnsideOrbitCountFromEventFlow (burnsideOrbitCountToEventFlow x) =
        burnsideOrbitCountFromEventFlow (burnsideOrbitCountToEventFlow y) :=
    congrArg burnsideOrbitCountFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (burnsideOrbitCount_round_trip x).symm
      (Eq.trans hread (burnsideOrbitCount_round_trip y)))

instance burnsideOrbitCountBHistCarrier : BHistCarrier BurnsideOrbitCountUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := burnsideOrbitCountToEventFlow
  fromEventFlow := burnsideOrbitCountFromEventFlow

instance burnsideOrbitCountChapterTasteGate : ChapterTasteGate BurnsideOrbitCountUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change burnsideOrbitCountFromEventFlow (burnsideOrbitCountToEventFlow x) = some x
    exact burnsideOrbitCount_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (burnsideOrbitCountToEventFlow_injective heq)

theorem BurnsideOrbitCountTasteGate_single_carrier_alignment :
    (∀ h : BHist, burnsideOrbitCountDecodeBHist (burnsideOrbitCountEncodeBHist h) = h) ∧
      (∀ x : BurnsideOrbitCountUp,
        burnsideOrbitCountFromEventFlow (burnsideOrbitCountToEventFlow x) = some x) ∧
        (∀ x y : BurnsideOrbitCountUp,
          burnsideOrbitCountToEventFlow x = burnsideOrbitCountToEventFlow y → x = y) ∧
          burnsideOrbitCountEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨burnsideOrbitCount_decode_encode_bhist,
      burnsideOrbitCount_round_trip,
      (fun _ _ heq => burnsideOrbitCountToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.BurnsideOrbitCountUp
