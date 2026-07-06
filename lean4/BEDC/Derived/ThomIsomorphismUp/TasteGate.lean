import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ThomIsomorphismUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ThomIsomorphismUp : Type where
  | mk (B V O K U L A R H C P N : BHist) : ThomIsomorphismUp
  deriving DecidableEq

def thomIsomorphismEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: thomIsomorphismEncodeBHist h
  | BHist.e1 h => BMark.b1 :: thomIsomorphismEncodeBHist h

def thomIsomorphismDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (thomIsomorphismDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (thomIsomorphismDecodeBHist tail)

private theorem thomIsomorphism_decode_encode_bhist :
    ∀ h : BHist, thomIsomorphismDecodeBHist (thomIsomorphismEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def thomIsomorphismFields : ThomIsomorphismUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ThomIsomorphismUp.mk B V O K U L A R H C P N => [B, V, O, K, U, L, A, R, H, C, P, N]

def thomIsomorphismToEventFlow : ThomIsomorphismUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (thomIsomorphismFields x).map thomIsomorphismEncodeBHist

private def thomIsomorphismEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => thomIsomorphismEventAtDefault index rest

def thomIsomorphismFromEventFlow : EventFlow → Option ThomIsomorphismUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (ThomIsomorphismUp.mk
        (thomIsomorphismDecodeBHist (thomIsomorphismEventAtDefault 0 ef))
        (thomIsomorphismDecodeBHist (thomIsomorphismEventAtDefault 1 ef))
        (thomIsomorphismDecodeBHist (thomIsomorphismEventAtDefault 2 ef))
        (thomIsomorphismDecodeBHist (thomIsomorphismEventAtDefault 3 ef))
        (thomIsomorphismDecodeBHist (thomIsomorphismEventAtDefault 4 ef))
        (thomIsomorphismDecodeBHist (thomIsomorphismEventAtDefault 5 ef))
        (thomIsomorphismDecodeBHist (thomIsomorphismEventAtDefault 6 ef))
        (thomIsomorphismDecodeBHist (thomIsomorphismEventAtDefault 7 ef))
        (thomIsomorphismDecodeBHist (thomIsomorphismEventAtDefault 8 ef))
        (thomIsomorphismDecodeBHist (thomIsomorphismEventAtDefault 9 ef))
        (thomIsomorphismDecodeBHist (thomIsomorphismEventAtDefault 10 ef))
        (thomIsomorphismDecodeBHist (thomIsomorphismEventAtDefault 11 ef)))

private theorem thomIsomorphism_round_trip :
    ∀ x : ThomIsomorphismUp,
      thomIsomorphismFromEventFlow (thomIsomorphismToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B V O K U L A R H C P N =>
      change
        some
          (ThomIsomorphismUp.mk
            (thomIsomorphismDecodeBHist (thomIsomorphismEncodeBHist B))
            (thomIsomorphismDecodeBHist (thomIsomorphismEncodeBHist V))
            (thomIsomorphismDecodeBHist (thomIsomorphismEncodeBHist O))
            (thomIsomorphismDecodeBHist (thomIsomorphismEncodeBHist K))
            (thomIsomorphismDecodeBHist (thomIsomorphismEncodeBHist U))
            (thomIsomorphismDecodeBHist (thomIsomorphismEncodeBHist L))
            (thomIsomorphismDecodeBHist (thomIsomorphismEncodeBHist A))
            (thomIsomorphismDecodeBHist (thomIsomorphismEncodeBHist R))
            (thomIsomorphismDecodeBHist (thomIsomorphismEncodeBHist H))
            (thomIsomorphismDecodeBHist (thomIsomorphismEncodeBHist C))
            (thomIsomorphismDecodeBHist (thomIsomorphismEncodeBHist P))
            (thomIsomorphismDecodeBHist (thomIsomorphismEncodeBHist N))) =
          some (ThomIsomorphismUp.mk B V O K U L A R H C P N)
      rw [thomIsomorphism_decode_encode_bhist B, thomIsomorphism_decode_encode_bhist V,
        thomIsomorphism_decode_encode_bhist O, thomIsomorphism_decode_encode_bhist K,
        thomIsomorphism_decode_encode_bhist U, thomIsomorphism_decode_encode_bhist L,
        thomIsomorphism_decode_encode_bhist A, thomIsomorphism_decode_encode_bhist R,
        thomIsomorphism_decode_encode_bhist H, thomIsomorphism_decode_encode_bhist C,
        thomIsomorphism_decode_encode_bhist P, thomIsomorphism_decode_encode_bhist N]

private theorem thomIsomorphismToEventFlow_injective {x y : ThomIsomorphismUp} :
    thomIsomorphismToEventFlow x = thomIsomorphismToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      thomIsomorphismFromEventFlow (thomIsomorphismToEventFlow x) =
        thomIsomorphismFromEventFlow (thomIsomorphismToEventFlow y) :=
    congrArg thomIsomorphismFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (thomIsomorphism_round_trip x).symm
      (Eq.trans hread (thomIsomorphism_round_trip y)))

instance thomIsomorphismBHistCarrier : BHistCarrier ThomIsomorphismUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := thomIsomorphismToEventFlow
  fromEventFlow := thomIsomorphismFromEventFlow

instance thomIsomorphismChapterTasteGate : ChapterTasteGate ThomIsomorphismUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change thomIsomorphismFromEventFlow (thomIsomorphismToEventFlow x) = some x
    exact thomIsomorphism_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (thomIsomorphismToEventFlow_injective heq)

theorem ThomIsomorphismTasteGate_single_carrier_alignment :
    (∀ h : BHist, thomIsomorphismDecodeBHist (thomIsomorphismEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier ThomIsomorphismUp) ∧
        Nonempty (ChapterTasteGate ThomIsomorphismUp) ∧
          thomIsomorphismEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨thomIsomorphism_decode_encode_bhist,
      Nonempty.intro thomIsomorphismBHistCarrier,
      Nonempty.intro thomIsomorphismChapterTasteGate,
      rfl⟩

end BEDC.Derived.ThomIsomorphismUp
