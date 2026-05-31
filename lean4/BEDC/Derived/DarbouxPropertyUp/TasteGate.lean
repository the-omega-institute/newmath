import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DarbouxPropertyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DarbouxPropertyUp : Type where
  | mk (I F A B Y S M R Q E H C P N : BHist) : DarbouxPropertyUp
  deriving DecidableEq

def darbouxPropertyEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: darbouxPropertyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: darbouxPropertyEncodeBHist h

def darbouxPropertyDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (darbouxPropertyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (darbouxPropertyDecodeBHist tail)

private theorem DarbouxPropertyTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, darbouxPropertyDecodeBHist (darbouxPropertyEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def darbouxPropertyFields : DarbouxPropertyUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DarbouxPropertyUp.mk I F A B Y S M R Q E H C P N =>
      [I, F, A, B, Y, S, M, R, Q, E, H, C, P, N]

def darbouxPropertyToEventFlow : DarbouxPropertyUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (darbouxPropertyFields x).map darbouxPropertyEncodeBHist

private def darbouxPropertyEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => darbouxPropertyEventAtDefault index rest

def darbouxPropertyFromEventFlow (ef : EventFlow) : Option DarbouxPropertyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DarbouxPropertyUp.mk
      (darbouxPropertyDecodeBHist (darbouxPropertyEventAtDefault 0 ef))
      (darbouxPropertyDecodeBHist (darbouxPropertyEventAtDefault 1 ef))
      (darbouxPropertyDecodeBHist (darbouxPropertyEventAtDefault 2 ef))
      (darbouxPropertyDecodeBHist (darbouxPropertyEventAtDefault 3 ef))
      (darbouxPropertyDecodeBHist (darbouxPropertyEventAtDefault 4 ef))
      (darbouxPropertyDecodeBHist (darbouxPropertyEventAtDefault 5 ef))
      (darbouxPropertyDecodeBHist (darbouxPropertyEventAtDefault 6 ef))
      (darbouxPropertyDecodeBHist (darbouxPropertyEventAtDefault 7 ef))
      (darbouxPropertyDecodeBHist (darbouxPropertyEventAtDefault 8 ef))
      (darbouxPropertyDecodeBHist (darbouxPropertyEventAtDefault 9 ef))
      (darbouxPropertyDecodeBHist (darbouxPropertyEventAtDefault 10 ef))
      (darbouxPropertyDecodeBHist (darbouxPropertyEventAtDefault 11 ef))
      (darbouxPropertyDecodeBHist (darbouxPropertyEventAtDefault 12 ef))
      (darbouxPropertyDecodeBHist (darbouxPropertyEventAtDefault 13 ef)))

private theorem DarbouxPropertyTasteGate_single_carrier_alignment_round_trip :
    ∀ x : DarbouxPropertyUp,
      darbouxPropertyFromEventFlow (darbouxPropertyToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I F A B Y S M R Q E H C P N =>
      change
        some
            (DarbouxPropertyUp.mk
              (darbouxPropertyDecodeBHist (darbouxPropertyEncodeBHist I))
              (darbouxPropertyDecodeBHist (darbouxPropertyEncodeBHist F))
              (darbouxPropertyDecodeBHist (darbouxPropertyEncodeBHist A))
              (darbouxPropertyDecodeBHist (darbouxPropertyEncodeBHist B))
              (darbouxPropertyDecodeBHist (darbouxPropertyEncodeBHist Y))
              (darbouxPropertyDecodeBHist (darbouxPropertyEncodeBHist S))
              (darbouxPropertyDecodeBHist (darbouxPropertyEncodeBHist M))
              (darbouxPropertyDecodeBHist (darbouxPropertyEncodeBHist R))
              (darbouxPropertyDecodeBHist (darbouxPropertyEncodeBHist Q))
              (darbouxPropertyDecodeBHist (darbouxPropertyEncodeBHist E))
              (darbouxPropertyDecodeBHist (darbouxPropertyEncodeBHist H))
              (darbouxPropertyDecodeBHist (darbouxPropertyEncodeBHist C))
              (darbouxPropertyDecodeBHist (darbouxPropertyEncodeBHist P))
              (darbouxPropertyDecodeBHist (darbouxPropertyEncodeBHist N))) =
          some (DarbouxPropertyUp.mk I F A B Y S M R Q E H C P N)
      rw [DarbouxPropertyTasteGate_single_carrier_alignment_decode I,
        DarbouxPropertyTasteGate_single_carrier_alignment_decode F,
        DarbouxPropertyTasteGate_single_carrier_alignment_decode A,
        DarbouxPropertyTasteGate_single_carrier_alignment_decode B,
        DarbouxPropertyTasteGate_single_carrier_alignment_decode Y,
        DarbouxPropertyTasteGate_single_carrier_alignment_decode S,
        DarbouxPropertyTasteGate_single_carrier_alignment_decode M,
        DarbouxPropertyTasteGate_single_carrier_alignment_decode R,
        DarbouxPropertyTasteGate_single_carrier_alignment_decode Q,
        DarbouxPropertyTasteGate_single_carrier_alignment_decode E,
        DarbouxPropertyTasteGate_single_carrier_alignment_decode H,
        DarbouxPropertyTasteGate_single_carrier_alignment_decode C,
        DarbouxPropertyTasteGate_single_carrier_alignment_decode P,
        DarbouxPropertyTasteGate_single_carrier_alignment_decode N]

private theorem DarbouxPropertyTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DarbouxPropertyUp} :
    darbouxPropertyToEventFlow x = darbouxPropertyToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      darbouxPropertyFromEventFlow (darbouxPropertyToEventFlow x) =
        darbouxPropertyFromEventFlow (darbouxPropertyToEventFlow y) :=
    congrArg darbouxPropertyFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (DarbouxPropertyTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (DarbouxPropertyTasteGate_single_carrier_alignment_round_trip y)))

instance darbouxPropertyBHistCarrier : BHistCarrier DarbouxPropertyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := darbouxPropertyToEventFlow
  fromEventFlow := darbouxPropertyFromEventFlow

instance darbouxPropertyChapterTasteGate : ChapterTasteGate DarbouxPropertyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change darbouxPropertyFromEventFlow (darbouxPropertyToEventFlow x) = some x
    exact DarbouxPropertyTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DarbouxPropertyTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem DarbouxPropertyTasteGate_single_carrier_alignment :
    (∀ h : BHist, darbouxPropertyDecodeBHist (darbouxPropertyEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier DarbouxPropertyUp) ∧
        Nonempty (ChapterTasteGate DarbouxPropertyUp) ∧
          darbouxPropertyEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨DarbouxPropertyTasteGate_single_carrier_alignment_decode,
      ⟨darbouxPropertyBHistCarrier⟩,
      ⟨darbouxPropertyChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.DarbouxPropertyUp
