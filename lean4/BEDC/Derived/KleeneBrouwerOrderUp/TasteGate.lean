import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.KleeneBrouwerOrderUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive KleeneBrouwerOrderUp : Type where
  | mk (T N P F L A H C Q M : BHist) : KleeneBrouwerOrderUp
  deriving DecidableEq

def kleeneBrouwerOrderEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: kleeneBrouwerOrderEncodeBHist h
  | BHist.e1 h => BMark.b1 :: kleeneBrouwerOrderEncodeBHist h

def kleeneBrouwerOrderDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (kleeneBrouwerOrderDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (kleeneBrouwerOrderDecodeBHist tail)

private theorem kleeneBrouwerOrder_decode_encode_bhist :
    ∀ h : BHist,
      kleeneBrouwerOrderDecodeBHist (kleeneBrouwerOrderEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def kleeneBrouwerOrderFields : KleeneBrouwerOrderUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | KleeneBrouwerOrderUp.mk T N P F L A H C Q M => [T, N, P, F, L, A, H, C, Q, M]

def kleeneBrouwerOrderToEventFlow : KleeneBrouwerOrderUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (kleeneBrouwerOrderFields x).map kleeneBrouwerOrderEncodeBHist

private def kleeneBrouwerOrderEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => kleeneBrouwerOrderEventAt index rest

def kleeneBrouwerOrderFromEventFlow (ef : EventFlow) : Option KleeneBrouwerOrderUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (KleeneBrouwerOrderUp.mk
      (kleeneBrouwerOrderDecodeBHist (kleeneBrouwerOrderEventAt 0 ef))
      (kleeneBrouwerOrderDecodeBHist (kleeneBrouwerOrderEventAt 1 ef))
      (kleeneBrouwerOrderDecodeBHist (kleeneBrouwerOrderEventAt 2 ef))
      (kleeneBrouwerOrderDecodeBHist (kleeneBrouwerOrderEventAt 3 ef))
      (kleeneBrouwerOrderDecodeBHist (kleeneBrouwerOrderEventAt 4 ef))
      (kleeneBrouwerOrderDecodeBHist (kleeneBrouwerOrderEventAt 5 ef))
      (kleeneBrouwerOrderDecodeBHist (kleeneBrouwerOrderEventAt 6 ef))
      (kleeneBrouwerOrderDecodeBHist (kleeneBrouwerOrderEventAt 7 ef))
      (kleeneBrouwerOrderDecodeBHist (kleeneBrouwerOrderEventAt 8 ef))
      (kleeneBrouwerOrderDecodeBHist (kleeneBrouwerOrderEventAt 9 ef)))

private theorem kleeneBrouwerOrder_round_trip (x : KleeneBrouwerOrderUp) :
    kleeneBrouwerOrderFromEventFlow (kleeneBrouwerOrderToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk T N P F L A H C Q M =>
      change
        some
          (KleeneBrouwerOrderUp.mk
            (kleeneBrouwerOrderDecodeBHist (kleeneBrouwerOrderEncodeBHist T))
            (kleeneBrouwerOrderDecodeBHist (kleeneBrouwerOrderEncodeBHist N))
            (kleeneBrouwerOrderDecodeBHist (kleeneBrouwerOrderEncodeBHist P))
            (kleeneBrouwerOrderDecodeBHist (kleeneBrouwerOrderEncodeBHist F))
            (kleeneBrouwerOrderDecodeBHist (kleeneBrouwerOrderEncodeBHist L))
            (kleeneBrouwerOrderDecodeBHist (kleeneBrouwerOrderEncodeBHist A))
            (kleeneBrouwerOrderDecodeBHist (kleeneBrouwerOrderEncodeBHist H))
            (kleeneBrouwerOrderDecodeBHist (kleeneBrouwerOrderEncodeBHist C))
            (kleeneBrouwerOrderDecodeBHist (kleeneBrouwerOrderEncodeBHist Q))
            (kleeneBrouwerOrderDecodeBHist (kleeneBrouwerOrderEncodeBHist M))) =
          some (KleeneBrouwerOrderUp.mk T N P F L A H C Q M)
      rw [kleeneBrouwerOrder_decode_encode_bhist T,
        kleeneBrouwerOrder_decode_encode_bhist N,
        kleeneBrouwerOrder_decode_encode_bhist P,
        kleeneBrouwerOrder_decode_encode_bhist F,
        kleeneBrouwerOrder_decode_encode_bhist L,
        kleeneBrouwerOrder_decode_encode_bhist A,
        kleeneBrouwerOrder_decode_encode_bhist H,
        kleeneBrouwerOrder_decode_encode_bhist C,
        kleeneBrouwerOrder_decode_encode_bhist Q,
        kleeneBrouwerOrder_decode_encode_bhist M]

private theorem kleeneBrouwerOrderToEventFlow_injective {x y : KleeneBrouwerOrderUp} :
    kleeneBrouwerOrderToEventFlow x = kleeneBrouwerOrderToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      kleeneBrouwerOrderFromEventFlow (kleeneBrouwerOrderToEventFlow x) =
        kleeneBrouwerOrderFromEventFlow (kleeneBrouwerOrderToEventFlow y) :=
    congrArg kleeneBrouwerOrderFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (kleeneBrouwerOrder_round_trip x).symm
      (Eq.trans hread (kleeneBrouwerOrder_round_trip y)))

private theorem kleeneBrouwerOrder_fields_faithful :
    ∀ x y : KleeneBrouwerOrderUp,
      kleeneBrouwerOrderFields x = kleeneBrouwerOrderFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk T N P F L A H C Q M =>
      cases y with
      | mk T' N' P' F' L' A' H' C' Q' M' =>
          cases hfields
          rfl

instance kleeneBrouwerOrderBHistCarrier : BHistCarrier KleeneBrouwerOrderUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := kleeneBrouwerOrderToEventFlow
  fromEventFlow := kleeneBrouwerOrderFromEventFlow

instance kleeneBrouwerOrderChapterTasteGate :
    ChapterTasteGate KleeneBrouwerOrderUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change kleeneBrouwerOrderFromEventFlow (kleeneBrouwerOrderToEventFlow x) = some x
    exact kleeneBrouwerOrder_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (kleeneBrouwerOrderToEventFlow_injective heq)

instance kleeneBrouwerOrderFieldFaithful : FieldFaithful KleeneBrouwerOrderUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := kleeneBrouwerOrderFields
  field_faithful := kleeneBrouwerOrder_fields_faithful

instance kleeneBrouwerOrderNontrivial : Nontrivial KleeneBrouwerOrderUp where
  witness_pair :=
    ⟨KleeneBrouwerOrderUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      KleeneBrouwerOrderUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

theorem KleeneBrouwerOrderTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        kleeneBrouwerOrderDecodeBHist (kleeneBrouwerOrderEncodeBHist h) = h) ∧
      (∀ x : KleeneBrouwerOrderUp,
        kleeneBrouwerOrderFromEventFlow (kleeneBrouwerOrderToEventFlow x) = some x) ∧
      (∀ x y : KleeneBrouwerOrderUp,
        kleeneBrouwerOrderToEventFlow x =
          kleeneBrouwerOrderToEventFlow y → x = y) ∧
      kleeneBrouwerOrderEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact ⟨kleeneBrouwerOrder_decode_encode_bhist,
    kleeneBrouwerOrder_round_trip,
    fun _ _ heq => kleeneBrouwerOrderToEventFlow_injective heq,
    rfl⟩

end BEDC.Derived.KleeneBrouwerOrderUp
