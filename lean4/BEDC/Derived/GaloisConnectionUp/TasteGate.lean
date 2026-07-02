import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Derived.GaloisConnectionUp
import BEDC.Meta.TasteGate

namespace BEDC.Derived.GaloisConnectionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def galoisConnectionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: galoisConnectionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: galoisConnectionEncodeBHist h

def galoisConnectionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (galoisConnectionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (galoisConnectionDecodeBHist tail)

private theorem GaloisConnectionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, galoisConnectionDecodeBHist (galoisConnectionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def galoisConnectionFields : GaloisConnectionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | GaloisConnectionUp.mk P Q F G M A T R L N => [P, Q, F, G, M, A, T, R, L, N]

def galoisConnectionToEventFlow : GaloisConnectionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (galoisConnectionFields x).map galoisConnectionEncodeBHist

private def galoisConnectionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => galoisConnectionEventAtDefault index rest

def galoisConnectionFromEventFlow (ef : EventFlow) : Option GaloisConnectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (GaloisConnectionUp.mk
      (galoisConnectionDecodeBHist (galoisConnectionEventAtDefault 0 ef))
      (galoisConnectionDecodeBHist (galoisConnectionEventAtDefault 1 ef))
      (galoisConnectionDecodeBHist (galoisConnectionEventAtDefault 2 ef))
      (galoisConnectionDecodeBHist (galoisConnectionEventAtDefault 3 ef))
      (galoisConnectionDecodeBHist (galoisConnectionEventAtDefault 4 ef))
      (galoisConnectionDecodeBHist (galoisConnectionEventAtDefault 5 ef))
      (galoisConnectionDecodeBHist (galoisConnectionEventAtDefault 6 ef))
      (galoisConnectionDecodeBHist (galoisConnectionEventAtDefault 7 ef))
      (galoisConnectionDecodeBHist (galoisConnectionEventAtDefault 8 ef))
      (galoisConnectionDecodeBHist (galoisConnectionEventAtDefault 9 ef)))

private theorem GaloisConnectionTasteGate_single_carrier_alignment_round_trip
    (x : GaloisConnectionUp) :
    galoisConnectionFromEventFlow (galoisConnectionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk P Q F G M A T R L N =>
      change
        some
          (GaloisConnectionUp.mk
            (galoisConnectionDecodeBHist (galoisConnectionEncodeBHist P))
            (galoisConnectionDecodeBHist (galoisConnectionEncodeBHist Q))
            (galoisConnectionDecodeBHist (galoisConnectionEncodeBHist F))
            (galoisConnectionDecodeBHist (galoisConnectionEncodeBHist G))
            (galoisConnectionDecodeBHist (galoisConnectionEncodeBHist M))
            (galoisConnectionDecodeBHist (galoisConnectionEncodeBHist A))
            (galoisConnectionDecodeBHist (galoisConnectionEncodeBHist T))
            (galoisConnectionDecodeBHist (galoisConnectionEncodeBHist R))
            (galoisConnectionDecodeBHist (galoisConnectionEncodeBHist L))
            (galoisConnectionDecodeBHist (galoisConnectionEncodeBHist N))) =
          some (GaloisConnectionUp.mk P Q F G M A T R L N)
      rw [GaloisConnectionTasteGate_single_carrier_alignment_decode_encode P,
        GaloisConnectionTasteGate_single_carrier_alignment_decode_encode Q,
        GaloisConnectionTasteGate_single_carrier_alignment_decode_encode F,
        GaloisConnectionTasteGate_single_carrier_alignment_decode_encode G,
        GaloisConnectionTasteGate_single_carrier_alignment_decode_encode M,
        GaloisConnectionTasteGate_single_carrier_alignment_decode_encode A,
        GaloisConnectionTasteGate_single_carrier_alignment_decode_encode T,
        GaloisConnectionTasteGate_single_carrier_alignment_decode_encode R,
        GaloisConnectionTasteGate_single_carrier_alignment_decode_encode L,
        GaloisConnectionTasteGate_single_carrier_alignment_decode_encode N]

private theorem GaloisConnectionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : GaloisConnectionUp} :
    galoisConnectionToEventFlow x = galoisConnectionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      galoisConnectionFromEventFlow (galoisConnectionToEventFlow x) =
        galoisConnectionFromEventFlow (galoisConnectionToEventFlow y) :=
    congrArg galoisConnectionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (GaloisConnectionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (GaloisConnectionTasteGate_single_carrier_alignment_round_trip y)))

instance galoisConnectionBHistCarrier : BHistCarrier GaloisConnectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := galoisConnectionToEventFlow
  fromEventFlow := galoisConnectionFromEventFlow

instance galoisConnectionChapterTasteGate :
    ChapterTasteGate GaloisConnectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change galoisConnectionFromEventFlow (galoisConnectionToEventFlow x) = some x
    exact GaloisConnectionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (GaloisConnectionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem GaloisConnectionTasteGate_single_carrier_alignment :
    (forall h : BHist, galoisConnectionDecodeBHist (galoisConnectionEncodeBHist h) = h) ∧
      (forall x : GaloisConnectionUp,
        galoisConnectionFromEventFlow (galoisConnectionToEventFlow x) = some x) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨GaloisConnectionTasteGate_single_carrier_alignment_decode_encode,
      GaloisConnectionTasteGate_single_carrier_alignment_round_trip⟩

end BEDC.Derived.GaloisConnectionUp
