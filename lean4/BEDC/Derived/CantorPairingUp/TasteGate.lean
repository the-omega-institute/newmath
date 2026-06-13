import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CantorPairingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CantorPairingUp : Type where
  -- BEDC touchpoint anchor: BHist BMark
  | mk (X Y J L R H C P N : BHist) : CantorPairingUp

def cantorPairingEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cantorPairingEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cantorPairingEncodeBHist h

def cantorPairingDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cantorPairingDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cantorPairingDecodeBHist tail)

private theorem cantorPairingDecode_encode :
    ∀ h : BHist, cantorPairingDecodeBHist (cantorPairingEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cantorPairingFields : CantorPairingUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CantorPairingUp.mk X Y J L R H C P N => [X, Y, J, L, R, H, C, P, N]

def cantorPairingToEventFlow : CantorPairingUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (cantorPairingFields x).map cantorPairingEncodeBHist

private def cantorPairingEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      cantorPairingEventAtDefault index rest

def cantorPairingFromEventFlow (ef : EventFlow) : Option CantorPairingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CantorPairingUp.mk
      (cantorPairingDecodeBHist (cantorPairingEventAtDefault 0 ef))
      (cantorPairingDecodeBHist (cantorPairingEventAtDefault 1 ef))
      (cantorPairingDecodeBHist (cantorPairingEventAtDefault 2 ef))
      (cantorPairingDecodeBHist (cantorPairingEventAtDefault 3 ef))
      (cantorPairingDecodeBHist (cantorPairingEventAtDefault 4 ef))
      (cantorPairingDecodeBHist (cantorPairingEventAtDefault 5 ef))
      (cantorPairingDecodeBHist (cantorPairingEventAtDefault 6 ef))
      (cantorPairingDecodeBHist (cantorPairingEventAtDefault 7 ef))
      (cantorPairingDecodeBHist (cantorPairingEventAtDefault 8 ef)))

private theorem cantorPairing_round_trip :
    ∀ x : CantorPairingUp,
      cantorPairingFromEventFlow (cantorPairingToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk X Y J L R H C P N =>
      change
        some
          (CantorPairingUp.mk
            (cantorPairingDecodeBHist (cantorPairingEncodeBHist X))
            (cantorPairingDecodeBHist (cantorPairingEncodeBHist Y))
            (cantorPairingDecodeBHist (cantorPairingEncodeBHist J))
            (cantorPairingDecodeBHist (cantorPairingEncodeBHist L))
            (cantorPairingDecodeBHist (cantorPairingEncodeBHist R))
            (cantorPairingDecodeBHist (cantorPairingEncodeBHist H))
            (cantorPairingDecodeBHist (cantorPairingEncodeBHist C))
            (cantorPairingDecodeBHist (cantorPairingEncodeBHist P))
            (cantorPairingDecodeBHist (cantorPairingEncodeBHist N))) =
          some (CantorPairingUp.mk X Y J L R H C P N)
      rw [cantorPairingDecode_encode X, cantorPairingDecode_encode Y,
        cantorPairingDecode_encode J, cantorPairingDecode_encode L,
        cantorPairingDecode_encode R, cantorPairingDecode_encode H,
        cantorPairingDecode_encode C, cantorPairingDecode_encode P,
        cantorPairingDecode_encode N]

private theorem cantorPairingToEventFlow_injective {x y : CantorPairingUp} :
    cantorPairingToEventFlow x = cantorPairingToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cantorPairingFromEventFlow (cantorPairingToEventFlow x) =
        cantorPairingFromEventFlow (cantorPairingToEventFlow y) :=
    congrArg cantorPairingFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cantorPairing_round_trip x).symm
      (Eq.trans hread (cantorPairing_round_trip y)))

instance cantorPairingBHistCarrier : BHistCarrier CantorPairingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cantorPairingToEventFlow
  fromEventFlow := cantorPairingFromEventFlow

instance cantorPairingChapterTasteGate : ChapterTasteGate CantorPairingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cantorPairingFromEventFlow (cantorPairingToEventFlow x) = some x
    exact cantorPairing_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cantorPairingToEventFlow_injective heq)

theorem CantorPairingTasteGate_single_carrier_alignment :
    (∀ h : BHist, cantorPairingDecodeBHist (cantorPairingEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier CantorPairingUp) ∧
        Nonempty (ChapterTasteGate CantorPairingUp) ∧
          cantorPairingEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨cantorPairingDecode_encode,
      ⟨⟨cantorPairingBHistCarrier⟩, ⟨⟨cantorPairingChapterTasteGate⟩, rfl⟩⟩⟩

end BEDC.Derived.CantorPairingUp
