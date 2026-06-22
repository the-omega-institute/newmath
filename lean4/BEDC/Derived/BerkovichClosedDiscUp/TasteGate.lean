import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BerkovichClosedDiscUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BerkovichClosedDiscUp : Type where
  | mk (K a rho U Q E V H C P N : BHist) : BerkovichClosedDiscUp
  deriving DecidableEq

def berkovichClosedDiscEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: berkovichClosedDiscEncodeBHist h
  | BHist.e1 h => BMark.b1 :: berkovichClosedDiscEncodeBHist h

def berkovichClosedDiscDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (berkovichClosedDiscDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (berkovichClosedDiscDecodeBHist tail)

private theorem berkovichClosedDisc_decode_encode_bhist :
    ∀ h : BHist,
      berkovichClosedDiscDecodeBHist (berkovichClosedDiscEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def berkovichClosedDiscFields : BerkovichClosedDiscUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BerkovichClosedDiscUp.mk K a rho U Q E V H C P N =>
      [K, a, rho, U, Q, E, V, H, C, P, N]

def berkovichClosedDiscToEventFlow : BerkovichClosedDiscUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (berkovichClosedDiscFields x).map berkovichClosedDiscEncodeBHist

private def berkovichClosedDiscEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => berkovichClosedDiscEventAt index rest

def berkovichClosedDiscFromEventFlow
    (ef : EventFlow) : Option BerkovichClosedDiscUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BerkovichClosedDiscUp.mk
      (berkovichClosedDiscDecodeBHist (berkovichClosedDiscEventAt 0 ef))
      (berkovichClosedDiscDecodeBHist (berkovichClosedDiscEventAt 1 ef))
      (berkovichClosedDiscDecodeBHist (berkovichClosedDiscEventAt 2 ef))
      (berkovichClosedDiscDecodeBHist (berkovichClosedDiscEventAt 3 ef))
      (berkovichClosedDiscDecodeBHist (berkovichClosedDiscEventAt 4 ef))
      (berkovichClosedDiscDecodeBHist (berkovichClosedDiscEventAt 5 ef))
      (berkovichClosedDiscDecodeBHist (berkovichClosedDiscEventAt 6 ef))
      (berkovichClosedDiscDecodeBHist (berkovichClosedDiscEventAt 7 ef))
      (berkovichClosedDiscDecodeBHist (berkovichClosedDiscEventAt 8 ef))
      (berkovichClosedDiscDecodeBHist (berkovichClosedDiscEventAt 9 ef))
      (berkovichClosedDiscDecodeBHist (berkovichClosedDiscEventAt 10 ef)))

private theorem berkovichClosedDisc_round_trip
    (x : BerkovichClosedDiscUp) :
    berkovichClosedDiscFromEventFlow (berkovichClosedDiscToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk K a rho U Q E V H C P N =>
      change
        some
          (BerkovichClosedDiscUp.mk
            (berkovichClosedDiscDecodeBHist (berkovichClosedDiscEncodeBHist K))
            (berkovichClosedDiscDecodeBHist (berkovichClosedDiscEncodeBHist a))
            (berkovichClosedDiscDecodeBHist (berkovichClosedDiscEncodeBHist rho))
            (berkovichClosedDiscDecodeBHist (berkovichClosedDiscEncodeBHist U))
            (berkovichClosedDiscDecodeBHist (berkovichClosedDiscEncodeBHist Q))
            (berkovichClosedDiscDecodeBHist (berkovichClosedDiscEncodeBHist E))
            (berkovichClosedDiscDecodeBHist (berkovichClosedDiscEncodeBHist V))
            (berkovichClosedDiscDecodeBHist (berkovichClosedDiscEncodeBHist H))
            (berkovichClosedDiscDecodeBHist (berkovichClosedDiscEncodeBHist C))
            (berkovichClosedDiscDecodeBHist (berkovichClosedDiscEncodeBHist P))
            (berkovichClosedDiscDecodeBHist (berkovichClosedDiscEncodeBHist N))) =
          some (BerkovichClosedDiscUp.mk K a rho U Q E V H C P N)
      rw [berkovichClosedDisc_decode_encode_bhist K,
        berkovichClosedDisc_decode_encode_bhist a,
        berkovichClosedDisc_decode_encode_bhist rho,
        berkovichClosedDisc_decode_encode_bhist U,
        berkovichClosedDisc_decode_encode_bhist Q,
        berkovichClosedDisc_decode_encode_bhist E,
        berkovichClosedDisc_decode_encode_bhist V,
        berkovichClosedDisc_decode_encode_bhist H,
        berkovichClosedDisc_decode_encode_bhist C,
        berkovichClosedDisc_decode_encode_bhist P,
        berkovichClosedDisc_decode_encode_bhist N]

private theorem berkovichClosedDiscToEventFlow_injective {x y : BerkovichClosedDiscUp} :
    berkovichClosedDiscToEventFlow x = berkovichClosedDiscToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      berkovichClosedDiscFromEventFlow (berkovichClosedDiscToEventFlow x) =
        berkovichClosedDiscFromEventFlow (berkovichClosedDiscToEventFlow y) :=
    congrArg berkovichClosedDiscFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (berkovichClosedDisc_round_trip x).symm
      (Eq.trans hread (berkovichClosedDisc_round_trip y)))

instance berkovichClosedDiscBHistCarrier : BHistCarrier BerkovichClosedDiscUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := berkovichClosedDiscToEventFlow
  fromEventFlow := berkovichClosedDiscFromEventFlow

instance berkovichClosedDiscChapterTasteGate : ChapterTasteGate BerkovichClosedDiscUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change berkovichClosedDiscFromEventFlow (berkovichClosedDiscToEventFlow x) = some x
    exact berkovichClosedDisc_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (berkovichClosedDiscToEventFlow_injective heq)

theorem BerkovichClosedDiscTasteGate_single_carrier_alignment :
    (∀ h : BHist, berkovichClosedDiscDecodeBHist (berkovichClosedDiscEncodeBHist h) = h) ∧
      (∀ x : BerkovichClosedDiscUp,
        berkovichClosedDiscFromEventFlow (berkovichClosedDiscToEventFlow x) = some x) ∧
        (∀ x y : BerkovichClosedDiscUp,
          berkovichClosedDiscToEventFlow x = berkovichClosedDiscToEventFlow y → x = y) ∧
          berkovichClosedDiscEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨berkovichClosedDisc_decode_encode_bhist,
      berkovichClosedDisc_round_trip,
      (fun _ _ heq => berkovichClosedDiscToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.BerkovichClosedDiscUp
