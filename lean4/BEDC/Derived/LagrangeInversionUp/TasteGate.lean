import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LagrangeInversionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LagrangeInversionUp : Type where
  | mk (c J a1 R B Q E H C P N : BHist) : LagrangeInversionUp

def lagrangeInversionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: lagrangeInversionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: lagrangeInversionEncodeBHist h

def lagrangeInversionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (lagrangeInversionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (lagrangeInversionDecodeBHist tail)

private theorem LagrangeInversionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, lagrangeInversionDecodeBHist (lagrangeInversionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def lagrangeInversionFields : LagrangeInversionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LagrangeInversionUp.mk c J a1 R B Q E H C P N => [c, J, a1, R, B, Q, E, H, C, P, N]

def lagrangeInversionToEventFlow : LagrangeInversionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (lagrangeInversionFields x).map lagrangeInversionEncodeBHist

private def lagrangeInversionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => lagrangeInversionEventAt index rest

def lagrangeInversionFromEventFlow (ef : EventFlow) : Option LagrangeInversionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LagrangeInversionUp.mk
      (lagrangeInversionDecodeBHist (lagrangeInversionEventAt 0 ef))
      (lagrangeInversionDecodeBHist (lagrangeInversionEventAt 1 ef))
      (lagrangeInversionDecodeBHist (lagrangeInversionEventAt 2 ef))
      (lagrangeInversionDecodeBHist (lagrangeInversionEventAt 3 ef))
      (lagrangeInversionDecodeBHist (lagrangeInversionEventAt 4 ef))
      (lagrangeInversionDecodeBHist (lagrangeInversionEventAt 5 ef))
      (lagrangeInversionDecodeBHist (lagrangeInversionEventAt 6 ef))
      (lagrangeInversionDecodeBHist (lagrangeInversionEventAt 7 ef))
      (lagrangeInversionDecodeBHist (lagrangeInversionEventAt 8 ef))
      (lagrangeInversionDecodeBHist (lagrangeInversionEventAt 9 ef))
      (lagrangeInversionDecodeBHist (lagrangeInversionEventAt 10 ef)))

private theorem LagrangeInversionTasteGate_single_carrier_alignment_round_trip
    (x : LagrangeInversionUp) :
    lagrangeInversionFromEventFlow (lagrangeInversionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk c J a1 R B Q E H C P N =>
      change
        some
          (LagrangeInversionUp.mk
            (lagrangeInversionDecodeBHist (lagrangeInversionEncodeBHist c))
            (lagrangeInversionDecodeBHist (lagrangeInversionEncodeBHist J))
            (lagrangeInversionDecodeBHist (lagrangeInversionEncodeBHist a1))
            (lagrangeInversionDecodeBHist (lagrangeInversionEncodeBHist R))
            (lagrangeInversionDecodeBHist (lagrangeInversionEncodeBHist B))
            (lagrangeInversionDecodeBHist (lagrangeInversionEncodeBHist Q))
            (lagrangeInversionDecodeBHist (lagrangeInversionEncodeBHist E))
            (lagrangeInversionDecodeBHist (lagrangeInversionEncodeBHist H))
            (lagrangeInversionDecodeBHist (lagrangeInversionEncodeBHist C))
            (lagrangeInversionDecodeBHist (lagrangeInversionEncodeBHist P))
            (lagrangeInversionDecodeBHist (lagrangeInversionEncodeBHist N))) =
          some (LagrangeInversionUp.mk c J a1 R B Q E H C P N)
      rw [LagrangeInversionTasteGate_single_carrier_alignment_decode_encode c,
        LagrangeInversionTasteGate_single_carrier_alignment_decode_encode J,
        LagrangeInversionTasteGate_single_carrier_alignment_decode_encode a1,
        LagrangeInversionTasteGate_single_carrier_alignment_decode_encode R,
        LagrangeInversionTasteGate_single_carrier_alignment_decode_encode B,
        LagrangeInversionTasteGate_single_carrier_alignment_decode_encode Q,
        LagrangeInversionTasteGate_single_carrier_alignment_decode_encode E,
        LagrangeInversionTasteGate_single_carrier_alignment_decode_encode H,
        LagrangeInversionTasteGate_single_carrier_alignment_decode_encode C,
        LagrangeInversionTasteGate_single_carrier_alignment_decode_encode P,
        LagrangeInversionTasteGate_single_carrier_alignment_decode_encode N]

private theorem lagrangeInversionToEventFlow_injective {x y : LagrangeInversionUp} :
    lagrangeInversionToEventFlow x = lagrangeInversionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      lagrangeInversionFromEventFlow (lagrangeInversionToEventFlow x) =
        lagrangeInversionFromEventFlow (lagrangeInversionToEventFlow y) :=
    congrArg lagrangeInversionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (LagrangeInversionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (LagrangeInversionTasteGate_single_carrier_alignment_round_trip y)))

instance lagrangeInversionBHistCarrier : BHistCarrier LagrangeInversionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := lagrangeInversionToEventFlow
  fromEventFlow := lagrangeInversionFromEventFlow

instance lagrangeInversionChapterTasteGate : ChapterTasteGate LagrangeInversionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change lagrangeInversionFromEventFlow (lagrangeInversionToEventFlow x) = some x
    exact LagrangeInversionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (lagrangeInversionToEventFlow_injective heq)

def taste_gate : ChapterTasteGate LagrangeInversionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  lagrangeInversionChapterTasteGate

theorem LagrangeInversionTasteGate_single_carrier_alignment :
    (∀ h : BHist, lagrangeInversionDecodeBHist (lagrangeInversionEncodeBHist h) = h) ∧
      (∀ x : LagrangeInversionUp,
        lagrangeInversionFromEventFlow (lagrangeInversionToEventFlow x) = some x) ∧
        (∀ x y : LagrangeInversionUp,
          lagrangeInversionToEventFlow x = lagrangeInversionToEventFlow y → x = y) ∧
          lagrangeInversionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨LagrangeInversionTasteGate_single_carrier_alignment_decode_encode,
      LagrangeInversionTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => lagrangeInversionToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.LagrangeInversionUp
