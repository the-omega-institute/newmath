import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LipschitzConstantUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LipschitzConstantUp : Type where
  | mk (K X Y D F M H C P N : BHist) : LipschitzConstantUp
  deriving DecidableEq

def lipschitzConstantEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: lipschitzConstantEncodeBHist h
  | BHist.e1 h => BMark.b1 :: lipschitzConstantEncodeBHist h

def lipschitzConstantDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (lipschitzConstantDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (lipschitzConstantDecodeBHist tail)

private theorem LipschitzConstantTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, lipschitzConstantDecodeBHist (lipschitzConstantEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def lipschitzConstantFields : LipschitzConstantUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LipschitzConstantUp.mk K X Y D F M H C P N => [K, X, Y, D, F, M, H, C, P, N]

def lipschitzConstantToEventFlow : LipschitzConstantUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (lipschitzConstantFields x).map lipschitzConstantEncodeBHist

private def lipschitzConstantEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => lipschitzConstantEventAtDefault index rest

def lipschitzConstantFromEventFlow (ef : EventFlow) : Option LipschitzConstantUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LipschitzConstantUp.mk
      (lipschitzConstantDecodeBHist (lipschitzConstantEventAtDefault 0 ef))
      (lipschitzConstantDecodeBHist (lipschitzConstantEventAtDefault 1 ef))
      (lipschitzConstantDecodeBHist (lipschitzConstantEventAtDefault 2 ef))
      (lipschitzConstantDecodeBHist (lipschitzConstantEventAtDefault 3 ef))
      (lipschitzConstantDecodeBHist (lipschitzConstantEventAtDefault 4 ef))
      (lipschitzConstantDecodeBHist (lipschitzConstantEventAtDefault 5 ef))
      (lipschitzConstantDecodeBHist (lipschitzConstantEventAtDefault 6 ef))
      (lipschitzConstantDecodeBHist (lipschitzConstantEventAtDefault 7 ef))
      (lipschitzConstantDecodeBHist (lipschitzConstantEventAtDefault 8 ef))
      (lipschitzConstantDecodeBHist (lipschitzConstantEventAtDefault 9 ef)))

private theorem LipschitzConstantTasteGate_single_carrier_alignment_round_trip :
    ∀ x : LipschitzConstantUp,
      lipschitzConstantFromEventFlow (lipschitzConstantToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K X Y D F M H C P N =>
      change
        some
          (LipschitzConstantUp.mk
            (lipschitzConstantDecodeBHist (lipschitzConstantEncodeBHist K))
            (lipschitzConstantDecodeBHist (lipschitzConstantEncodeBHist X))
            (lipschitzConstantDecodeBHist (lipschitzConstantEncodeBHist Y))
            (lipschitzConstantDecodeBHist (lipschitzConstantEncodeBHist D))
            (lipschitzConstantDecodeBHist (lipschitzConstantEncodeBHist F))
            (lipschitzConstantDecodeBHist (lipschitzConstantEncodeBHist M))
            (lipschitzConstantDecodeBHist (lipschitzConstantEncodeBHist H))
            (lipschitzConstantDecodeBHist (lipschitzConstantEncodeBHist C))
            (lipschitzConstantDecodeBHist (lipschitzConstantEncodeBHist P))
            (lipschitzConstantDecodeBHist (lipschitzConstantEncodeBHist N))) =
          some (LipschitzConstantUp.mk K X Y D F M H C P N)
      rw [LipschitzConstantTasteGate_single_carrier_alignment_decode K,
        LipschitzConstantTasteGate_single_carrier_alignment_decode X,
        LipschitzConstantTasteGate_single_carrier_alignment_decode Y,
        LipschitzConstantTasteGate_single_carrier_alignment_decode D,
        LipschitzConstantTasteGate_single_carrier_alignment_decode F,
        LipschitzConstantTasteGate_single_carrier_alignment_decode M,
        LipschitzConstantTasteGate_single_carrier_alignment_decode H,
        LipschitzConstantTasteGate_single_carrier_alignment_decode C,
        LipschitzConstantTasteGate_single_carrier_alignment_decode P,
        LipschitzConstantTasteGate_single_carrier_alignment_decode N]

private theorem LipschitzConstantTasteGate_single_carrier_alignment_injective
    {x y : LipschitzConstantUp} :
    lipschitzConstantToEventFlow x = lipschitzConstantToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      lipschitzConstantFromEventFlow (lipschitzConstantToEventFlow x) =
        lipschitzConstantFromEventFlow (lipschitzConstantToEventFlow y) :=
    congrArg lipschitzConstantFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (LipschitzConstantTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (LipschitzConstantTasteGate_single_carrier_alignment_round_trip y)))

instance lipschitzConstantBHistCarrier : BHistCarrier LipschitzConstantUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := lipschitzConstantToEventFlow
  fromEventFlow := lipschitzConstantFromEventFlow

instance lipschitzConstantChapterTasteGate : ChapterTasteGate LipschitzConstantUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change lipschitzConstantFromEventFlow (lipschitzConstantToEventFlow x) = some x
    exact LipschitzConstantTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LipschitzConstantTasteGate_single_carrier_alignment_injective heq)

theorem LipschitzConstantTasteGate_single_carrier_alignment :
    ChapterTasteGate LipschitzConstantUp := by
  -- BEDC touchpoint anchor: BHist BMark
  exact lipschitzConstantChapterTasteGate

end BEDC.Derived.LipschitzConstantUp
