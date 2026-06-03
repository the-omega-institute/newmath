import BEDC.Derived.NoetherianModuleUp
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.NoetherianModuleUp
namespace TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive NoetherianModuleUp : Type where
  | mk (M R I A G H Q P N : BHist) : NoetherianModuleUp
  deriving DecidableEq

def noetherianModuleEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: noetherianModuleEncodeBHist h
  | BHist.e1 h => BMark.b1 :: noetherianModuleEncodeBHist h

def noetherianModuleDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (noetherianModuleDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (noetherianModuleDecodeBHist tail)

private theorem NoetherianModuleTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, noetherianModuleDecodeBHist (noetherianModuleEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def noetherianModuleFields : NoetherianModuleUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | NoetherianModuleUp.mk M R I A G H Q P N => [M, R, I, A, G, H, Q, P, N]

def noetherianModuleToEventFlow : NoetherianModuleUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (noetherianModuleFields x).map noetherianModuleEncodeBHist

private def noetherianModuleEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => noetherianModuleEventAt index rest

def noetherianModuleFromEventFlow (ef : EventFlow) : Option NoetherianModuleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (NoetherianModuleUp.mk
      (noetherianModuleDecodeBHist (noetherianModuleEventAt 0 ef))
      (noetherianModuleDecodeBHist (noetherianModuleEventAt 1 ef))
      (noetherianModuleDecodeBHist (noetherianModuleEventAt 2 ef))
      (noetherianModuleDecodeBHist (noetherianModuleEventAt 3 ef))
      (noetherianModuleDecodeBHist (noetherianModuleEventAt 4 ef))
      (noetherianModuleDecodeBHist (noetherianModuleEventAt 5 ef))
      (noetherianModuleDecodeBHist (noetherianModuleEventAt 6 ef))
      (noetherianModuleDecodeBHist (noetherianModuleEventAt 7 ef))
      (noetherianModuleDecodeBHist (noetherianModuleEventAt 8 ef)))

private theorem NoetherianModuleTasteGate_single_carrier_alignment_round_trip
    (x : NoetherianModuleUp) :
    noetherianModuleFromEventFlow (noetherianModuleToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk M R I A G H Q P N =>
      change
        some
          (NoetherianModuleUp.mk
            (noetherianModuleDecodeBHist (noetherianModuleEncodeBHist M))
            (noetherianModuleDecodeBHist (noetherianModuleEncodeBHist R))
            (noetherianModuleDecodeBHist (noetherianModuleEncodeBHist I))
            (noetherianModuleDecodeBHist (noetherianModuleEncodeBHist A))
            (noetherianModuleDecodeBHist (noetherianModuleEncodeBHist G))
            (noetherianModuleDecodeBHist (noetherianModuleEncodeBHist H))
            (noetherianModuleDecodeBHist (noetherianModuleEncodeBHist Q))
            (noetherianModuleDecodeBHist (noetherianModuleEncodeBHist P))
            (noetherianModuleDecodeBHist (noetherianModuleEncodeBHist N))) =
          some (NoetherianModuleUp.mk M R I A G H Q P N)
      rw [NoetherianModuleTasteGate_single_carrier_alignment_decode_encode M,
        NoetherianModuleTasteGate_single_carrier_alignment_decode_encode R,
        NoetherianModuleTasteGate_single_carrier_alignment_decode_encode I,
        NoetherianModuleTasteGate_single_carrier_alignment_decode_encode A,
        NoetherianModuleTasteGate_single_carrier_alignment_decode_encode G,
        NoetherianModuleTasteGate_single_carrier_alignment_decode_encode H,
        NoetherianModuleTasteGate_single_carrier_alignment_decode_encode Q,
        NoetherianModuleTasteGate_single_carrier_alignment_decode_encode P,
        NoetherianModuleTasteGate_single_carrier_alignment_decode_encode N]

private theorem NoetherianModuleTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : NoetherianModuleUp} :
    noetherianModuleToEventFlow x = noetherianModuleToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      noetherianModuleFromEventFlow (noetherianModuleToEventFlow x) =
        noetherianModuleFromEventFlow (noetherianModuleToEventFlow y) :=
    congrArg noetherianModuleFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (NoetherianModuleTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (NoetherianModuleTasteGate_single_carrier_alignment_round_trip y)))

instance noetherianModuleBHistCarrier : BHistCarrier NoetherianModuleUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := noetherianModuleToEventFlow
  fromEventFlow := noetherianModuleFromEventFlow

instance noetherianModuleChapterTasteGate : ChapterTasteGate NoetherianModuleUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change noetherianModuleFromEventFlow (noetherianModuleToEventFlow x) = some x
    exact NoetherianModuleTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (NoetherianModuleTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem NoetherianModuleTasteGate_single_carrier_alignment :
    (∀ h : BHist, noetherianModuleDecodeBHist (noetherianModuleEncodeBHist h) = h) ∧
      (∀ x : NoetherianModuleUp,
        noetherianModuleFromEventFlow (noetherianModuleToEventFlow x) = some x) ∧
        (∀ x y : NoetherianModuleUp,
          noetherianModuleToEventFlow x = noetherianModuleToEventFlow y → x = y) ∧
          noetherianModuleEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨NoetherianModuleTasteGate_single_carrier_alignment_decode_encode,
      NoetherianModuleTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        NoetherianModuleTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end TasteGate
end BEDC.Derived.NoetherianModuleUp
