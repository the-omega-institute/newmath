import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RadonTheoremUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RadonTheoremUp : Type where
  | mk (A F D L U V H Q P N : BHist) : RadonTheoremUp
  deriving DecidableEq

def radonTheoremEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: radonTheoremEncodeBHist h
  | BHist.e1 h => BMark.b1 :: radonTheoremEncodeBHist h

def radonTheoremDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (radonTheoremDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (radonTheoremDecodeBHist tail)

private theorem RadonTheoremTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, radonTheoremDecodeBHist (radonTheoremEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def radonTheoremFields : RadonTheoremUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RadonTheoremUp.mk A F D L U V H Q P N => [A, F, D, L, U, V, H, Q, P, N]

def radonTheoremToEventFlow : RadonTheoremUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map radonTheoremEncodeBHist (radonTheoremFields x)

def radonTheoremFromEventFlow (ef : EventFlow) : Option RadonTheoremUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match ef with
  | [A, F, D, L, U, V, H, Q, P, N] =>
      some
        (RadonTheoremUp.mk
          (radonTheoremDecodeBHist A)
          (radonTheoremDecodeBHist F)
          (radonTheoremDecodeBHist D)
          (radonTheoremDecodeBHist L)
          (radonTheoremDecodeBHist U)
          (radonTheoremDecodeBHist V)
          (radonTheoremDecodeBHist H)
          (radonTheoremDecodeBHist Q)
          (radonTheoremDecodeBHist P)
          (radonTheoremDecodeBHist N))
  | _ => none

private theorem RadonTheoremTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RadonTheoremUp,
      radonTheoremFromEventFlow (radonTheoremToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A F D L U V H Q P N =>
      change
        some
            (RadonTheoremUp.mk
              (radonTheoremDecodeBHist (radonTheoremEncodeBHist A))
              (radonTheoremDecodeBHist (radonTheoremEncodeBHist F))
              (radonTheoremDecodeBHist (radonTheoremEncodeBHist D))
              (radonTheoremDecodeBHist (radonTheoremEncodeBHist L))
              (radonTheoremDecodeBHist (radonTheoremEncodeBHist U))
              (radonTheoremDecodeBHist (radonTheoremEncodeBHist V))
              (radonTheoremDecodeBHist (radonTheoremEncodeBHist H))
              (radonTheoremDecodeBHist (radonTheoremEncodeBHist Q))
              (radonTheoremDecodeBHist (radonTheoremEncodeBHist P))
              (radonTheoremDecodeBHist (radonTheoremEncodeBHist N))) =
          some (RadonTheoremUp.mk A F D L U V H Q P N)
      rw [RadonTheoremTasteGate_single_carrier_alignment_decode A,
        RadonTheoremTasteGate_single_carrier_alignment_decode F,
        RadonTheoremTasteGate_single_carrier_alignment_decode D,
        RadonTheoremTasteGate_single_carrier_alignment_decode L,
        RadonTheoremTasteGate_single_carrier_alignment_decode U,
        RadonTheoremTasteGate_single_carrier_alignment_decode V,
        RadonTheoremTasteGate_single_carrier_alignment_decode H,
        RadonTheoremTasteGate_single_carrier_alignment_decode Q,
        RadonTheoremTasteGate_single_carrier_alignment_decode P,
        RadonTheoremTasteGate_single_carrier_alignment_decode N]

private theorem radonTheoremToEventFlow_injective {x y : RadonTheoremUp} :
    radonTheoremToEventFlow x = radonTheoremToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      radonTheoremFromEventFlow (radonTheoremToEventFlow x) =
        radonTheoremFromEventFlow (radonTheoremToEventFlow y) :=
    congrArg radonTheoremFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RadonTheoremTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RadonTheoremTasteGate_single_carrier_alignment_round_trip y)))

instance radonTheoremBHistCarrier : BHistCarrier RadonTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := radonTheoremToEventFlow
  fromEventFlow := radonTheoremFromEventFlow

instance radonTheoremChapterTasteGate : ChapterTasteGate RadonTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change radonTheoremFromEventFlow (radonTheoremToEventFlow x) = some x
    exact RadonTheoremTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (radonTheoremToEventFlow_injective heq)

theorem RadonTheoremTasteGate_single_carrier_alignment :
    (∀ h : BHist, radonTheoremDecodeBHist (radonTheoremEncodeBHist h) = h) ∧
      (∀ x : RadonTheoremUp,
        radonTheoremToEventFlow x = List.map radonTheoremEncodeBHist
          (radonTheoremFields x)) ∧
          radonTheoremEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨RadonTheoremTasteGate_single_carrier_alignment_decode,
      (fun _ => rfl),
      rfl⟩

end BEDC.Derived.RadonTheoremUp
