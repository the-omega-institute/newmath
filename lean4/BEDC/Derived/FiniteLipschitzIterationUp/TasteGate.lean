import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteLipschitzIterationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteLipschitzIterationUp : Type where
  | mk (X d f L q n x0 W B H C P N : BHist) : FiniteLipschitzIterationUp
  deriving DecidableEq

def finiteLipschitzIterationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteLipschitzIterationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteLipschitzIterationEncodeBHist h

def finiteLipschitzIterationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteLipschitzIterationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteLipschitzIterationDecodeBHist tail)

private theorem FiniteLipschitzIterationTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      finiteLipschitzIterationDecodeBHist (finiteLipschitzIterationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteLipschitzIterationFields : FiniteLipschitzIterationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteLipschitzIterationUp.mk X d f L q n x0 W B H C P N =>
      [X, d, f, L, q, n, x0, W, B, H, C, P, N]

def finiteLipschitzIterationToEventFlow : FiniteLipschitzIterationUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (finiteLipschitzIterationFields x).map finiteLipschitzIterationEncodeBHist

private def finiteLipschitzIterationEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => finiteLipschitzIterationEventAtDefault index rest

def finiteLipschitzIterationFromEventFlow :
    EventFlow → Option FiniteLipschitzIterationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (FiniteLipschitzIterationUp.mk
        (finiteLipschitzIterationDecodeBHist (finiteLipschitzIterationEventAtDefault 0 ef))
        (finiteLipschitzIterationDecodeBHist (finiteLipschitzIterationEventAtDefault 1 ef))
        (finiteLipschitzIterationDecodeBHist (finiteLipschitzIterationEventAtDefault 2 ef))
        (finiteLipschitzIterationDecodeBHist (finiteLipschitzIterationEventAtDefault 3 ef))
        (finiteLipschitzIterationDecodeBHist (finiteLipschitzIterationEventAtDefault 4 ef))
        (finiteLipschitzIterationDecodeBHist (finiteLipschitzIterationEventAtDefault 5 ef))
        (finiteLipschitzIterationDecodeBHist (finiteLipschitzIterationEventAtDefault 6 ef))
        (finiteLipschitzIterationDecodeBHist (finiteLipschitzIterationEventAtDefault 7 ef))
        (finiteLipschitzIterationDecodeBHist (finiteLipschitzIterationEventAtDefault 8 ef))
        (finiteLipschitzIterationDecodeBHist (finiteLipschitzIterationEventAtDefault 9 ef))
        (finiteLipschitzIterationDecodeBHist (finiteLipschitzIterationEventAtDefault 10 ef))
        (finiteLipschitzIterationDecodeBHist (finiteLipschitzIterationEventAtDefault 11 ef))
        (finiteLipschitzIterationDecodeBHist (finiteLipschitzIterationEventAtDefault 12 ef)))

private theorem FiniteLipschitzIterationTasteGate_single_carrier_alignment_round_trip :
    ∀ x : FiniteLipschitzIterationUp,
      finiteLipschitzIterationFromEventFlow (finiteLipschitzIterationToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X d f L q n x0 W B H C P N =>
      change
        some
          (FiniteLipschitzIterationUp.mk
            (finiteLipschitzIterationDecodeBHist (finiteLipschitzIterationEncodeBHist X))
            (finiteLipschitzIterationDecodeBHist (finiteLipschitzIterationEncodeBHist d))
            (finiteLipschitzIterationDecodeBHist (finiteLipschitzIterationEncodeBHist f))
            (finiteLipschitzIterationDecodeBHist (finiteLipschitzIterationEncodeBHist L))
            (finiteLipschitzIterationDecodeBHist (finiteLipschitzIterationEncodeBHist q))
            (finiteLipschitzIterationDecodeBHist (finiteLipschitzIterationEncodeBHist n))
            (finiteLipschitzIterationDecodeBHist (finiteLipschitzIterationEncodeBHist x0))
            (finiteLipschitzIterationDecodeBHist (finiteLipschitzIterationEncodeBHist W))
            (finiteLipschitzIterationDecodeBHist (finiteLipschitzIterationEncodeBHist B))
            (finiteLipschitzIterationDecodeBHist (finiteLipschitzIterationEncodeBHist H))
            (finiteLipschitzIterationDecodeBHist (finiteLipschitzIterationEncodeBHist C))
            (finiteLipschitzIterationDecodeBHist (finiteLipschitzIterationEncodeBHist P))
            (finiteLipschitzIterationDecodeBHist (finiteLipschitzIterationEncodeBHist N))) =
          some (FiniteLipschitzIterationUp.mk X d f L q n x0 W B H C P N)
      rw [FiniteLipschitzIterationTasteGate_single_carrier_alignment_decode X,
        FiniteLipschitzIterationTasteGate_single_carrier_alignment_decode d,
        FiniteLipschitzIterationTasteGate_single_carrier_alignment_decode f,
        FiniteLipschitzIterationTasteGate_single_carrier_alignment_decode L,
        FiniteLipschitzIterationTasteGate_single_carrier_alignment_decode q,
        FiniteLipschitzIterationTasteGate_single_carrier_alignment_decode n,
        FiniteLipschitzIterationTasteGate_single_carrier_alignment_decode x0,
        FiniteLipschitzIterationTasteGate_single_carrier_alignment_decode W,
        FiniteLipschitzIterationTasteGate_single_carrier_alignment_decode B,
        FiniteLipschitzIterationTasteGate_single_carrier_alignment_decode H,
        FiniteLipschitzIterationTasteGate_single_carrier_alignment_decode C,
        FiniteLipschitzIterationTasteGate_single_carrier_alignment_decode P,
        FiniteLipschitzIterationTasteGate_single_carrier_alignment_decode N]

private theorem FiniteLipschitzIterationTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : FiniteLipschitzIterationUp} :
    finiteLipschitzIterationToEventFlow x = finiteLipschitzIterationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteLipschitzIterationFromEventFlow (finiteLipschitzIterationToEventFlow x) =
        finiteLipschitzIterationFromEventFlow (finiteLipschitzIterationToEventFlow y) :=
    congrArg finiteLipschitzIterationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (FiniteLipschitzIterationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (FiniteLipschitzIterationTasteGate_single_carrier_alignment_round_trip y)))

instance finiteLipschitzIterationBHistCarrier : BHistCarrier FiniteLipschitzIterationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteLipschitzIterationToEventFlow
  fromEventFlow := finiteLipschitzIterationFromEventFlow

instance finiteLipschitzIterationChapterTasteGate :
    ChapterTasteGate FiniteLipschitzIterationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finiteLipschitzIterationFromEventFlow (finiteLipschitzIterationToEventFlow x) =
      some x
    exact FiniteLipschitzIterationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (FiniteLipschitzIterationTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate FiniteLipschitzIterationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteLipschitzIterationChapterTasteGate

theorem FiniteLipschitzIterationTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      finiteLipschitzIterationDecodeBHist (finiteLipschitzIterationEncodeBHist h) = h) ∧
      (∀ x : FiniteLipschitzIterationUp,
        finiteLipschitzIterationFromEventFlow (finiteLipschitzIterationToEventFlow x) =
          some x) ∧
        (∀ x y : FiniteLipschitzIterationUp,
          finiteLipschitzIterationToEventFlow x = finiteLipschitzIterationToEventFlow y →
            x = y) ∧
          finiteLipschitzIterationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨FiniteLipschitzIterationTasteGate_single_carrier_alignment_decode,
      FiniteLipschitzIterationTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        FiniteLipschitzIterationTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.FiniteLipschitzIterationUp
