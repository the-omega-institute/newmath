import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SeparatedCompletionFunctorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SeparatedCompletionFunctorUp : Type where
  | mk (M N f S T R L W Q A H C P E : BHist) : SeparatedCompletionFunctorUp
  deriving DecidableEq

def separatedCompletionFunctorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: separatedCompletionFunctorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: separatedCompletionFunctorEncodeBHist h

def separatedCompletionFunctorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (separatedCompletionFunctorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (separatedCompletionFunctorDecodeBHist tail)

private theorem SeparatedCompletionFunctorTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      separatedCompletionFunctorDecodeBHist
          (separatedCompletionFunctorEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def separatedCompletionFunctorFields :
    SeparatedCompletionFunctorUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SeparatedCompletionFunctorUp.mk M N f S T R L W Q A H C P E =>
      [M, N, f, S, T, R, L, W, Q, A, H, C, P, E]

def separatedCompletionFunctorToEventFlow :
    SeparatedCompletionFunctorUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (separatedCompletionFunctorFields x).map separatedCompletionFunctorEncodeBHist

private def separatedCompletionFunctorEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => separatedCompletionFunctorEventAtDefault index rest

def separatedCompletionFunctorFromEventFlow
    (ef : EventFlow) : Option SeparatedCompletionFunctorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SeparatedCompletionFunctorUp.mk
      (separatedCompletionFunctorDecodeBHist
        (separatedCompletionFunctorEventAtDefault 0 ef))
      (separatedCompletionFunctorDecodeBHist
        (separatedCompletionFunctorEventAtDefault 1 ef))
      (separatedCompletionFunctorDecodeBHist
        (separatedCompletionFunctorEventAtDefault 2 ef))
      (separatedCompletionFunctorDecodeBHist
        (separatedCompletionFunctorEventAtDefault 3 ef))
      (separatedCompletionFunctorDecodeBHist
        (separatedCompletionFunctorEventAtDefault 4 ef))
      (separatedCompletionFunctorDecodeBHist
        (separatedCompletionFunctorEventAtDefault 5 ef))
      (separatedCompletionFunctorDecodeBHist
        (separatedCompletionFunctorEventAtDefault 6 ef))
      (separatedCompletionFunctorDecodeBHist
        (separatedCompletionFunctorEventAtDefault 7 ef))
      (separatedCompletionFunctorDecodeBHist
        (separatedCompletionFunctorEventAtDefault 8 ef))
      (separatedCompletionFunctorDecodeBHist
        (separatedCompletionFunctorEventAtDefault 9 ef))
      (separatedCompletionFunctorDecodeBHist
        (separatedCompletionFunctorEventAtDefault 10 ef))
      (separatedCompletionFunctorDecodeBHist
        (separatedCompletionFunctorEventAtDefault 11 ef))
      (separatedCompletionFunctorDecodeBHist
        (separatedCompletionFunctorEventAtDefault 12 ef))
      (separatedCompletionFunctorDecodeBHist
        (separatedCompletionFunctorEventAtDefault 13 ef)))

private theorem SeparatedCompletionFunctorTasteGate_single_carrier_alignment_round_trip :
    ∀ x : SeparatedCompletionFunctorUp,
      separatedCompletionFunctorFromEventFlow
          (separatedCompletionFunctorToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M N f S T R L W Q A H C P E =>
      change
        some
          (SeparatedCompletionFunctorUp.mk
            (separatedCompletionFunctorDecodeBHist
              (separatedCompletionFunctorEncodeBHist M))
            (separatedCompletionFunctorDecodeBHist
              (separatedCompletionFunctorEncodeBHist N))
            (separatedCompletionFunctorDecodeBHist
              (separatedCompletionFunctorEncodeBHist f))
            (separatedCompletionFunctorDecodeBHist
              (separatedCompletionFunctorEncodeBHist S))
            (separatedCompletionFunctorDecodeBHist
              (separatedCompletionFunctorEncodeBHist T))
            (separatedCompletionFunctorDecodeBHist
              (separatedCompletionFunctorEncodeBHist R))
            (separatedCompletionFunctorDecodeBHist
              (separatedCompletionFunctorEncodeBHist L))
            (separatedCompletionFunctorDecodeBHist
              (separatedCompletionFunctorEncodeBHist W))
            (separatedCompletionFunctorDecodeBHist
              (separatedCompletionFunctorEncodeBHist Q))
            (separatedCompletionFunctorDecodeBHist
              (separatedCompletionFunctorEncodeBHist A))
            (separatedCompletionFunctorDecodeBHist
              (separatedCompletionFunctorEncodeBHist H))
            (separatedCompletionFunctorDecodeBHist
              (separatedCompletionFunctorEncodeBHist C))
            (separatedCompletionFunctorDecodeBHist
              (separatedCompletionFunctorEncodeBHist P))
            (separatedCompletionFunctorDecodeBHist
              (separatedCompletionFunctorEncodeBHist E))) =
          some (SeparatedCompletionFunctorUp.mk M N f S T R L W Q A H C P E)
      rw [SeparatedCompletionFunctorTasteGate_single_carrier_alignment_decode M,
        SeparatedCompletionFunctorTasteGate_single_carrier_alignment_decode N,
        SeparatedCompletionFunctorTasteGate_single_carrier_alignment_decode f,
        SeparatedCompletionFunctorTasteGate_single_carrier_alignment_decode S,
        SeparatedCompletionFunctorTasteGate_single_carrier_alignment_decode T,
        SeparatedCompletionFunctorTasteGate_single_carrier_alignment_decode R,
        SeparatedCompletionFunctorTasteGate_single_carrier_alignment_decode L,
        SeparatedCompletionFunctorTasteGate_single_carrier_alignment_decode W,
        SeparatedCompletionFunctorTasteGate_single_carrier_alignment_decode Q,
        SeparatedCompletionFunctorTasteGate_single_carrier_alignment_decode A,
        SeparatedCompletionFunctorTasteGate_single_carrier_alignment_decode H,
        SeparatedCompletionFunctorTasteGate_single_carrier_alignment_decode C,
        SeparatedCompletionFunctorTasteGate_single_carrier_alignment_decode P,
        SeparatedCompletionFunctorTasteGate_single_carrier_alignment_decode E]

private theorem SeparatedCompletionFunctorTasteGate_single_carrier_alignment_injective
    {x y : SeparatedCompletionFunctorUp} :
    separatedCompletionFunctorToEventFlow x =
        separatedCompletionFunctorToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      separatedCompletionFunctorFromEventFlow
          (separatedCompletionFunctorToEventFlow x) =
        separatedCompletionFunctorFromEventFlow
          (separatedCompletionFunctorToEventFlow y) :=
    congrArg separatedCompletionFunctorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (SeparatedCompletionFunctorTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (SeparatedCompletionFunctorTasteGate_single_carrier_alignment_round_trip y)))

instance separatedCompletionFunctorBHistCarrier :
    BHistCarrier SeparatedCompletionFunctorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := separatedCompletionFunctorToEventFlow
  fromEventFlow := separatedCompletionFunctorFromEventFlow

instance separatedCompletionFunctorChapterTasteGate :
    ChapterTasteGate SeparatedCompletionFunctorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      separatedCompletionFunctorFromEventFlow
          (separatedCompletionFunctorToEventFlow x) =
        some x
    exact SeparatedCompletionFunctorTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (SeparatedCompletionFunctorTasteGate_single_carrier_alignment_injective heq)

theorem SeparatedCompletionFunctorTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      separatedCompletionFunctorDecodeBHist
          (separatedCompletionFunctorEncodeBHist h) =
        h) ∧
      Nonempty (BHistCarrier SeparatedCompletionFunctorUp) ∧
        Nonempty (ChapterTasteGate SeparatedCompletionFunctorUp) ∧
          separatedCompletionFunctorEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark BHistCarrier ChapterTasteGate
  exact
    ⟨SeparatedCompletionFunctorTasteGate_single_carrier_alignment_decode,
      ⟨separatedCompletionFunctorBHistCarrier⟩,
      ⟨separatedCompletionFunctorChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.SeparatedCompletionFunctorUp
