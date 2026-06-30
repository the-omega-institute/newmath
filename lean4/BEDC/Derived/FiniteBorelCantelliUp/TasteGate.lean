import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteBorelCantelliUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteBorelCantelliUp : Type where
  | mk (A M U S L E H C P N : BHist) : FiniteBorelCantelliUp
  deriving DecidableEq

def FiniteBorelCantelliTasteGate_single_carrier_alignment_encodeBHist :
    BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: FiniteBorelCantelliTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: FiniteBorelCantelliTasteGate_single_carrier_alignment_encodeBHist h

def FiniteBorelCantelliTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0 (FiniteBorelCantelliTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1 (FiniteBorelCantelliTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem FiniteBorelCantelliTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      FiniteBorelCantelliTasteGate_single_carrier_alignment_decodeBHist
        (FiniteBorelCantelliTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def FiniteBorelCantelliTasteGate_single_carrier_alignment_fields :
    FiniteBorelCantelliUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteBorelCantelliUp.mk A M U S L E H C P N => [A, M, U, S, L, E, H, C, P, N]

def FiniteBorelCantelliTasteGate_single_carrier_alignment_toEventFlow :
    FiniteBorelCantelliUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (FiniteBorelCantelliTasteGate_single_carrier_alignment_fields x).map
      FiniteBorelCantelliTasteGate_single_carrier_alignment_encodeBHist

private def FiniteBorelCantelliTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      FiniteBorelCantelliTasteGate_single_carrier_alignment_eventAt index rest

def FiniteBorelCantelliTasteGate_single_carrier_alignment_fromEventFlow
    (ef : EventFlow) : Option FiniteBorelCantelliUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FiniteBorelCantelliUp.mk
      (FiniteBorelCantelliTasteGate_single_carrier_alignment_decodeBHist
        (FiniteBorelCantelliTasteGate_single_carrier_alignment_eventAt 0 ef))
      (FiniteBorelCantelliTasteGate_single_carrier_alignment_decodeBHist
        (FiniteBorelCantelliTasteGate_single_carrier_alignment_eventAt 1 ef))
      (FiniteBorelCantelliTasteGate_single_carrier_alignment_decodeBHist
        (FiniteBorelCantelliTasteGate_single_carrier_alignment_eventAt 2 ef))
      (FiniteBorelCantelliTasteGate_single_carrier_alignment_decodeBHist
        (FiniteBorelCantelliTasteGate_single_carrier_alignment_eventAt 3 ef))
      (FiniteBorelCantelliTasteGate_single_carrier_alignment_decodeBHist
        (FiniteBorelCantelliTasteGate_single_carrier_alignment_eventAt 4 ef))
      (FiniteBorelCantelliTasteGate_single_carrier_alignment_decodeBHist
        (FiniteBorelCantelliTasteGate_single_carrier_alignment_eventAt 5 ef))
      (FiniteBorelCantelliTasteGate_single_carrier_alignment_decodeBHist
        (FiniteBorelCantelliTasteGate_single_carrier_alignment_eventAt 6 ef))
      (FiniteBorelCantelliTasteGate_single_carrier_alignment_decodeBHist
        (FiniteBorelCantelliTasteGate_single_carrier_alignment_eventAt 7 ef))
      (FiniteBorelCantelliTasteGate_single_carrier_alignment_decodeBHist
        (FiniteBorelCantelliTasteGate_single_carrier_alignment_eventAt 8 ef))
      (FiniteBorelCantelliTasteGate_single_carrier_alignment_decodeBHist
        (FiniteBorelCantelliTasteGate_single_carrier_alignment_eventAt 9 ef)))

private theorem FiniteBorelCantelliTasteGate_single_carrier_alignment_round_trip :
    ∀ x : FiniteBorelCantelliUp,
      FiniteBorelCantelliTasteGate_single_carrier_alignment_fromEventFlow
        (FiniteBorelCantelliTasteGate_single_carrier_alignment_toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A M U S L E H C P N =>
      change
        some
          (FiniteBorelCantelliUp.mk
            (FiniteBorelCantelliTasteGate_single_carrier_alignment_decodeBHist
              (FiniteBorelCantelliTasteGate_single_carrier_alignment_encodeBHist A))
            (FiniteBorelCantelliTasteGate_single_carrier_alignment_decodeBHist
              (FiniteBorelCantelliTasteGate_single_carrier_alignment_encodeBHist M))
            (FiniteBorelCantelliTasteGate_single_carrier_alignment_decodeBHist
              (FiniteBorelCantelliTasteGate_single_carrier_alignment_encodeBHist U))
            (FiniteBorelCantelliTasteGate_single_carrier_alignment_decodeBHist
              (FiniteBorelCantelliTasteGate_single_carrier_alignment_encodeBHist S))
            (FiniteBorelCantelliTasteGate_single_carrier_alignment_decodeBHist
              (FiniteBorelCantelliTasteGate_single_carrier_alignment_encodeBHist L))
            (FiniteBorelCantelliTasteGate_single_carrier_alignment_decodeBHist
              (FiniteBorelCantelliTasteGate_single_carrier_alignment_encodeBHist E))
            (FiniteBorelCantelliTasteGate_single_carrier_alignment_decodeBHist
              (FiniteBorelCantelliTasteGate_single_carrier_alignment_encodeBHist H))
            (FiniteBorelCantelliTasteGate_single_carrier_alignment_decodeBHist
              (FiniteBorelCantelliTasteGate_single_carrier_alignment_encodeBHist C))
            (FiniteBorelCantelliTasteGate_single_carrier_alignment_decodeBHist
              (FiniteBorelCantelliTasteGate_single_carrier_alignment_encodeBHist P))
            (FiniteBorelCantelliTasteGate_single_carrier_alignment_decodeBHist
              (FiniteBorelCantelliTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (FiniteBorelCantelliUp.mk A M U S L E H C P N)
      rw [FiniteBorelCantelliTasteGate_single_carrier_alignment_decode A,
        FiniteBorelCantelliTasteGate_single_carrier_alignment_decode M,
        FiniteBorelCantelliTasteGate_single_carrier_alignment_decode U,
        FiniteBorelCantelliTasteGate_single_carrier_alignment_decode S,
        FiniteBorelCantelliTasteGate_single_carrier_alignment_decode L,
        FiniteBorelCantelliTasteGate_single_carrier_alignment_decode E,
        FiniteBorelCantelliTasteGate_single_carrier_alignment_decode H,
        FiniteBorelCantelliTasteGate_single_carrier_alignment_decode C,
        FiniteBorelCantelliTasteGate_single_carrier_alignment_decode P,
        FiniteBorelCantelliTasteGate_single_carrier_alignment_decode N]

private theorem FiniteBorelCantelliTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : FiniteBorelCantelliUp} :
    FiniteBorelCantelliTasteGate_single_carrier_alignment_toEventFlow x =
      FiniteBorelCantelliTasteGate_single_carrier_alignment_toEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      FiniteBorelCantelliTasteGate_single_carrier_alignment_fromEventFlow
          (FiniteBorelCantelliTasteGate_single_carrier_alignment_toEventFlow x) =
        FiniteBorelCantelliTasteGate_single_carrier_alignment_fromEventFlow
          (FiniteBorelCantelliTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg FiniteBorelCantelliTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (FiniteBorelCantelliTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (FiniteBorelCantelliTasteGate_single_carrier_alignment_round_trip y)))

instance finiteBorelCantelliBHistCarrier : BHistCarrier FiniteBorelCantelliUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := FiniteBorelCantelliTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := FiniteBorelCantelliTasteGate_single_carrier_alignment_fromEventFlow

instance finiteBorelCantelliChapterTasteGate : ChapterTasteGate FiniteBorelCantelliUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      FiniteBorelCantelliTasteGate_single_carrier_alignment_fromEventFlow
        (FiniteBorelCantelliTasteGate_single_carrier_alignment_toEventFlow x) = some x
    exact FiniteBorelCantelliTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FiniteBorelCantelliTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem FiniteBorelCantelliTasteGate_single_carrier_alignment :
    (∀ A M U S L E H C P N : BHist,
      FiniteBorelCantelliTasteGate_single_carrier_alignment_fields
        (FiniteBorelCantelliUp.mk A M U S L E H C P N) =
        [A, M, U, S, L, E, H, C, P, N]) ∧
      (∀ h : BHist,
        FiniteBorelCantelliTasteGate_single_carrier_alignment_decodeBHist
          (FiniteBorelCantelliTasteGate_single_carrier_alignment_encodeBHist h) = h) ∧
        FiniteBorelCantelliTasteGate_single_carrier_alignment_encodeBHist
          (BHist.e1 BHist.Empty) = [BMark.b1] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨(by intro A M U S L E H C P N; rfl),
      FiniteBorelCantelliTasteGate_single_carrier_alignment_decode,
      rfl⟩

end BEDC.Derived.FiniteBorelCantelliUp
