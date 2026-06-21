import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SignedDecimalExpansionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SignedDecimalExpansionUp : Type where
  | mk (S D W A L U Z R E H C P N : BHist) : SignedDecimalExpansionUp
  deriving DecidableEq

def signedDecimalExpansionEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: signedDecimalExpansionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: signedDecimalExpansionEncodeBHist h

def signedDecimalExpansionDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (signedDecimalExpansionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (signedDecimalExpansionDecodeBHist tail)

private theorem SignedDecimalExpansionTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      signedDecimalExpansionDecodeBHist
        (signedDecimalExpansionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def signedDecimalExpansionFields :
    SignedDecimalExpansionUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SignedDecimalExpansionUp.mk S D W A L U Z R E H C P N =>
      [S, D, W, A, L, U, Z, R, E, H, C, P, N]

def signedDecimalExpansionToEventFlow :
    SignedDecimalExpansionUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (signedDecimalExpansionFields x).map
      signedDecimalExpansionEncodeBHist

private def signedDecimalExpansionEventAtDefault :
    Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      signedDecimalExpansionEventAtDefault index rest

def signedDecimalExpansionFromEventFlow
    (ef : EventFlow) : Option SignedDecimalExpansionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SignedDecimalExpansionUp.mk
      (signedDecimalExpansionDecodeBHist
        (signedDecimalExpansionEventAtDefault 0 ef))
      (signedDecimalExpansionDecodeBHist
        (signedDecimalExpansionEventAtDefault 1 ef))
      (signedDecimalExpansionDecodeBHist
        (signedDecimalExpansionEventAtDefault 2 ef))
      (signedDecimalExpansionDecodeBHist
        (signedDecimalExpansionEventAtDefault 3 ef))
      (signedDecimalExpansionDecodeBHist
        (signedDecimalExpansionEventAtDefault 4 ef))
      (signedDecimalExpansionDecodeBHist
        (signedDecimalExpansionEventAtDefault 5 ef))
      (signedDecimalExpansionDecodeBHist
        (signedDecimalExpansionEventAtDefault 6 ef))
      (signedDecimalExpansionDecodeBHist
        (signedDecimalExpansionEventAtDefault 7 ef))
      (signedDecimalExpansionDecodeBHist
        (signedDecimalExpansionEventAtDefault 8 ef))
      (signedDecimalExpansionDecodeBHist
        (signedDecimalExpansionEventAtDefault 9 ef))
      (signedDecimalExpansionDecodeBHist
        (signedDecimalExpansionEventAtDefault 10 ef))
      (signedDecimalExpansionDecodeBHist
        (signedDecimalExpansionEventAtDefault 11 ef))
      (signedDecimalExpansionDecodeBHist
        (signedDecimalExpansionEventAtDefault 12 ef)))

private theorem SignedDecimalExpansionTasteGate_single_carrier_alignment_round_trip :
    forall x : SignedDecimalExpansionUp,
      signedDecimalExpansionFromEventFlow
        (signedDecimalExpansionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk S D W A L U Z R E H C P N =>
      change
        some
          (SignedDecimalExpansionUp.mk
            (signedDecimalExpansionDecodeBHist
              (signedDecimalExpansionEncodeBHist S))
            (signedDecimalExpansionDecodeBHist
              (signedDecimalExpansionEncodeBHist D))
            (signedDecimalExpansionDecodeBHist
              (signedDecimalExpansionEncodeBHist W))
            (signedDecimalExpansionDecodeBHist
              (signedDecimalExpansionEncodeBHist A))
            (signedDecimalExpansionDecodeBHist
              (signedDecimalExpansionEncodeBHist L))
            (signedDecimalExpansionDecodeBHist
              (signedDecimalExpansionEncodeBHist U))
            (signedDecimalExpansionDecodeBHist
              (signedDecimalExpansionEncodeBHist Z))
            (signedDecimalExpansionDecodeBHist
              (signedDecimalExpansionEncodeBHist R))
            (signedDecimalExpansionDecodeBHist
              (signedDecimalExpansionEncodeBHist E))
            (signedDecimalExpansionDecodeBHist
              (signedDecimalExpansionEncodeBHist H))
            (signedDecimalExpansionDecodeBHist
              (signedDecimalExpansionEncodeBHist C))
            (signedDecimalExpansionDecodeBHist
              (signedDecimalExpansionEncodeBHist P))
            (signedDecimalExpansionDecodeBHist
              (signedDecimalExpansionEncodeBHist N))) =
          some (SignedDecimalExpansionUp.mk S D W A L U Z R E H C P N)
      rw [
        SignedDecimalExpansionTasteGate_single_carrier_alignment_decode S,
        SignedDecimalExpansionTasteGate_single_carrier_alignment_decode D,
        SignedDecimalExpansionTasteGate_single_carrier_alignment_decode W,
        SignedDecimalExpansionTasteGate_single_carrier_alignment_decode A,
        SignedDecimalExpansionTasteGate_single_carrier_alignment_decode L,
        SignedDecimalExpansionTasteGate_single_carrier_alignment_decode U,
        SignedDecimalExpansionTasteGate_single_carrier_alignment_decode Z,
        SignedDecimalExpansionTasteGate_single_carrier_alignment_decode R,
        SignedDecimalExpansionTasteGate_single_carrier_alignment_decode E,
        SignedDecimalExpansionTasteGate_single_carrier_alignment_decode H,
        SignedDecimalExpansionTasteGate_single_carrier_alignment_decode C,
        SignedDecimalExpansionTasteGate_single_carrier_alignment_decode P,
        SignedDecimalExpansionTasteGate_single_carrier_alignment_decode N]

private theorem SignedDecimalExpansionTasteGate_single_carrier_alignment_injective
    {x y : SignedDecimalExpansionUp} :
    signedDecimalExpansionToEventFlow x =
        signedDecimalExpansionToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      signedDecimalExpansionFromEventFlow
          (signedDecimalExpansionToEventFlow x) =
        signedDecimalExpansionFromEventFlow
          (signedDecimalExpansionToEventFlow y) :=
    congrArg signedDecimalExpansionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (SignedDecimalExpansionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (SignedDecimalExpansionTasteGate_single_carrier_alignment_round_trip y)))

instance signedDecimalExpansionBHistCarrier :
    BHistCarrier SignedDecimalExpansionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := signedDecimalExpansionToEventFlow
  fromEventFlow := signedDecimalExpansionFromEventFlow

instance signedDecimalExpansionChapterTasteGate :
    ChapterTasteGate SignedDecimalExpansionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      signedDecimalExpansionFromEventFlow
        (signedDecimalExpansionToEventFlow x) = some x
    exact SignedDecimalExpansionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (SignedDecimalExpansionTasteGate_single_carrier_alignment_injective heq)

def taste_gate : ChapterTasteGate SignedDecimalExpansionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  signedDecimalExpansionChapterTasteGate

theorem SignedDecimalExpansionTasteGate_single_carrier_alignment :
    (forall h : BHist,
      signedDecimalExpansionDecodeBHist
        (signedDecimalExpansionEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier SignedDecimalExpansionUp) ∧
      Nonempty (ChapterTasteGate SignedDecimalExpansionUp) ∧
      signedDecimalExpansionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact SignedDecimalExpansionTasteGate_single_carrier_alignment_decode
  · constructor
    · exact ⟨signedDecimalExpansionBHistCarrier⟩
    · constructor
      · exact ⟨signedDecimalExpansionChapterTasteGate⟩
      · rfl

end BEDC.Derived.SignedDecimalExpansionUp
