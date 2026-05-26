import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SignedDistanceUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SignedDistanceUp : Type where
  | mk (M L A D R E H C P N : BHist) : SignedDistanceUp
  deriving DecidableEq

def signedDistanceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: signedDistanceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: signedDistanceEncodeBHist h

def signedDistanceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (signedDistanceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (signedDistanceDecodeBHist tail)

private theorem SignedDistanceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, signedDistanceDecodeBHist (signedDistanceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def signedDistanceFields : SignedDistanceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SignedDistanceUp.mk M L A D R E H C P N => [M, L, A, D, R, E, H, C, P, N]

def signedDistanceToEventFlow : SignedDistanceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (signedDistanceFields x).map signedDistanceEncodeBHist

private def SignedDistanceTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      SignedDistanceTasteGate_single_carrier_alignment_eventAt index rest

def signedDistanceFromEventFlow (ef : EventFlow) : Option SignedDistanceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SignedDistanceUp.mk
      (signedDistanceDecodeBHist (SignedDistanceTasteGate_single_carrier_alignment_eventAt 0 ef))
      (signedDistanceDecodeBHist (SignedDistanceTasteGate_single_carrier_alignment_eventAt 1 ef))
      (signedDistanceDecodeBHist (SignedDistanceTasteGate_single_carrier_alignment_eventAt 2 ef))
      (signedDistanceDecodeBHist (SignedDistanceTasteGate_single_carrier_alignment_eventAt 3 ef))
      (signedDistanceDecodeBHist (SignedDistanceTasteGate_single_carrier_alignment_eventAt 4 ef))
      (signedDistanceDecodeBHist (SignedDistanceTasteGate_single_carrier_alignment_eventAt 5 ef))
      (signedDistanceDecodeBHist (SignedDistanceTasteGate_single_carrier_alignment_eventAt 6 ef))
      (signedDistanceDecodeBHist (SignedDistanceTasteGate_single_carrier_alignment_eventAt 7 ef))
      (signedDistanceDecodeBHist (SignedDistanceTasteGate_single_carrier_alignment_eventAt 8 ef))
      (signedDistanceDecodeBHist (SignedDistanceTasteGate_single_carrier_alignment_eventAt 9 ef)))

private theorem SignedDistanceTasteGate_single_carrier_alignment_round_trip
    (x : SignedDistanceUp) :
    signedDistanceFromEventFlow (signedDistanceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk M L A D R E H C P N =>
      change
        some
          (SignedDistanceUp.mk
            (signedDistanceDecodeBHist (signedDistanceEncodeBHist M))
            (signedDistanceDecodeBHist (signedDistanceEncodeBHist L))
            (signedDistanceDecodeBHist (signedDistanceEncodeBHist A))
            (signedDistanceDecodeBHist (signedDistanceEncodeBHist D))
            (signedDistanceDecodeBHist (signedDistanceEncodeBHist R))
            (signedDistanceDecodeBHist (signedDistanceEncodeBHist E))
            (signedDistanceDecodeBHist (signedDistanceEncodeBHist H))
            (signedDistanceDecodeBHist (signedDistanceEncodeBHist C))
            (signedDistanceDecodeBHist (signedDistanceEncodeBHist P))
            (signedDistanceDecodeBHist (signedDistanceEncodeBHist N))) =
          some (SignedDistanceUp.mk M L A D R E H C P N)
      rw [SignedDistanceTasteGate_single_carrier_alignment_decode_encode M,
        SignedDistanceTasteGate_single_carrier_alignment_decode_encode L,
        SignedDistanceTasteGate_single_carrier_alignment_decode_encode A,
        SignedDistanceTasteGate_single_carrier_alignment_decode_encode D,
        SignedDistanceTasteGate_single_carrier_alignment_decode_encode R,
        SignedDistanceTasteGate_single_carrier_alignment_decode_encode E,
        SignedDistanceTasteGate_single_carrier_alignment_decode_encode H,
        SignedDistanceTasteGate_single_carrier_alignment_decode_encode C,
        SignedDistanceTasteGate_single_carrier_alignment_decode_encode P,
        SignedDistanceTasteGate_single_carrier_alignment_decode_encode N]

private theorem SignedDistanceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : SignedDistanceUp} :
    signedDistanceToEventFlow x = signedDistanceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      signedDistanceFromEventFlow (signedDistanceToEventFlow x) =
        signedDistanceFromEventFlow (signedDistanceToEventFlow y) :=
    congrArg signedDistanceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (SignedDistanceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (SignedDistanceTasteGate_single_carrier_alignment_round_trip y)))

private theorem SignedDistanceTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : SignedDistanceUp, signedDistanceFields x = signedDistanceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M₁ L₁ A₁ D₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk M₂ L₂ A₂ D₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance signedDistanceBHistCarrier : BHistCarrier SignedDistanceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := signedDistanceToEventFlow
  fromEventFlow := signedDistanceFromEventFlow

instance signedDistanceChapterTasteGate : ChapterTasteGate SignedDistanceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change signedDistanceFromEventFlow (signedDistanceToEventFlow x) = some x
    exact SignedDistanceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (SignedDistanceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance signedDistanceFieldFaithful : FieldFaithful SignedDistanceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := signedDistanceFields
  field_faithful := SignedDistanceTasteGate_single_carrier_alignment_fields_faithful

instance signedDistanceNontrivial :
    BEDC.Meta.TasteGate.Nontrivial SignedDistanceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SignedDistanceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      SignedDistanceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def signedDistanceTasteGate : ChapterTasteGate SignedDistanceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  signedDistanceChapterTasteGate

theorem SignedDistanceTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate SignedDistanceUp) ∧
      Nonempty (FieldFaithful SignedDistanceUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial SignedDistanceUp) ∧
          (∀ h : BHist, signedDistanceDecodeBHist (signedDistanceEncodeBHist h) = h) ∧
            (∀ x : SignedDistanceUp,
              signedDistanceFromEventFlow (signedDistanceToEventFlow x) = some x) ∧
              (∀ x y : SignedDistanceUp,
                signedDistanceToEventFlow x = signedDistanceToEventFlow y → x = y) ∧
                signedDistanceEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨⟨signedDistanceChapterTasteGate⟩,
      ⟨signedDistanceFieldFaithful⟩,
      ⟨signedDistanceNontrivial⟩,
      SignedDistanceTasteGate_single_carrier_alignment_decode_encode,
      SignedDistanceTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => SignedDistanceTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.SignedDistanceUp.TasteGate
