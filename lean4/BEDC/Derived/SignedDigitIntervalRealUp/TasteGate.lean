import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SignedDigitIntervalRealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SignedDigitIntervalRealUp : Type where
  | mk (L U D O S R E H C P N : BHist) : SignedDigitIntervalRealUp
  deriving DecidableEq

def signedDigitIntervalRealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: signedDigitIntervalRealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: signedDigitIntervalRealEncodeBHist h

def signedDigitIntervalRealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (signedDigitIntervalRealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (signedDigitIntervalRealDecodeBHist tail)

private theorem SignedDigitIntervalRealTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      signedDigitIntervalRealDecodeBHist (signedDigitIntervalRealEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def signedDigitIntervalRealFields : SignedDigitIntervalRealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SignedDigitIntervalRealUp.mk L U D O S R E H C P N =>
      [L, U, D, O, S, R, E, H, C, P, N]

def signedDigitIntervalRealToEventFlow : SignedDigitIntervalRealUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (signedDigitIntervalRealFields x).map signedDigitIntervalRealEncodeBHist

private def signedDigitIntervalRealEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => signedDigitIntervalRealEventAtDefault index rest

def signedDigitIntervalRealFromEventFlow
    (ef : EventFlow) : Option SignedDigitIntervalRealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SignedDigitIntervalRealUp.mk
      (signedDigitIntervalRealDecodeBHist (signedDigitIntervalRealEventAtDefault 0 ef))
      (signedDigitIntervalRealDecodeBHist (signedDigitIntervalRealEventAtDefault 1 ef))
      (signedDigitIntervalRealDecodeBHist (signedDigitIntervalRealEventAtDefault 2 ef))
      (signedDigitIntervalRealDecodeBHist (signedDigitIntervalRealEventAtDefault 3 ef))
      (signedDigitIntervalRealDecodeBHist (signedDigitIntervalRealEventAtDefault 4 ef))
      (signedDigitIntervalRealDecodeBHist (signedDigitIntervalRealEventAtDefault 5 ef))
      (signedDigitIntervalRealDecodeBHist (signedDigitIntervalRealEventAtDefault 6 ef))
      (signedDigitIntervalRealDecodeBHist (signedDigitIntervalRealEventAtDefault 7 ef))
      (signedDigitIntervalRealDecodeBHist (signedDigitIntervalRealEventAtDefault 8 ef))
      (signedDigitIntervalRealDecodeBHist (signedDigitIntervalRealEventAtDefault 9 ef))
      (signedDigitIntervalRealDecodeBHist (signedDigitIntervalRealEventAtDefault 10 ef)))

private theorem SignedDigitIntervalRealTasteGate_single_carrier_alignment_round_trip :
    ∀ x : SignedDigitIntervalRealUp,
      signedDigitIntervalRealFromEventFlow (signedDigitIntervalRealToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L U D O S R E H C P N =>
      change
        some
          (SignedDigitIntervalRealUp.mk
            (signedDigitIntervalRealDecodeBHist (signedDigitIntervalRealEncodeBHist L))
            (signedDigitIntervalRealDecodeBHist (signedDigitIntervalRealEncodeBHist U))
            (signedDigitIntervalRealDecodeBHist (signedDigitIntervalRealEncodeBHist D))
            (signedDigitIntervalRealDecodeBHist (signedDigitIntervalRealEncodeBHist O))
            (signedDigitIntervalRealDecodeBHist (signedDigitIntervalRealEncodeBHist S))
            (signedDigitIntervalRealDecodeBHist (signedDigitIntervalRealEncodeBHist R))
            (signedDigitIntervalRealDecodeBHist (signedDigitIntervalRealEncodeBHist E))
            (signedDigitIntervalRealDecodeBHist (signedDigitIntervalRealEncodeBHist H))
            (signedDigitIntervalRealDecodeBHist (signedDigitIntervalRealEncodeBHist C))
            (signedDigitIntervalRealDecodeBHist (signedDigitIntervalRealEncodeBHist P))
            (signedDigitIntervalRealDecodeBHist (signedDigitIntervalRealEncodeBHist N))) =
          some (SignedDigitIntervalRealUp.mk L U D O S R E H C P N)
      rw [SignedDigitIntervalRealTasteGate_single_carrier_alignment_decode L,
        SignedDigitIntervalRealTasteGate_single_carrier_alignment_decode U,
        SignedDigitIntervalRealTasteGate_single_carrier_alignment_decode D,
        SignedDigitIntervalRealTasteGate_single_carrier_alignment_decode O,
        SignedDigitIntervalRealTasteGate_single_carrier_alignment_decode S,
        SignedDigitIntervalRealTasteGate_single_carrier_alignment_decode R,
        SignedDigitIntervalRealTasteGate_single_carrier_alignment_decode E,
        SignedDigitIntervalRealTasteGate_single_carrier_alignment_decode H,
        SignedDigitIntervalRealTasteGate_single_carrier_alignment_decode C,
        SignedDigitIntervalRealTasteGate_single_carrier_alignment_decode P,
        SignedDigitIntervalRealTasteGate_single_carrier_alignment_decode N]

private theorem SignedDigitIntervalRealTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : SignedDigitIntervalRealUp} :
    signedDigitIntervalRealToEventFlow x = signedDigitIntervalRealToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      signedDigitIntervalRealFromEventFlow (signedDigitIntervalRealToEventFlow x) =
        signedDigitIntervalRealFromEventFlow (signedDigitIntervalRealToEventFlow y) :=
    congrArg signedDigitIntervalRealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (SignedDigitIntervalRealTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (SignedDigitIntervalRealTasteGate_single_carrier_alignment_round_trip y)))

private theorem SignedDigitIntervalRealTasteGate_single_carrier_alignment_fields :
    ∀ x y : SignedDigitIntervalRealUp,
      signedDigitIntervalRealFields x = signedDigitIntervalRealFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk L₁ U₁ D₁ O₁ S₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk L₂ U₂ D₂ O₂ S₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance signedDigitIntervalRealBHistCarrier :
    BHistCarrier SignedDigitIntervalRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := signedDigitIntervalRealToEventFlow
  fromEventFlow := signedDigitIntervalRealFromEventFlow

instance signedDigitIntervalRealChapterTasteGate :
    ChapterTasteGate SignedDigitIntervalRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      signedDigitIntervalRealFromEventFlow (signedDigitIntervalRealToEventFlow x) =
        some x
    exact SignedDigitIntervalRealTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (SignedDigitIntervalRealTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance signedDigitIntervalRealFieldFaithful :
    FieldFaithful SignedDigitIntervalRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := signedDigitIntervalRealFields
  field_faithful := SignedDigitIntervalRealTasteGate_single_carrier_alignment_fields

instance signedDigitIntervalRealNontrivial :
    BEDC.Meta.TasteGate.Nontrivial SignedDigitIntervalRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SignedDigitIntervalRealUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      SignedDigitIntervalRealUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate SignedDigitIntervalRealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  signedDigitIntervalRealChapterTasteGate

theorem SignedDigitIntervalRealTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      signedDigitIntervalRealDecodeBHist (signedDigitIntervalRealEncodeBHist h) =
        h) ∧
      (∀ x : SignedDigitIntervalRealUp,
        signedDigitIntervalRealFromEventFlow (signedDigitIntervalRealToEventFlow x) =
          some x) ∧
        (∀ x y : SignedDigitIntervalRealUp,
          signedDigitIntervalRealToEventFlow x = signedDigitIntervalRealToEventFlow y ->
            x = y) ∧
          signedDigitIntervalRealEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨SignedDigitIntervalRealTasteGate_single_carrier_alignment_decode,
      SignedDigitIntervalRealTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        SignedDigitIntervalRealTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.SignedDigitIntervalRealUp
