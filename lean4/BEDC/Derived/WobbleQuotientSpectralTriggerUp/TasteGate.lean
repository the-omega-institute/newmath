import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.WobbleQuotientSpectralTriggerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive WobbleQuotientSpectralTriggerUp : Type where
  | mk (Q S E H C P B R N : BHist) : WobbleQuotientSpectralTriggerUp
  deriving DecidableEq

def wobbleQuotientSpectralTriggerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: wobbleQuotientSpectralTriggerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: wobbleQuotientSpectralTriggerEncodeBHist h

def wobbleQuotientSpectralTriggerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (wobbleQuotientSpectralTriggerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (wobbleQuotientSpectralTriggerDecodeBHist tail)

private theorem wobbleQuotientSpectralTrigger_decode_encode :
    ∀ h : BHist,
      wobbleQuotientSpectralTriggerDecodeBHist
          (wobbleQuotientSpectralTriggerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem wobbleQuotientSpectralTrigger_encode_injective :
    ∀ {a b : BHist},
      wobbleQuotientSpectralTriggerEncodeBHist a =
          wobbleQuotientSpectralTriggerEncodeBHist b →
        a = b := by
  -- BEDC touchpoint anchor: BHist BMark
  intro a
  induction a with
  | Empty =>
      intro b h
      cases b with
      | Empty => rfl
      | e0 b => cases h
      | e1 b => cases h
  | e0 a ih =>
      intro b h
      cases b with
      | Empty => cases h
      | e0 b =>
          injection h with _ htail
          exact congrArg BHist.e0 (ih htail)
      | e1 b => cases h
  | e1 a ih =>
      intro b h
      cases b with
      | Empty => cases h
      | e0 b => cases h
      | e1 b =>
          injection h with _ htail
          exact congrArg BHist.e1 (ih htail)

def wobbleQuotientSpectralTriggerFields : WobbleQuotientSpectralTriggerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | WobbleQuotientSpectralTriggerUp.mk Q S E H C P B R N => [Q, S, E, H, C, P, B, R, N]

def wobbleQuotientSpectralTriggerToEventFlow : WobbleQuotientSpectralTriggerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (wobbleQuotientSpectralTriggerFields x).map wobbleQuotientSpectralTriggerEncodeBHist

def wobbleQuotientSpectralTriggerFromEventFlow :
    EventFlow → Option WobbleQuotientSpectralTriggerUp
  -- BEDC touchpoint anchor: BHist BMark
  | Q :: S :: E :: H :: C :: P :: B :: R :: N :: [] =>
      some
        (WobbleQuotientSpectralTriggerUp.mk
          (wobbleQuotientSpectralTriggerDecodeBHist Q)
          (wobbleQuotientSpectralTriggerDecodeBHist S)
          (wobbleQuotientSpectralTriggerDecodeBHist E)
          (wobbleQuotientSpectralTriggerDecodeBHist H)
          (wobbleQuotientSpectralTriggerDecodeBHist C)
          (wobbleQuotientSpectralTriggerDecodeBHist P)
          (wobbleQuotientSpectralTriggerDecodeBHist B)
          (wobbleQuotientSpectralTriggerDecodeBHist R)
          (wobbleQuotientSpectralTriggerDecodeBHist N))
  | _ => none

private theorem wobbleQuotientSpectralTrigger_round_trip :
    ∀ x : WobbleQuotientSpectralTriggerUp,
      wobbleQuotientSpectralTriggerFromEventFlow
          (wobbleQuotientSpectralTriggerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Q S E H C P B R N =>
      change
        some
          (WobbleQuotientSpectralTriggerUp.mk
            (wobbleQuotientSpectralTriggerDecodeBHist
              (wobbleQuotientSpectralTriggerEncodeBHist Q))
            (wobbleQuotientSpectralTriggerDecodeBHist
              (wobbleQuotientSpectralTriggerEncodeBHist S))
            (wobbleQuotientSpectralTriggerDecodeBHist
              (wobbleQuotientSpectralTriggerEncodeBHist E))
            (wobbleQuotientSpectralTriggerDecodeBHist
              (wobbleQuotientSpectralTriggerEncodeBHist H))
            (wobbleQuotientSpectralTriggerDecodeBHist
              (wobbleQuotientSpectralTriggerEncodeBHist C))
            (wobbleQuotientSpectralTriggerDecodeBHist
              (wobbleQuotientSpectralTriggerEncodeBHist P))
            (wobbleQuotientSpectralTriggerDecodeBHist
              (wobbleQuotientSpectralTriggerEncodeBHist B))
            (wobbleQuotientSpectralTriggerDecodeBHist
              (wobbleQuotientSpectralTriggerEncodeBHist R))
            (wobbleQuotientSpectralTriggerDecodeBHist
              (wobbleQuotientSpectralTriggerEncodeBHist N))) =
          some (WobbleQuotientSpectralTriggerUp.mk Q S E H C P B R N)
      rw [wobbleQuotientSpectralTrigger_decode_encode Q,
        wobbleQuotientSpectralTrigger_decode_encode S,
        wobbleQuotientSpectralTrigger_decode_encode E,
        wobbleQuotientSpectralTrigger_decode_encode H,
        wobbleQuotientSpectralTrigger_decode_encode C,
        wobbleQuotientSpectralTrigger_decode_encode P,
        wobbleQuotientSpectralTrigger_decode_encode B,
        wobbleQuotientSpectralTrigger_decode_encode R,
        wobbleQuotientSpectralTrigger_decode_encode N]

theorem wobbleQuotientSpectralTriggerToEventFlow_injective
    {x y : WobbleQuotientSpectralTriggerUp} :
    wobbleQuotientSpectralTriggerToEventFlow x =
        wobbleQuotientSpectralTriggerToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  cases x with
  | mk Q₁ S₁ E₁ H₁ C₁ P₁ B₁ R₁ N₁ =>
      cases y with
      | mk Q₂ S₂ E₂ H₂ C₂ P₂ B₂ R₂ N₂ =>
          injection heq with hQ tail0
          injection tail0 with hS tail1
          injection tail1 with hE tail2
          injection tail2 with hH tail3
          injection tail3 with hC tail4
          injection tail4 with hP tail5
          injection tail5 with hB tail6
          injection tail6 with hR tail7
          injection tail7 with hN _
          have eQ := wobbleQuotientSpectralTrigger_encode_injective hQ
          have eS := wobbleQuotientSpectralTrigger_encode_injective hS
          have eE := wobbleQuotientSpectralTrigger_encode_injective hE
          have eH := wobbleQuotientSpectralTrigger_encode_injective hH
          have eC := wobbleQuotientSpectralTrigger_encode_injective hC
          have eP := wobbleQuotientSpectralTrigger_encode_injective hP
          have eB := wobbleQuotientSpectralTrigger_encode_injective hB
          have eR := wobbleQuotientSpectralTrigger_encode_injective hR
          have eN := wobbleQuotientSpectralTrigger_encode_injective hN
          cases eQ
          cases eS
          cases eE
          cases eH
          cases eC
          cases eP
          cases eB
          cases eR
          cases eN
          rfl

private theorem wobbleQuotientSpectralTrigger_fields_faithful :
    ∀ x y : WobbleQuotientSpectralTriggerUp,
      wobbleQuotientSpectralTriggerFields x = wobbleQuotientSpectralTriggerFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk Q₁ S₁ E₁ H₁ C₁ P₁ B₁ R₁ N₁ =>
      cases y with
      | mk Q₂ S₂ E₂ H₂ C₂ P₂ B₂ R₂ N₂ =>
          injection hfields with hQ tail0
          injection tail0 with hS tail1
          injection tail1 with hE tail2
          injection tail2 with hH tail3
          injection tail3 with hC tail4
          injection tail4 with hP tail5
          injection tail5 with hB tail6
          injection tail6 with hR tail7
          injection tail7 with hN _
          subst hQ
          subst hS
          subst hE
          subst hH
          subst hC
          subst hP
          subst hB
          subst hR
          subst hN
          rfl

instance wobbleQuotientSpectralTriggerBHistCarrier :
    BHistCarrier WobbleQuotientSpectralTriggerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := wobbleQuotientSpectralTriggerToEventFlow
  fromEventFlow := wobbleQuotientSpectralTriggerFromEventFlow

def wobbleQuotientSpectralTriggerChapterTasteGate :
    ChapterTasteGate WobbleQuotientSpectralTriggerUp := {
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      wobbleQuotientSpectralTriggerFromEventFlow
          (wobbleQuotientSpectralTriggerToEventFlow x) = some x
    exact wobbleQuotientSpectralTrigger_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (wobbleQuotientSpectralTriggerToEventFlow_injective heq)
}

instance wobbleQuotientSpectralTriggerChapterTasteGateInstance :
    ChapterTasteGate WobbleQuotientSpectralTriggerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  wobbleQuotientSpectralTriggerChapterTasteGate

instance wobbleQuotientSpectralTriggerFieldFaithful :
    FieldFaithful WobbleQuotientSpectralTriggerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := wobbleQuotientSpectralTriggerFields
  field_faithful := wobbleQuotientSpectralTrigger_fields_faithful

instance wobbleQuotientSpectralTriggerNontrivial :
    Nontrivial WobbleQuotientSpectralTriggerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨WobbleQuotientSpectralTriggerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      WobbleQuotientSpectralTriggerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate WobbleQuotientSpectralTriggerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  wobbleQuotientSpectralTriggerChapterTasteGate

end BEDC.Derived.WobbleQuotientSpectralTriggerUp
