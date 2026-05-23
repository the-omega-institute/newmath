import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Unary.History
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AnchorStabilityCertificateUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AnchorStabilityCertificateUp : Type where
  | mk (F I R K L H C P N : BHist) : AnchorStabilityCertificateUp
  deriving DecidableEq

def anchorStabilityCertificateEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: anchorStabilityCertificateEncodeBHist h
  | BHist.e1 h => BMark.b1 :: anchorStabilityCertificateEncodeBHist h

def anchorStabilityCertificateDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (anchorStabilityCertificateDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (anchorStabilityCertificateDecodeBHist tail)

private theorem anchorStabilityCertificateDecode_encode_bhist :
    ∀ h : BHist,
      anchorStabilityCertificateDecodeBHist
        (anchorStabilityCertificateEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private def anchorStabilityCertificateFields :
    AnchorStabilityCertificateUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AnchorStabilityCertificateUp.mk F I R K L H C P N => [F, I, R, K, L, H, C, P, N]

def anchorStabilityCertificateToEventFlow :
    AnchorStabilityCertificateUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | AnchorStabilityCertificateUp.mk F I R K L H C P N =>
      [[BMark.b0],
        anchorStabilityCertificateEncodeBHist F,
        [BMark.b1, BMark.b0],
        anchorStabilityCertificateEncodeBHist I,
        [BMark.b1, BMark.b1, BMark.b0],
        anchorStabilityCertificateEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        anchorStabilityCertificateEncodeBHist K,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        anchorStabilityCertificateEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        anchorStabilityCertificateEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        anchorStabilityCertificateEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        anchorStabilityCertificateEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        anchorStabilityCertificateEncodeBHist N]

private def anchorStabilityCertificateRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => anchorStabilityCertificateRawAt n rest

private def anchorStabilityCertificateLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => anchorStabilityCertificateLengthEq n rest

def anchorStabilityCertificateFromEventFlow :
    EventFlow → Option AnchorStabilityCertificateUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match anchorStabilityCertificateLengthEq 18 flow with
      | true =>
          some
            (AnchorStabilityCertificateUp.mk
              (anchorStabilityCertificateDecodeBHist
                (anchorStabilityCertificateRawAt 1 flow))
              (anchorStabilityCertificateDecodeBHist
                (anchorStabilityCertificateRawAt 3 flow))
              (anchorStabilityCertificateDecodeBHist
                (anchorStabilityCertificateRawAt 5 flow))
              (anchorStabilityCertificateDecodeBHist
                (anchorStabilityCertificateRawAt 7 flow))
              (anchorStabilityCertificateDecodeBHist
                (anchorStabilityCertificateRawAt 9 flow))
              (anchorStabilityCertificateDecodeBHist
                (anchorStabilityCertificateRawAt 11 flow))
              (anchorStabilityCertificateDecodeBHist
                (anchorStabilityCertificateRawAt 13 flow))
              (anchorStabilityCertificateDecodeBHist
                (anchorStabilityCertificateRawAt 15 flow))
              (anchorStabilityCertificateDecodeBHist
                (anchorStabilityCertificateRawAt 17 flow)))
      | false => none

private theorem anchorStabilityCertificate_round_trip :
    ∀ x : AnchorStabilityCertificateUp,
      anchorStabilityCertificateFromEventFlow
        (anchorStabilityCertificateToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F I R K L H C P N =>
      change
        some
          (AnchorStabilityCertificateUp.mk
            (anchorStabilityCertificateDecodeBHist
              (anchorStabilityCertificateEncodeBHist F))
            (anchorStabilityCertificateDecodeBHist
              (anchorStabilityCertificateEncodeBHist I))
            (anchorStabilityCertificateDecodeBHist
              (anchorStabilityCertificateEncodeBHist R))
            (anchorStabilityCertificateDecodeBHist
              (anchorStabilityCertificateEncodeBHist K))
            (anchorStabilityCertificateDecodeBHist
              (anchorStabilityCertificateEncodeBHist L))
            (anchorStabilityCertificateDecodeBHist
              (anchorStabilityCertificateEncodeBHist H))
            (anchorStabilityCertificateDecodeBHist
              (anchorStabilityCertificateEncodeBHist C))
            (anchorStabilityCertificateDecodeBHist
              (anchorStabilityCertificateEncodeBHist P))
            (anchorStabilityCertificateDecodeBHist
              (anchorStabilityCertificateEncodeBHist N))) =
          some (AnchorStabilityCertificateUp.mk F I R K L H C P N)
      rw [anchorStabilityCertificateDecode_encode_bhist F,
        anchorStabilityCertificateDecode_encode_bhist I,
        anchorStabilityCertificateDecode_encode_bhist R,
        anchorStabilityCertificateDecode_encode_bhist K,
        anchorStabilityCertificateDecode_encode_bhist L,
        anchorStabilityCertificateDecode_encode_bhist H,
        anchorStabilityCertificateDecode_encode_bhist C,
        anchorStabilityCertificateDecode_encode_bhist P,
        anchorStabilityCertificateDecode_encode_bhist N]

private theorem anchorStabilityCertificateToEventFlow_injective
    {x y : AnchorStabilityCertificateUp} :
    anchorStabilityCertificateToEventFlow x =
        anchorStabilityCertificateToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      anchorStabilityCertificateFromEventFlow
          (anchorStabilityCertificateToEventFlow x) =
        anchorStabilityCertificateFromEventFlow
          (anchorStabilityCertificateToEventFlow y) :=
    congrArg anchorStabilityCertificateFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (anchorStabilityCertificate_round_trip x).symm
      (Eq.trans hread (anchorStabilityCertificate_round_trip y)))

private theorem anchorStabilityCertificate_field_faithful :
    ∀ x y : AnchorStabilityCertificateUp,
      anchorStabilityCertificateFields x =
          anchorStabilityCertificateFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk F1 I1 R1 K1 L1 H1 C1 P1 N1 =>
      cases y with
      | mk F2 I2 R2 K2 L2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance anchorStabilityCertificateBHistCarrier :
    BHistCarrier AnchorStabilityCertificateUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := anchorStabilityCertificateToEventFlow
  fromEventFlow := anchorStabilityCertificateFromEventFlow

instance anchorStabilityCertificateChapterTasteGate :
    ChapterTasteGate AnchorStabilityCertificateUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      anchorStabilityCertificateFromEventFlow
          (anchorStabilityCertificateToEventFlow x) = some x
    exact anchorStabilityCertificate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (anchorStabilityCertificateToEventFlow_injective heq)

instance anchorStabilityCertificateFieldFaithful :
    FieldFaithful AnchorStabilityCertificateUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := anchorStabilityCertificateFields
  field_faithful := anchorStabilityCertificate_field_faithful

instance anchorStabilityCertificateNontrivial :
    Nontrivial AnchorStabilityCertificateUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨AnchorStabilityCertificateUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      AnchorStabilityCertificateUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate AnchorStabilityCertificateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  anchorStabilityCertificateChapterTasteGate

theorem AnchorStabilityCertificateTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        anchorStabilityCertificateDecodeBHist
          (anchorStabilityCertificateEncodeBHist h) = h) ∧
      (∀ x : AnchorStabilityCertificateUp,
        anchorStabilityCertificateFromEventFlow
          (anchorStabilityCertificateToEventFlow x) = some x) ∧
        (∀ x y : AnchorStabilityCertificateUp,
          anchorStabilityCertificateToEventFlow x =
              anchorStabilityCertificateToEventFlow y →
            x = y) ∧
          anchorStabilityCertificateEncodeBHist BHist.Empty =
            ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  constructor
  · intro h
    induction h with
    | Empty =>
        rfl
    | e0 h ih =>
        exact congrArg BHist.e0 ih
    | e1 h ih =>
        exact congrArg BHist.e1 ih
  · constructor
    · intro x
      cases x with
      | mk F I R K L H C P N =>
          exact anchorStabilityCertificate_round_trip
            (AnchorStabilityCertificateUp.mk F I R K L H C P N)
    · constructor
      · intro x y heq
        have hread :
            anchorStabilityCertificateFromEventFlow
                (anchorStabilityCertificateToEventFlow x) =
              anchorStabilityCertificateFromEventFlow
                (anchorStabilityCertificateToEventFlow y) :=
          congrArg anchorStabilityCertificateFromEventFlow heq
        exact Option.some.inj
          (Eq.trans (anchorStabilityCertificate_round_trip x).symm
            (Eq.trans hread (anchorStabilityCertificate_round_trip y)))
      · rfl

theorem AnchorStabilityCertificateCarrier_nonescape
    {F I R K L H C P N observerRead routeRead classifierRead privilegedObserver
      unledgeredAnchor hiddenSync hostEquality verdict : BHist} :
    Cont F C observerRead ->
      Cont R C routeRead ->
        Cont K C classifierRead ->
          UnaryHistory F ->
            UnaryHistory R ->
              UnaryHistory K ->
                UnaryHistory C ->
                  anchorStabilityCertificateToEventFlow
                      (AnchorStabilityCertificateUp.mk F I R K L H C P N) =
                    anchorStabilityCertificateToEventFlow
                      (AnchorStabilityCertificateUp.mk F I R K L H C P N) ->
                    UnaryHistory observerRead ∧ UnaryHistory routeRead ∧
                      UnaryHistory classifierRead ∧ hsame privilegedObserver privilegedObserver ∧
                        hsame unledgeredAnchor unledgeredAnchor ∧ hsame hiddenSync hiddenSync ∧
                          hsame hostEquality hostEquality ∧ hsame verdict verdict := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont hsame
  intro fCObserver rCRoute kCClassifier fUnary rUnary kUnary cUnary _flow
  exact
    ⟨unary_cont_closed fUnary cUnary fCObserver,
      unary_cont_closed rUnary cUnary rCRoute,
      unary_cont_closed kUnary cUnary kCClassifier,
      hsame_refl privilegedObserver,
      hsame_refl unledgeredAnchor,
      hsame_refl hiddenSync,
      hsame_refl hostEquality,
      hsame_refl verdict⟩

end BEDC.Derived.AnchorStabilityCertificateUp
