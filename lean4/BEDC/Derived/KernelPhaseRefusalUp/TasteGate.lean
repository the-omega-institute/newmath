import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.KernelPhaseRefusalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive KernelPhaseRefusalUp : Type where
  | mk
      (phase target blocker verdict admissibility transport continuation provenance localName :
        BHist) : KernelPhaseRefusalUp
  deriving DecidableEq

def kernelPhaseRefusalEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: kernelPhaseRefusalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: kernelPhaseRefusalEncodeBHist h

def kernelPhaseRefusalDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (kernelPhaseRefusalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (kernelPhaseRefusalDecodeBHist tail)

private theorem kernelPhaseRefusalDecode_encode_bhist :
    ∀ h : BHist, kernelPhaseRefusalDecodeBHist (kernelPhaseRefusalEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private def kernelPhaseRefusalFields : KernelPhaseRefusalUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | KernelPhaseRefusalUp.mk P T D R A H C Q N => [P, T, D, R, A, H, C, Q, N]

def kernelPhaseRefusalToEventFlow : KernelPhaseRefusalUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | KernelPhaseRefusalUp.mk P T D R A H C Q N =>
      [[BMark.b0],
        kernelPhaseRefusalEncodeBHist P,
        [BMark.b1, BMark.b0],
        kernelPhaseRefusalEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b0],
        kernelPhaseRefusalEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        kernelPhaseRefusalEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        kernelPhaseRefusalEncodeBHist A,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        kernelPhaseRefusalEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        kernelPhaseRefusalEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        kernelPhaseRefusalEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        kernelPhaseRefusalEncodeBHist N]

private def kernelPhaseRefusalRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => kernelPhaseRefusalRawAt n rest

private def kernelPhaseRefusalLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => kernelPhaseRefusalLengthEq n rest

def kernelPhaseRefusalFromEventFlow : EventFlow → Option KernelPhaseRefusalUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match kernelPhaseRefusalLengthEq 18 flow with
      | true =>
          some
            (KernelPhaseRefusalUp.mk
              (kernelPhaseRefusalDecodeBHist (kernelPhaseRefusalRawAt 1 flow))
              (kernelPhaseRefusalDecodeBHist (kernelPhaseRefusalRawAt 3 flow))
              (kernelPhaseRefusalDecodeBHist (kernelPhaseRefusalRawAt 5 flow))
              (kernelPhaseRefusalDecodeBHist (kernelPhaseRefusalRawAt 7 flow))
              (kernelPhaseRefusalDecodeBHist (kernelPhaseRefusalRawAt 9 flow))
              (kernelPhaseRefusalDecodeBHist (kernelPhaseRefusalRawAt 11 flow))
              (kernelPhaseRefusalDecodeBHist (kernelPhaseRefusalRawAt 13 flow))
              (kernelPhaseRefusalDecodeBHist (kernelPhaseRefusalRawAt 15 flow))
              (kernelPhaseRefusalDecodeBHist (kernelPhaseRefusalRawAt 17 flow)))
      | false => none

private theorem kernelPhaseRefusal_round_trip :
    ∀ x : KernelPhaseRefusalUp,
      kernelPhaseRefusalFromEventFlow (kernelPhaseRefusalToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk P T D R A H C Q N =>
      change
        some
          (KernelPhaseRefusalUp.mk
            (kernelPhaseRefusalDecodeBHist (kernelPhaseRefusalEncodeBHist P))
            (kernelPhaseRefusalDecodeBHist (kernelPhaseRefusalEncodeBHist T))
            (kernelPhaseRefusalDecodeBHist (kernelPhaseRefusalEncodeBHist D))
            (kernelPhaseRefusalDecodeBHist (kernelPhaseRefusalEncodeBHist R))
            (kernelPhaseRefusalDecodeBHist (kernelPhaseRefusalEncodeBHist A))
            (kernelPhaseRefusalDecodeBHist (kernelPhaseRefusalEncodeBHist H))
            (kernelPhaseRefusalDecodeBHist (kernelPhaseRefusalEncodeBHist C))
            (kernelPhaseRefusalDecodeBHist (kernelPhaseRefusalEncodeBHist Q))
            (kernelPhaseRefusalDecodeBHist (kernelPhaseRefusalEncodeBHist N))) =
          some (KernelPhaseRefusalUp.mk P T D R A H C Q N)
      rw [kernelPhaseRefusalDecode_encode_bhist P, kernelPhaseRefusalDecode_encode_bhist T,
        kernelPhaseRefusalDecode_encode_bhist D, kernelPhaseRefusalDecode_encode_bhist R,
        kernelPhaseRefusalDecode_encode_bhist A, kernelPhaseRefusalDecode_encode_bhist H,
        kernelPhaseRefusalDecode_encode_bhist C, kernelPhaseRefusalDecode_encode_bhist Q,
        kernelPhaseRefusalDecode_encode_bhist N]

private theorem kernelPhaseRefusalToEventFlow_injective {x y : KernelPhaseRefusalUp} :
    kernelPhaseRefusalToEventFlow x = kernelPhaseRefusalToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      kernelPhaseRefusalFromEventFlow (kernelPhaseRefusalToEventFlow x) =
        kernelPhaseRefusalFromEventFlow (kernelPhaseRefusalToEventFlow y) :=
    congrArg kernelPhaseRefusalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (kernelPhaseRefusal_round_trip x).symm
      (Eq.trans hread (kernelPhaseRefusal_round_trip y)))

private theorem kernelPhaseRefusal_field_faithful :
    ∀ x y : KernelPhaseRefusalUp,
      kernelPhaseRefusalFields x = kernelPhaseRefusalFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk P1 T1 D1 R1 A1 H1 C1 Q1 N1 =>
      cases y with
      | mk P2 T2 D2 R2 A2 H2 C2 Q2 N2 =>
          cases hfields
          rfl

instance kernelPhaseRefusalBHistCarrier : BHistCarrier KernelPhaseRefusalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := kernelPhaseRefusalToEventFlow
  fromEventFlow := kernelPhaseRefusalFromEventFlow

instance kernelPhaseRefusalChapterTasteGate :
    ChapterTasteGate KernelPhaseRefusalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change kernelPhaseRefusalFromEventFlow (kernelPhaseRefusalToEventFlow x) = some x
    exact kernelPhaseRefusal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (kernelPhaseRefusalToEventFlow_injective heq)

instance kernelPhaseRefusalFieldFaithful :
    FieldFaithful KernelPhaseRefusalUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := kernelPhaseRefusalFields
  field_faithful := kernelPhaseRefusal_field_faithful

instance kernelPhaseRefusalNontrivial : Nontrivial KernelPhaseRefusalUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨KernelPhaseRefusalUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      KernelPhaseRefusalUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate KernelPhaseRefusalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  kernelPhaseRefusalChapterTasteGate

end BEDC.Derived.KernelPhaseRefusalUp
