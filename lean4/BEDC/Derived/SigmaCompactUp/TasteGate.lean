import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SigmaCompactUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SigmaCompactUp : Type where
  | mk (X E K B L H C P N : BHist) : SigmaCompactUp
  deriving DecidableEq

def sigmaCompactEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: sigmaCompactEncodeBHist h
  | BHist.e1 h => BMark.b1 :: sigmaCompactEncodeBHist h

def sigmaCompactDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (sigmaCompactDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (sigmaCompactDecodeBHist tail)

private theorem SigmaCompactTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, sigmaCompactDecodeBHist (sigmaCompactEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def sigmaCompactToEventFlow : SigmaCompactUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | SigmaCompactUp.mk X E K B L H C P N =>
      [sigmaCompactEncodeBHist X,
        sigmaCompactEncodeBHist E,
        sigmaCompactEncodeBHist K,
        sigmaCompactEncodeBHist B,
        sigmaCompactEncodeBHist L,
        sigmaCompactEncodeBHist H,
        sigmaCompactEncodeBHist C,
        sigmaCompactEncodeBHist P,
        sigmaCompactEncodeBHist N]

private def sigmaCompactEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => sigmaCompactEventAtDefault index rest

def sigmaCompactFromEventFlow (ef : EventFlow) : Option SigmaCompactUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SigmaCompactUp.mk
      (sigmaCompactDecodeBHist (sigmaCompactEventAtDefault 0 ef))
      (sigmaCompactDecodeBHist (sigmaCompactEventAtDefault 1 ef))
      (sigmaCompactDecodeBHist (sigmaCompactEventAtDefault 2 ef))
      (sigmaCompactDecodeBHist (sigmaCompactEventAtDefault 3 ef))
      (sigmaCompactDecodeBHist (sigmaCompactEventAtDefault 4 ef))
      (sigmaCompactDecodeBHist (sigmaCompactEventAtDefault 5 ef))
      (sigmaCompactDecodeBHist (sigmaCompactEventAtDefault 6 ef))
      (sigmaCompactDecodeBHist (sigmaCompactEventAtDefault 7 ef))
      (sigmaCompactDecodeBHist (sigmaCompactEventAtDefault 8 ef)))

private theorem SigmaCompactTasteGate_single_carrier_alignment_round_trip :
    ∀ x : SigmaCompactUp,
      sigmaCompactFromEventFlow (sigmaCompactToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X E K B L H C P N =>
      change
        some
          (SigmaCompactUp.mk
            (sigmaCompactDecodeBHist (sigmaCompactEncodeBHist X))
            (sigmaCompactDecodeBHist (sigmaCompactEncodeBHist E))
            (sigmaCompactDecodeBHist (sigmaCompactEncodeBHist K))
            (sigmaCompactDecodeBHist (sigmaCompactEncodeBHist B))
            (sigmaCompactDecodeBHist (sigmaCompactEncodeBHist L))
            (sigmaCompactDecodeBHist (sigmaCompactEncodeBHist H))
            (sigmaCompactDecodeBHist (sigmaCompactEncodeBHist C))
            (sigmaCompactDecodeBHist (sigmaCompactEncodeBHist P))
            (sigmaCompactDecodeBHist (sigmaCompactEncodeBHist N))) =
          some (SigmaCompactUp.mk X E K B L H C P N)
      rw [SigmaCompactTasteGate_single_carrier_alignment_decode X,
        SigmaCompactTasteGate_single_carrier_alignment_decode E,
        SigmaCompactTasteGate_single_carrier_alignment_decode K,
        SigmaCompactTasteGate_single_carrier_alignment_decode B,
        SigmaCompactTasteGate_single_carrier_alignment_decode L,
        SigmaCompactTasteGate_single_carrier_alignment_decode H,
        SigmaCompactTasteGate_single_carrier_alignment_decode C,
        SigmaCompactTasteGate_single_carrier_alignment_decode P,
        SigmaCompactTasteGate_single_carrier_alignment_decode N]

private theorem SigmaCompactTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : SigmaCompactUp} :
    sigmaCompactToEventFlow x = sigmaCompactToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      sigmaCompactFromEventFlow (sigmaCompactToEventFlow x) =
        sigmaCompactFromEventFlow (sigmaCompactToEventFlow y) :=
    congrArg sigmaCompactFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (SigmaCompactTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (SigmaCompactTasteGate_single_carrier_alignment_round_trip y)))

def sigmaCompactFields : SigmaCompactUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SigmaCompactUp.mk X E K B L H C P N => [X, E, K, B, L, H, C, P, N]

private theorem SigmaCompactTasteGate_single_carrier_alignment_fields :
    ∀ x y : SigmaCompactUp, sigmaCompactFields x = sigmaCompactFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X1 E1 K1 B1 L1 H1 C1 P1 N1 =>
      cases y with
      | mk X2 E2 K2 B2 L2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance sigmaCompactBHistCarrier : BHistCarrier SigmaCompactUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := sigmaCompactToEventFlow
  fromEventFlow := sigmaCompactFromEventFlow

instance sigmaCompactChapterTasteGate : ChapterTasteGate SigmaCompactUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change sigmaCompactFromEventFlow (sigmaCompactToEventFlow x) = some x
    exact SigmaCompactTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (SigmaCompactTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance sigmaCompactFieldFaithful : FieldFaithful SigmaCompactUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := sigmaCompactFields
  field_faithful := SigmaCompactTasteGate_single_carrier_alignment_fields

instance sigmaCompactNontrivial :
    BEDC.Meta.TasteGate.Nontrivial SigmaCompactUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SigmaCompactUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      SigmaCompactUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate SigmaCompactUp :=
  -- BEDC touchpoint anchor: BHist BMark
  sigmaCompactChapterTasteGate

namespace TasteGate

theorem SigmaCompactTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate SigmaCompactUp) ∧
      Nonempty (FieldFaithful SigmaCompactUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial SigmaCompactUp) ∧
          (∀ h : BHist, sigmaCompactDecodeBHist (sigmaCompactEncodeBHist h) = h) ∧
            (∀ x : SigmaCompactUp,
              sigmaCompactFromEventFlow (sigmaCompactToEventFlow x) = some x) ∧
              (∀ x y : SigmaCompactUp,
                sigmaCompactToEventFlow x = sigmaCompactToEventFlow y → x = y) ∧
                sigmaCompactEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨sigmaCompactChapterTasteGate⟩,
      ⟨sigmaCompactFieldFaithful⟩,
      ⟨sigmaCompactNontrivial⟩,
      SigmaCompactTasteGate_single_carrier_alignment_decode,
      SigmaCompactTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => SigmaCompactTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end TasteGate

end BEDC.Derived.SigmaCompactUp
