import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.KelleyficationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive KelleyficationUp : Type where
  | mk (T C O W H R P N : BHist) : KelleyficationUp
  deriving DecidableEq

def kelleyficationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: kelleyficationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: kelleyficationEncodeBHist h

def kelleyficationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (kelleyficationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (kelleyficationDecodeBHist tail)

private theorem KelleyficationTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, kelleyficationDecodeBHist (kelleyficationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def kelleyficationToEventFlow : KelleyficationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | KelleyficationUp.mk T C O W H R P N =>
      [kelleyficationEncodeBHist T,
        kelleyficationEncodeBHist C,
        kelleyficationEncodeBHist O,
        kelleyficationEncodeBHist W,
        kelleyficationEncodeBHist H,
        kelleyficationEncodeBHist R,
        kelleyficationEncodeBHist P,
        kelleyficationEncodeBHist N]

private def kelleyficationEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => kelleyficationEventAtDefault index rest

def kelleyficationFromEventFlow (ef : EventFlow) : Option KelleyficationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (KelleyficationUp.mk
      (kelleyficationDecodeBHist (kelleyficationEventAtDefault 0 ef))
      (kelleyficationDecodeBHist (kelleyficationEventAtDefault 1 ef))
      (kelleyficationDecodeBHist (kelleyficationEventAtDefault 2 ef))
      (kelleyficationDecodeBHist (kelleyficationEventAtDefault 3 ef))
      (kelleyficationDecodeBHist (kelleyficationEventAtDefault 4 ef))
      (kelleyficationDecodeBHist (kelleyficationEventAtDefault 5 ef))
      (kelleyficationDecodeBHist (kelleyficationEventAtDefault 6 ef))
      (kelleyficationDecodeBHist (kelleyficationEventAtDefault 7 ef)))

private theorem KelleyficationTasteGate_single_carrier_alignment_round_trip :
    ∀ x : KelleyficationUp,
      kelleyficationFromEventFlow (kelleyficationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk T C O W H R P N =>
      change
        some
          (KelleyficationUp.mk
            (kelleyficationDecodeBHist (kelleyficationEncodeBHist T))
            (kelleyficationDecodeBHist (kelleyficationEncodeBHist C))
            (kelleyficationDecodeBHist (kelleyficationEncodeBHist O))
            (kelleyficationDecodeBHist (kelleyficationEncodeBHist W))
            (kelleyficationDecodeBHist (kelleyficationEncodeBHist H))
            (kelleyficationDecodeBHist (kelleyficationEncodeBHist R))
            (kelleyficationDecodeBHist (kelleyficationEncodeBHist P))
            (kelleyficationDecodeBHist (kelleyficationEncodeBHist N))) =
          some (KelleyficationUp.mk T C O W H R P N)
      rw [KelleyficationTasteGate_single_carrier_alignment_decode_encode T,
        KelleyficationTasteGate_single_carrier_alignment_decode_encode C,
        KelleyficationTasteGate_single_carrier_alignment_decode_encode O,
        KelleyficationTasteGate_single_carrier_alignment_decode_encode W,
        KelleyficationTasteGate_single_carrier_alignment_decode_encode H,
        KelleyficationTasteGate_single_carrier_alignment_decode_encode R,
        KelleyficationTasteGate_single_carrier_alignment_decode_encode P,
        KelleyficationTasteGate_single_carrier_alignment_decode_encode N]

private theorem KelleyficationTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : KelleyficationUp} :
    kelleyficationToEventFlow x = kelleyficationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  cases x with
  | mk T₁ C₁ O₁ W₁ H₁ R₁ P₁ N₁ =>
      cases y with
      | mk T₂ C₂ O₂ W₂ H₂ R₂ P₂ N₂ =>
          change
            [kelleyficationEncodeBHist T₁, kelleyficationEncodeBHist C₁,
              kelleyficationEncodeBHist O₁, kelleyficationEncodeBHist W₁,
              kelleyficationEncodeBHist H₁, kelleyficationEncodeBHist R₁,
              kelleyficationEncodeBHist P₁, kelleyficationEncodeBHist N₁] =
              [kelleyficationEncodeBHist T₂, kelleyficationEncodeBHist C₂,
                kelleyficationEncodeBHist O₂, kelleyficationEncodeBHist W₂,
                kelleyficationEncodeBHist H₂, kelleyficationEncodeBHist R₂,
                kelleyficationEncodeBHist P₂, kelleyficationEncodeBHist N₂] at heq
          injection heq with hT tailT
          injection tailT with hC tailC
          injection tailC with hO tailO
          injection tailO with hW tailW
          injection tailW with hH tailH
          injection tailH with hR tailR
          injection tailR with hP tailP
          injection tailP with hN _tailN
          have eT : T₁ = T₂ := by
            calc
              T₁ = kelleyficationDecodeBHist (kelleyficationEncodeBHist T₁) :=
                (KelleyficationTasteGate_single_carrier_alignment_decode_encode T₁).symm
              _ = kelleyficationDecodeBHist (kelleyficationEncodeBHist T₂) :=
                congrArg kelleyficationDecodeBHist hT
              _ = T₂ := KelleyficationTasteGate_single_carrier_alignment_decode_encode T₂
          have eC : C₁ = C₂ := by
            calc
              C₁ = kelleyficationDecodeBHist (kelleyficationEncodeBHist C₁) :=
                (KelleyficationTasteGate_single_carrier_alignment_decode_encode C₁).symm
              _ = kelleyficationDecodeBHist (kelleyficationEncodeBHist C₂) :=
                congrArg kelleyficationDecodeBHist hC
              _ = C₂ := KelleyficationTasteGate_single_carrier_alignment_decode_encode C₂
          have eO : O₁ = O₂ := by
            calc
              O₁ = kelleyficationDecodeBHist (kelleyficationEncodeBHist O₁) :=
                (KelleyficationTasteGate_single_carrier_alignment_decode_encode O₁).symm
              _ = kelleyficationDecodeBHist (kelleyficationEncodeBHist O₂) :=
                congrArg kelleyficationDecodeBHist hO
              _ = O₂ := KelleyficationTasteGate_single_carrier_alignment_decode_encode O₂
          have eW : W₁ = W₂ := by
            calc
              W₁ = kelleyficationDecodeBHist (kelleyficationEncodeBHist W₁) :=
                (KelleyficationTasteGate_single_carrier_alignment_decode_encode W₁).symm
              _ = kelleyficationDecodeBHist (kelleyficationEncodeBHist W₂) :=
                congrArg kelleyficationDecodeBHist hW
              _ = W₂ := KelleyficationTasteGate_single_carrier_alignment_decode_encode W₂
          have eH : H₁ = H₂ := by
            calc
              H₁ = kelleyficationDecodeBHist (kelleyficationEncodeBHist H₁) :=
                (KelleyficationTasteGate_single_carrier_alignment_decode_encode H₁).symm
              _ = kelleyficationDecodeBHist (kelleyficationEncodeBHist H₂) :=
                congrArg kelleyficationDecodeBHist hH
              _ = H₂ := KelleyficationTasteGate_single_carrier_alignment_decode_encode H₂
          have eR : R₁ = R₂ := by
            calc
              R₁ = kelleyficationDecodeBHist (kelleyficationEncodeBHist R₁) :=
                (KelleyficationTasteGate_single_carrier_alignment_decode_encode R₁).symm
              _ = kelleyficationDecodeBHist (kelleyficationEncodeBHist R₂) :=
                congrArg kelleyficationDecodeBHist hR
              _ = R₂ := KelleyficationTasteGate_single_carrier_alignment_decode_encode R₂
          have eP : P₁ = P₂ := by
            calc
              P₁ = kelleyficationDecodeBHist (kelleyficationEncodeBHist P₁) :=
                (KelleyficationTasteGate_single_carrier_alignment_decode_encode P₁).symm
              _ = kelleyficationDecodeBHist (kelleyficationEncodeBHist P₂) :=
                congrArg kelleyficationDecodeBHist hP
              _ = P₂ := KelleyficationTasteGate_single_carrier_alignment_decode_encode P₂
          have eN : N₁ = N₂ := by
            calc
              N₁ = kelleyficationDecodeBHist (kelleyficationEncodeBHist N₁) :=
                (KelleyficationTasteGate_single_carrier_alignment_decode_encode N₁).symm
              _ = kelleyficationDecodeBHist (kelleyficationEncodeBHist N₂) :=
                congrArg kelleyficationDecodeBHist hN
              _ = N₂ := KelleyficationTasteGate_single_carrier_alignment_decode_encode N₂
          subst eT
          subst eC
          subst eO
          subst eW
          subst eH
          subst eR
          subst eP
          subst eN
          rfl

instance kelleyficationBHistCarrier : BHistCarrier KelleyficationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := kelleyficationToEventFlow
  fromEventFlow := kelleyficationFromEventFlow

instance kelleyficationChapterTasteGate : ChapterTasteGate KelleyficationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change kelleyficationFromEventFlow (kelleyficationToEventFlow x) = some x
    exact KelleyficationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (KelleyficationTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate KelleyficationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  kelleyficationChapterTasteGate

theorem KelleyficationTasteGate_single_carrier_alignment :
    (∀ h : BHist, kelleyficationDecodeBHist (kelleyficationEncodeBHist h) = h) ∧
      (∀ x : KelleyficationUp,
        kelleyficationFromEventFlow (kelleyficationToEventFlow x) = some x) ∧
        (∀ x y : KelleyficationUp,
          kelleyficationToEventFlow x = kelleyficationToEventFlow y → x = y) ∧
          kelleyficationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨KelleyficationTasteGate_single_carrier_alignment_decode_encode,
      KelleyficationTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => KelleyficationTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.KelleyficationUp
