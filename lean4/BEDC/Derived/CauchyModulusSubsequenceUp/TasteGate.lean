import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyModulusSubsequenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyModulusSubsequenceUp : Type where
  | mk (B M T W D Q R E H C P N : BHist) : CauchyModulusSubsequenceUp
  deriving DecidableEq

def cauchyModulusSubsequenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyModulusSubsequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyModulusSubsequenceEncodeBHist h

def cauchyModulusSubsequenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyModulusSubsequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyModulusSubsequenceDecodeBHist tail)

private theorem CauchyModulusSubsequenceTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      cauchyModulusSubsequenceDecodeBHist
        (cauchyModulusSubsequenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyModulusSubsequenceFields : CauchyModulusSubsequenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyModulusSubsequenceUp.mk B M T W D Q R E H C P N =>
      [B, M, T, W, D, Q, R, E, H, C, P, N]

def cauchyModulusSubsequenceToEventFlow : CauchyModulusSubsequenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyModulusSubsequenceFields x).map cauchyModulusSubsequenceEncodeBHist

private def cauchyModulusSubsequenceEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyModulusSubsequenceEventAt index rest

def cauchyModulusSubsequenceFromEventFlow :
    EventFlow → Option CauchyModulusSubsequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun flow =>
    some
      (CauchyModulusSubsequenceUp.mk
        (cauchyModulusSubsequenceDecodeBHist (cauchyModulusSubsequenceEventAt 0 flow))
        (cauchyModulusSubsequenceDecodeBHist (cauchyModulusSubsequenceEventAt 1 flow))
        (cauchyModulusSubsequenceDecodeBHist (cauchyModulusSubsequenceEventAt 2 flow))
        (cauchyModulusSubsequenceDecodeBHist (cauchyModulusSubsequenceEventAt 3 flow))
        (cauchyModulusSubsequenceDecodeBHist (cauchyModulusSubsequenceEventAt 4 flow))
        (cauchyModulusSubsequenceDecodeBHist (cauchyModulusSubsequenceEventAt 5 flow))
        (cauchyModulusSubsequenceDecodeBHist (cauchyModulusSubsequenceEventAt 6 flow))
        (cauchyModulusSubsequenceDecodeBHist (cauchyModulusSubsequenceEventAt 7 flow))
        (cauchyModulusSubsequenceDecodeBHist (cauchyModulusSubsequenceEventAt 8 flow))
        (cauchyModulusSubsequenceDecodeBHist (cauchyModulusSubsequenceEventAt 9 flow))
        (cauchyModulusSubsequenceDecodeBHist (cauchyModulusSubsequenceEventAt 10 flow))
        (cauchyModulusSubsequenceDecodeBHist (cauchyModulusSubsequenceEventAt 11 flow)))

private theorem CauchyModulusSubsequenceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyModulusSubsequenceUp,
      cauchyModulusSubsequenceFromEventFlow
        (cauchyModulusSubsequenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B M T W D Q R E H C P N =>
      change
        some
          (CauchyModulusSubsequenceUp.mk
            (cauchyModulusSubsequenceDecodeBHist
              (cauchyModulusSubsequenceEncodeBHist B))
            (cauchyModulusSubsequenceDecodeBHist
              (cauchyModulusSubsequenceEncodeBHist M))
            (cauchyModulusSubsequenceDecodeBHist
              (cauchyModulusSubsequenceEncodeBHist T))
            (cauchyModulusSubsequenceDecodeBHist
              (cauchyModulusSubsequenceEncodeBHist W))
            (cauchyModulusSubsequenceDecodeBHist
              (cauchyModulusSubsequenceEncodeBHist D))
            (cauchyModulusSubsequenceDecodeBHist
              (cauchyModulusSubsequenceEncodeBHist Q))
            (cauchyModulusSubsequenceDecodeBHist
              (cauchyModulusSubsequenceEncodeBHist R))
            (cauchyModulusSubsequenceDecodeBHist
              (cauchyModulusSubsequenceEncodeBHist E))
            (cauchyModulusSubsequenceDecodeBHist
              (cauchyModulusSubsequenceEncodeBHist H))
            (cauchyModulusSubsequenceDecodeBHist
              (cauchyModulusSubsequenceEncodeBHist C))
            (cauchyModulusSubsequenceDecodeBHist
              (cauchyModulusSubsequenceEncodeBHist P))
            (cauchyModulusSubsequenceDecodeBHist
              (cauchyModulusSubsequenceEncodeBHist N))) =
          some (CauchyModulusSubsequenceUp.mk B M T W D Q R E H C P N)
      rw [CauchyModulusSubsequenceTasteGate_single_carrier_alignment_decode B,
        CauchyModulusSubsequenceTasteGate_single_carrier_alignment_decode M,
        CauchyModulusSubsequenceTasteGate_single_carrier_alignment_decode T,
        CauchyModulusSubsequenceTasteGate_single_carrier_alignment_decode W,
        CauchyModulusSubsequenceTasteGate_single_carrier_alignment_decode D,
        CauchyModulusSubsequenceTasteGate_single_carrier_alignment_decode Q,
        CauchyModulusSubsequenceTasteGate_single_carrier_alignment_decode R,
        CauchyModulusSubsequenceTasteGate_single_carrier_alignment_decode E,
        CauchyModulusSubsequenceTasteGate_single_carrier_alignment_decode H,
        CauchyModulusSubsequenceTasteGate_single_carrier_alignment_decode C,
        CauchyModulusSubsequenceTasteGate_single_carrier_alignment_decode P,
        CauchyModulusSubsequenceTasteGate_single_carrier_alignment_decode N]

private theorem CauchyModulusSubsequenceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyModulusSubsequenceUp} :
    cauchyModulusSubsequenceToEventFlow x = cauchyModulusSubsequenceToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyModulusSubsequenceFromEventFlow (cauchyModulusSubsequenceToEventFlow x) =
        cauchyModulusSubsequenceFromEventFlow (cauchyModulusSubsequenceToEventFlow y) :=
    congrArg cauchyModulusSubsequenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyModulusSubsequenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyModulusSubsequenceTasteGate_single_carrier_alignment_round_trip y)))

private theorem CauchyModulusSubsequenceTasteGate_single_carrier_alignment_fields :
    ∀ x y : CauchyModulusSubsequenceUp,
      cauchyModulusSubsequenceFields x = cauchyModulusSubsequenceFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk B₁ M₁ T₁ W₁ D₁ Q₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk B₂ M₂ T₂ W₂ D₂ Q₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
          injection hfields with hB tail0
          injection tail0 with hM tail1
          injection tail1 with hT tail2
          injection tail2 with hW tail3
          injection tail3 with hD tail4
          injection tail4 with hQ tail5
          injection tail5 with hR tail6
          injection tail6 with hE tail7
          injection tail7 with hH tail8
          injection tail8 with hC tail9
          injection tail9 with hP tail10
          injection tail10 with hN _
          subst hB
          subst hM
          subst hT
          subst hW
          subst hD
          subst hQ
          subst hR
          subst hE
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance cauchyModulusSubsequenceBHistCarrier :
    BHistCarrier CauchyModulusSubsequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyModulusSubsequenceToEventFlow
  fromEventFlow := cauchyModulusSubsequenceFromEventFlow

instance cauchyModulusSubsequenceChapterTasteGate :
    ChapterTasteGate CauchyModulusSubsequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyModulusSubsequenceFromEventFlow
        (cauchyModulusSubsequenceToEventFlow x) = some x
    exact CauchyModulusSubsequenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact
      hxy
        (CauchyModulusSubsequenceTasteGate_single_carrier_alignment_toEventFlow_injective
          heq)

instance cauchyModulusSubsequenceFieldFaithful :
    FieldFaithful CauchyModulusSubsequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyModulusSubsequenceFields
  field_faithful := CauchyModulusSubsequenceTasteGate_single_carrier_alignment_fields

instance cauchyModulusSubsequenceNontrivial :
    BEDC.Meta.TasteGate.Nontrivial CauchyModulusSubsequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyModulusSubsequenceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      CauchyModulusSubsequenceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchyModulusSubsequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyModulusSubsequenceChapterTasteGate

theorem CauchyModulusSubsequenceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyModulusSubsequenceDecodeBHist
        (cauchyModulusSubsequenceEncodeBHist h) = h) ∧
      (∀ x : CauchyModulusSubsequenceUp,
        cauchyModulusSubsequenceFromEventFlow
          (cauchyModulusSubsequenceToEventFlow x) = some x) ∧
        (∀ x y : CauchyModulusSubsequenceUp,
          cauchyModulusSubsequenceToEventFlow x =
              cauchyModulusSubsequenceToEventFlow y →
            x = y) ∧
          cauchyModulusSubsequenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨CauchyModulusSubsequenceTasteGate_single_carrier_alignment_decode,
      CauchyModulusSubsequenceTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        CauchyModulusSubsequenceTasteGate_single_carrier_alignment_toEventFlow_injective
          heq),
      rfl⟩

end BEDC.Derived.CauchyModulusSubsequenceUp
