import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SRRouteDependencyAuditUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SRRouteDependencyAuditUp : Type where
  | mk (R U T F B K O H C P N : BHist) : SRRouteDependencyAuditUp
deriving DecidableEq

def srRouteDependencyAuditEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: srRouteDependencyAuditEncodeBHist h
  | BHist.e1 h => BMark.b1 :: srRouteDependencyAuditEncodeBHist h

def srRouteDependencyAuditDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (srRouteDependencyAuditDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (srRouteDependencyAuditDecodeBHist tail)

private theorem SRRouteDependencyAuditTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      srRouteDependencyAuditDecodeBHist (srRouteDependencyAuditEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def srRouteDependencyAuditFields : SRRouteDependencyAuditUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SRRouteDependencyAuditUp.mk R U T F B K O H C P N => [R, U, T, F, B, K, O, H, C, P, N]

def srRouteDependencyAuditToEventFlow : SRRouteDependencyAuditUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (srRouteDependencyAuditFields x).map srRouteDependencyAuditEncodeBHist

private def srRouteDependencyAuditEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => srRouteDependencyAuditEventAtDefault index rest

def srRouteDependencyAuditFromEventFlow (ef : EventFlow) :
    Option SRRouteDependencyAuditUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SRRouteDependencyAuditUp.mk
      (srRouteDependencyAuditDecodeBHist (srRouteDependencyAuditEventAtDefault 0 ef))
      (srRouteDependencyAuditDecodeBHist (srRouteDependencyAuditEventAtDefault 1 ef))
      (srRouteDependencyAuditDecodeBHist (srRouteDependencyAuditEventAtDefault 2 ef))
      (srRouteDependencyAuditDecodeBHist (srRouteDependencyAuditEventAtDefault 3 ef))
      (srRouteDependencyAuditDecodeBHist (srRouteDependencyAuditEventAtDefault 4 ef))
      (srRouteDependencyAuditDecodeBHist (srRouteDependencyAuditEventAtDefault 5 ef))
      (srRouteDependencyAuditDecodeBHist (srRouteDependencyAuditEventAtDefault 6 ef))
      (srRouteDependencyAuditDecodeBHist (srRouteDependencyAuditEventAtDefault 7 ef))
      (srRouteDependencyAuditDecodeBHist (srRouteDependencyAuditEventAtDefault 8 ef))
      (srRouteDependencyAuditDecodeBHist (srRouteDependencyAuditEventAtDefault 9 ef))
      (srRouteDependencyAuditDecodeBHist (srRouteDependencyAuditEventAtDefault 10 ef)))

private theorem SRRouteDependencyAuditTasteGate_single_carrier_alignment_round_trip :
    ∀ x : SRRouteDependencyAuditUp,
      srRouteDependencyAuditFromEventFlow
        (srRouteDependencyAuditToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R U T F B K O H C P N =>
      change
        some
          (SRRouteDependencyAuditUp.mk
            (srRouteDependencyAuditDecodeBHist (srRouteDependencyAuditEncodeBHist R))
            (srRouteDependencyAuditDecodeBHist (srRouteDependencyAuditEncodeBHist U))
            (srRouteDependencyAuditDecodeBHist (srRouteDependencyAuditEncodeBHist T))
            (srRouteDependencyAuditDecodeBHist (srRouteDependencyAuditEncodeBHist F))
            (srRouteDependencyAuditDecodeBHist (srRouteDependencyAuditEncodeBHist B))
            (srRouteDependencyAuditDecodeBHist (srRouteDependencyAuditEncodeBHist K))
            (srRouteDependencyAuditDecodeBHist (srRouteDependencyAuditEncodeBHist O))
            (srRouteDependencyAuditDecodeBHist (srRouteDependencyAuditEncodeBHist H))
            (srRouteDependencyAuditDecodeBHist (srRouteDependencyAuditEncodeBHist C))
            (srRouteDependencyAuditDecodeBHist (srRouteDependencyAuditEncodeBHist P))
            (srRouteDependencyAuditDecodeBHist (srRouteDependencyAuditEncodeBHist N))) =
          some (SRRouteDependencyAuditUp.mk R U T F B K O H C P N)
      rw [SRRouteDependencyAuditTasteGate_single_carrier_alignment_decode R,
        SRRouteDependencyAuditTasteGate_single_carrier_alignment_decode U,
        SRRouteDependencyAuditTasteGate_single_carrier_alignment_decode T,
        SRRouteDependencyAuditTasteGate_single_carrier_alignment_decode F,
        SRRouteDependencyAuditTasteGate_single_carrier_alignment_decode B,
        SRRouteDependencyAuditTasteGate_single_carrier_alignment_decode K,
        SRRouteDependencyAuditTasteGate_single_carrier_alignment_decode O,
        SRRouteDependencyAuditTasteGate_single_carrier_alignment_decode H,
        SRRouteDependencyAuditTasteGate_single_carrier_alignment_decode C,
        SRRouteDependencyAuditTasteGate_single_carrier_alignment_decode P,
        SRRouteDependencyAuditTasteGate_single_carrier_alignment_decode N]

private theorem SRRouteDependencyAuditTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : SRRouteDependencyAuditUp} :
    srRouteDependencyAuditToEventFlow x = srRouteDependencyAuditToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      srRouteDependencyAuditFromEventFlow (srRouteDependencyAuditToEventFlow x) =
        srRouteDependencyAuditFromEventFlow (srRouteDependencyAuditToEventFlow y) :=
    congrArg srRouteDependencyAuditFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (SRRouteDependencyAuditTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (SRRouteDependencyAuditTasteGate_single_carrier_alignment_round_trip y)))

private theorem SRRouteDependencyAuditTasteGate_single_carrier_alignment_fields :
    ∀ x y : SRRouteDependencyAuditUp,
      srRouteDependencyAuditFields x = srRouteDependencyAuditFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk R₁ U₁ T₁ F₁ B₁ K₁ O₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk R₂ U₂ T₂ F₂ B₂ K₂ O₂ H₂ C₂ P₂ N₂ =>
          injection hfields with hR tail0
          injection tail0 with hU tail1
          injection tail1 with hT tail2
          injection tail2 with hF tail3
          injection tail3 with hB tail4
          injection tail4 with hK tail5
          injection tail5 with hO tail6
          injection tail6 with hH tail7
          injection tail7 with hC tail8
          injection tail8 with hP tail9
          injection tail9 with hN _
          subst hR
          subst hU
          subst hT
          subst hF
          subst hB
          subst hK
          subst hO
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance srRouteDependencyAuditBHistCarrier :
    BHistCarrier SRRouteDependencyAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := srRouteDependencyAuditToEventFlow
  fromEventFlow := srRouteDependencyAuditFromEventFlow

instance srRouteDependencyAuditChapterTasteGate :
    ChapterTasteGate SRRouteDependencyAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change srRouteDependencyAuditFromEventFlow (srRouteDependencyAuditToEventFlow x) = some x
    exact SRRouteDependencyAuditTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (SRRouteDependencyAuditTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance srRouteDependencyAuditFieldFaithful :
    FieldFaithful SRRouteDependencyAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := srRouteDependencyAuditFields
  field_faithful := SRRouteDependencyAuditTasteGate_single_carrier_alignment_fields

instance srRouteDependencyAuditNontrivial :
    Nontrivial SRRouteDependencyAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SRRouteDependencyAuditUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      SRRouteDependencyAuditUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate SRRouteDependencyAuditUp :=
  -- BEDC touchpoint anchor: BHist BMark
  srRouteDependencyAuditChapterTasteGate

theorem SRRouteDependencyAuditTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate SRRouteDependencyAuditUp) ∧
      Nonempty (FieldFaithful SRRouteDependencyAuditUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial SRRouteDependencyAuditUp) ∧
          (∀ h : BHist,
            srRouteDependencyAuditDecodeBHist (srRouteDependencyAuditEncodeBHist h) = h) ∧
            (∀ x : SRRouteDependencyAuditUp,
              srRouteDependencyAuditFromEventFlow
                (srRouteDependencyAuditToEventFlow x) = some x) ∧
              (∀ x y : SRRouteDependencyAuditUp,
                srRouteDependencyAuditToEventFlow x =
                  srRouteDependencyAuditToEventFlow y → x = y) ∧
                srRouteDependencyAuditEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨Nonempty.intro srRouteDependencyAuditChapterTasteGate,
      Nonempty.intro srRouteDependencyAuditFieldFaithful,
      Nonempty.intro srRouteDependencyAuditNontrivial,
      SRRouteDependencyAuditTasteGate_single_carrier_alignment_decode,
      SRRouteDependencyAuditTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        SRRouteDependencyAuditTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.SRRouteDependencyAuditUp
