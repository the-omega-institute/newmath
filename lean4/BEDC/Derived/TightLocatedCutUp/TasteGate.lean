import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TightLocatedCutUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TightLocatedCutUp : Type where
  | mk (L U A B D E H C P N : BHist) : TightLocatedCutUp
  deriving DecidableEq

def tightLocatedCutEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: tightLocatedCutEncodeBHist h
  | BHist.e1 h => BMark.b1 :: tightLocatedCutEncodeBHist h

def tightLocatedCutDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (tightLocatedCutDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (tightLocatedCutDecodeBHist tail)

private theorem TightLocatedCutTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, tightLocatedCutDecodeBHist (tightLocatedCutEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def tightLocatedCutFields : TightLocatedCutUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | TightLocatedCutUp.mk L U A B D E H C P N => [L, U, A, B, D, E, H, C, P, N]

def tightLocatedCutToEventFlow : TightLocatedCutUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (tightLocatedCutFields x).map tightLocatedCutEncodeBHist

def tightLocatedCutFromEventFlow : EventFlow → Option TightLocatedCutUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | lower :: rest0 =>
      match rest0 with
      | [] => none
      | upper :: rest1 =>
          match rest1 with
          | [] => none
          | apartness :: rest2 =>
              match rest2 with
              | [] => none
              | boundedness :: rest3 =>
                  match rest3 with
                  | [] => none
                  | dyadic :: rest4 =>
                      match rest4 with
                      | [] => none
                      | realSeal :: rest5 =>
                          match rest5 with
                          | [] => none
                          | transport :: rest6 =>
                              match rest6 with
                              | [] => none
                              | replay :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | provenance :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | nameCert :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (TightLocatedCutUp.mk
                                                  (tightLocatedCutDecodeBHist lower)
                                                  (tightLocatedCutDecodeBHist upper)
                                                  (tightLocatedCutDecodeBHist apartness)
                                                  (tightLocatedCutDecodeBHist boundedness)
                                                  (tightLocatedCutDecodeBHist dyadic)
                                                  (tightLocatedCutDecodeBHist realSeal)
                                                  (tightLocatedCutDecodeBHist transport)
                                                  (tightLocatedCutDecodeBHist replay)
                                                  (tightLocatedCutDecodeBHist provenance)
                                                  (tightLocatedCutDecodeBHist nameCert))
                                          | _ :: _ => none

private theorem TightLocatedCutTasteGate_single_carrier_alignment_round_trip
    (x : TightLocatedCutUp) :
    tightLocatedCutFromEventFlow (tightLocatedCutToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk L U A B D E H C P N =>
      change
        some
          (TightLocatedCutUp.mk
            (tightLocatedCutDecodeBHist (tightLocatedCutEncodeBHist L))
            (tightLocatedCutDecodeBHist (tightLocatedCutEncodeBHist U))
            (tightLocatedCutDecodeBHist (tightLocatedCutEncodeBHist A))
            (tightLocatedCutDecodeBHist (tightLocatedCutEncodeBHist B))
            (tightLocatedCutDecodeBHist (tightLocatedCutEncodeBHist D))
            (tightLocatedCutDecodeBHist (tightLocatedCutEncodeBHist E))
            (tightLocatedCutDecodeBHist (tightLocatedCutEncodeBHist H))
            (tightLocatedCutDecodeBHist (tightLocatedCutEncodeBHist C))
            (tightLocatedCutDecodeBHist (tightLocatedCutEncodeBHist P))
            (tightLocatedCutDecodeBHist (tightLocatedCutEncodeBHist N))) =
          some (TightLocatedCutUp.mk L U A B D E H C P N)
      rw [TightLocatedCutTasteGate_single_carrier_alignment_decode_encode L,
        TightLocatedCutTasteGate_single_carrier_alignment_decode_encode U,
        TightLocatedCutTasteGate_single_carrier_alignment_decode_encode A,
        TightLocatedCutTasteGate_single_carrier_alignment_decode_encode B,
        TightLocatedCutTasteGate_single_carrier_alignment_decode_encode D,
        TightLocatedCutTasteGate_single_carrier_alignment_decode_encode E,
        TightLocatedCutTasteGate_single_carrier_alignment_decode_encode H,
        TightLocatedCutTasteGate_single_carrier_alignment_decode_encode C,
        TightLocatedCutTasteGate_single_carrier_alignment_decode_encode P,
        TightLocatedCutTasteGate_single_carrier_alignment_decode_encode N]

private theorem tightLocatedCutToEventFlow_injective {x y : TightLocatedCutUp} :
    tightLocatedCutToEventFlow x = tightLocatedCutToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      tightLocatedCutFromEventFlow (tightLocatedCutToEventFlow x) =
        tightLocatedCutFromEventFlow (tightLocatedCutToEventFlow y) :=
    congrArg tightLocatedCutFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (TightLocatedCutTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (TightLocatedCutTasteGate_single_carrier_alignment_round_trip y)))

private theorem TightLocatedCutTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : TightLocatedCutUp, tightLocatedCutFields x = tightLocatedCutFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk L₁ U₁ A₁ B₁ D₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk L₂ U₂ A₂ B₂ D₂ E₂ H₂ C₂ P₂ N₂ =>
          injection hfields with hL tail0
          injection tail0 with hU tail1
          injection tail1 with hA tail2
          injection tail2 with hB tail3
          injection tail3 with hD tail4
          injection tail4 with hE tail5
          injection tail5 with hH tail6
          injection tail6 with hC tail7
          injection tail7 with hP tail8
          injection tail8 with hN _
          subst hL
          subst hU
          subst hA
          subst hB
          subst hD
          subst hE
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance tightLocatedCutBHistCarrier : BHistCarrier TightLocatedCutUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := tightLocatedCutToEventFlow
  fromEventFlow := tightLocatedCutFromEventFlow

instance tightLocatedCutChapterTasteGate : ChapterTasteGate TightLocatedCutUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change tightLocatedCutFromEventFlow (tightLocatedCutToEventFlow x) = some x
    exact TightLocatedCutTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (tightLocatedCutToEventFlow_injective heq)

instance tightLocatedCutFieldFaithful : FieldFaithful TightLocatedCutUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := tightLocatedCutFields
  field_faithful := TightLocatedCutTasteGate_single_carrier_alignment_fields_faithful

instance tightLocatedCutNontrivial : BEDC.Meta.TasteGate.Nontrivial TightLocatedCutUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨TightLocatedCutUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      TightLocatedCutUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate TightLocatedCutUp :=
  -- BEDC touchpoint anchor: BHist BMark
  tightLocatedCutChapterTasteGate

theorem TightLocatedCutTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate TightLocatedCutUp) ∧
      Nonempty (FieldFaithful TightLocatedCutUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial TightLocatedCutUp) ∧
          (∀ h : BHist, tightLocatedCutDecodeBHist (tightLocatedCutEncodeBHist h) = h) ∧
            (∀ x : TightLocatedCutUp,
              tightLocatedCutFromEventFlow (tightLocatedCutToEventFlow x) = some x) ∧
              (∀ x y : TightLocatedCutUp,
                tightLocatedCutToEventFlow x = tightLocatedCutToEventFlow y -> x = y) ∧
                tightLocatedCutEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨tightLocatedCutChapterTasteGate⟩,
      ⟨⟨tightLocatedCutFieldFaithful⟩,
        ⟨⟨tightLocatedCutNontrivial⟩,
          TightLocatedCutTasteGate_single_carrier_alignment_decode_encode,
          TightLocatedCutTasteGate_single_carrier_alignment_round_trip,
          (fun _ _ heq => tightLocatedCutToEventFlow_injective heq),
          rfl⟩⟩⟩

end BEDC.Derived.TightLocatedCutUp
