import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealityConstrainedSignatureDescentUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealityConstrainedSignatureDescentUp : Type where
  | mk :
      (schedule endpoint metric gap representation descent witness transport replay provenance
        name : BHist) →
      RealityConstrainedSignatureDescentUp
  deriving DecidableEq

def realityConstrainedSignatureDescentEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realityConstrainedSignatureDescentEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realityConstrainedSignatureDescentEncodeBHist h

def realityConstrainedSignatureDescentDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realityConstrainedSignatureDescentDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realityConstrainedSignatureDescentDecodeBHist tail)

private theorem realityConstrainedSignatureDescent_decode_encode_bhist :
    ∀ h : BHist,
      realityConstrainedSignatureDescentDecodeBHist
        (realityConstrainedSignatureDescentEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def realityConstrainedSignatureDescentFields :
    RealityConstrainedSignatureDescentUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealityConstrainedSignatureDescentUp.mk schedule endpoint metric gap representation descent
      witness transport replay provenance name =>
      [schedule, endpoint, metric, gap, representation, descent, witness, transport, replay,
        provenance, name]

def realityConstrainedSignatureDescentToEventFlow :
    RealityConstrainedSignatureDescentUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      List.map realityConstrainedSignatureDescentEncodeBHist
        (realityConstrainedSignatureDescentFields x)

def realityConstrainedSignatureDescentFromEventFlow :
    EventFlow → Option RealityConstrainedSignatureDescentUp
  -- BEDC touchpoint anchor: BHist BMark
  | [schedule, endpoint, metric, gap, representation, descent, witness, transport, replay,
      provenance, name] =>
      some
        (RealityConstrainedSignatureDescentUp.mk
          (realityConstrainedSignatureDescentDecodeBHist schedule)
          (realityConstrainedSignatureDescentDecodeBHist endpoint)
          (realityConstrainedSignatureDescentDecodeBHist metric)
          (realityConstrainedSignatureDescentDecodeBHist gap)
          (realityConstrainedSignatureDescentDecodeBHist representation)
          (realityConstrainedSignatureDescentDecodeBHist descent)
          (realityConstrainedSignatureDescentDecodeBHist witness)
          (realityConstrainedSignatureDescentDecodeBHist transport)
          (realityConstrainedSignatureDescentDecodeBHist replay)
          (realityConstrainedSignatureDescentDecodeBHist provenance)
          (realityConstrainedSignatureDescentDecodeBHist name))
  | _ => none

private theorem realityConstrainedSignatureDescent_round_trip :
    ∀ x : RealityConstrainedSignatureDescentUp,
      realityConstrainedSignatureDescentFromEventFlow
        (realityConstrainedSignatureDescentToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk schedule endpoint metric gap representation descent witness transport replay provenance name =>
      change
        some
          (RealityConstrainedSignatureDescentUp.mk
            (realityConstrainedSignatureDescentDecodeBHist
              (realityConstrainedSignatureDescentEncodeBHist schedule))
            (realityConstrainedSignatureDescentDecodeBHist
              (realityConstrainedSignatureDescentEncodeBHist endpoint))
            (realityConstrainedSignatureDescentDecodeBHist
              (realityConstrainedSignatureDescentEncodeBHist metric))
            (realityConstrainedSignatureDescentDecodeBHist
              (realityConstrainedSignatureDescentEncodeBHist gap))
            (realityConstrainedSignatureDescentDecodeBHist
              (realityConstrainedSignatureDescentEncodeBHist representation))
            (realityConstrainedSignatureDescentDecodeBHist
              (realityConstrainedSignatureDescentEncodeBHist descent))
            (realityConstrainedSignatureDescentDecodeBHist
              (realityConstrainedSignatureDescentEncodeBHist witness))
            (realityConstrainedSignatureDescentDecodeBHist
              (realityConstrainedSignatureDescentEncodeBHist transport))
            (realityConstrainedSignatureDescentDecodeBHist
              (realityConstrainedSignatureDescentEncodeBHist replay))
            (realityConstrainedSignatureDescentDecodeBHist
              (realityConstrainedSignatureDescentEncodeBHist provenance))
            (realityConstrainedSignatureDescentDecodeBHist
              (realityConstrainedSignatureDescentEncodeBHist name))) =
          some
            (RealityConstrainedSignatureDescentUp.mk schedule endpoint metric gap representation
              descent witness transport replay provenance name)
      rw [realityConstrainedSignatureDescent_decode_encode_bhist schedule,
        realityConstrainedSignatureDescent_decode_encode_bhist endpoint,
        realityConstrainedSignatureDescent_decode_encode_bhist metric,
        realityConstrainedSignatureDescent_decode_encode_bhist gap,
        realityConstrainedSignatureDescent_decode_encode_bhist representation,
        realityConstrainedSignatureDescent_decode_encode_bhist descent,
        realityConstrainedSignatureDescent_decode_encode_bhist witness,
        realityConstrainedSignatureDescent_decode_encode_bhist transport,
        realityConstrainedSignatureDescent_decode_encode_bhist replay,
        realityConstrainedSignatureDescent_decode_encode_bhist provenance,
        realityConstrainedSignatureDescent_decode_encode_bhist name]

private theorem realityConstrainedSignatureDescentToEventFlow_injective
    {x y : RealityConstrainedSignatureDescentUp} :
    realityConstrainedSignatureDescentToEventFlow x =
        realityConstrainedSignatureDescentToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realityConstrainedSignatureDescentFromEventFlow
          (realityConstrainedSignatureDescentToEventFlow x) =
        realityConstrainedSignatureDescentFromEventFlow
          (realityConstrainedSignatureDescentToEventFlow y) :=
    congrArg realityConstrainedSignatureDescentFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realityConstrainedSignatureDescent_round_trip x).symm
      (Eq.trans hread (realityConstrainedSignatureDescent_round_trip y)))

private theorem realityConstrainedSignatureDescent_field_faithful :
    ∀ x y : RealityConstrainedSignatureDescentUp,
      realityConstrainedSignatureDescentFields x = realityConstrainedSignatureDescentFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk schedule₁ endpoint₁ metric₁ gap₁ representation₁ descent₁ witness₁ transport₁ replay₁
      provenance₁ name₁ =>
      cases y with
      | mk schedule₂ endpoint₂ metric₂ gap₂ representation₂ descent₂ witness₂ transport₂ replay₂
          provenance₂ name₂ =>
          cases h
          rfl

instance realityConstrainedSignatureDescentBHistCarrier :
    BHistCarrier RealityConstrainedSignatureDescentUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realityConstrainedSignatureDescentToEventFlow
  fromEventFlow := realityConstrainedSignatureDescentFromEventFlow

instance realityConstrainedSignatureDescentChapterTasteGate :
    ChapterTasteGate RealityConstrainedSignatureDescentUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      realityConstrainedSignatureDescentFromEventFlow
        (realityConstrainedSignatureDescentToEventFlow x) = some x
    exact realityConstrainedSignatureDescent_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realityConstrainedSignatureDescentToEventFlow_injective heq)

instance realityConstrainedSignatureDescentFieldFaithful :
    FieldFaithful RealityConstrainedSignatureDescentUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realityConstrainedSignatureDescentFields
  field_faithful := realityConstrainedSignatureDescent_field_faithful

instance realityConstrainedSignatureDescentNontrivial :
    Nontrivial RealityConstrainedSignatureDescentUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealityConstrainedSignatureDescentUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealityConstrainedSignatureDescentUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RealityConstrainedSignatureDescentUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realityConstrainedSignatureDescentChapterTasteGate

theorem RealityConstrainedSignatureDescentCarrier_namecert_obligations
    (R : RealityConstrainedSignatureDescentUp) :
    SemanticNameCert
      (fun row : BHist =>
        ∃ S A M G P O W H C Q N : BHist,
          R = RealityConstrainedSignatureDescentUp.mk S A M G P O W H C Q N ∧
            hsame row H)
      (fun row : BHist =>
        ∃ S A M G P O W H C Q N : BHist,
          R = RealityConstrainedSignatureDescentUp.mk S A M G P O W H C Q N ∧
            hsame row H)
      (fun row : BHist =>
        ∃ S A M G P O W H C Q N : BHist,
          R = RealityConstrainedSignatureDescentUp.mk S A M G P O W H C Q N ∧
            hsame row H)
      hsame := by
  -- BEDC touchpoint anchor: BHist SemanticNameCert hsame NameCert
  cases R with
  | mk S A M G P O W H C Q N =>
      exact {
        core := {
          carrier_inhabited :=
            Exists.intro H ⟨S, A, M, G, P, O, W, H, C, Q, N, rfl, hsame_refl H⟩
          equiv_refl := by
            intro row _source
            exact hsame_refl row
          equiv_symm := by
            intro _row _other same
            exact hsame_symm same
          equiv_trans := by
            intro _row _middle _other sameLeft sameRight
            exact hsame_trans sameLeft sameRight
          carrier_respects_equiv := by
            intro row other same source
            have sameRow : hsame row H := by
              cases source with
              | intro S' source =>
                  cases source with
                  | intro A' source =>
                      cases source with
                      | intro M' source =>
                          cases source with
                          | intro G' source =>
                              cases source with
                              | intro P' source =>
                                  cases source with
                                  | intro O' source =>
                                      cases source with
                                      | intro W' source =>
                                          cases source with
                                          | intro H' source =>
                                              cases source with
                                              | intro C' source =>
                                                  cases source with
                                                  | intro Q' source =>
                                                      cases source with
                                                      | intro N' source =>
                                                          cases source.left
                                                          exact source.right
            exact
              ⟨S, A, M, G, P, O, W, H, C, Q, N, rfl,
                hsame_trans (hsame_symm same) sameRow⟩
        }
        pattern_sound := by
          intro _row source
          exact source
        ledger_sound := by
          intro _row source
          exact source
      }

end BEDC.Derived.RealityConstrainedSignatureDescentUp
