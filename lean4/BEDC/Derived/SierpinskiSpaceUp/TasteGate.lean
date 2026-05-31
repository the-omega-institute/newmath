import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SierpinskiSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SierpinskiSpaceUp : Type where
  | mk (B O W H C P N : BHist) : SierpinskiSpaceUp
  deriving DecidableEq

def sierpinskiSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: sierpinskiSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: sierpinskiSpaceEncodeBHist h

def sierpinskiSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (sierpinskiSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (sierpinskiSpaceDecodeBHist tail)

private theorem sierpinskiSpace_decode_encode :
    ∀ h : BHist, sierpinskiSpaceDecodeBHist (sierpinskiSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def sierpinskiSpaceFields : SierpinskiSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SierpinskiSpaceUp.mk B O W H C P N => [B, O, W, H, C, P, N]

def sierpinskiSpaceToEventFlow : SierpinskiSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | SierpinskiSpaceUp.mk B O W H C P N =>
      [sierpinskiSpaceEncodeBHist B, sierpinskiSpaceEncodeBHist O,
        sierpinskiSpaceEncodeBHist W, sierpinskiSpaceEncodeBHist H,
        sierpinskiSpaceEncodeBHist C, sierpinskiSpaceEncodeBHist P,
        sierpinskiSpaceEncodeBHist N]

def sierpinskiSpaceFromEventFlow : EventFlow → Option SierpinskiSpaceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | B :: rest0 =>
      match rest0 with
      | [] => none
      | O :: rest1 =>
          match rest1 with
          | [] => none
          | W :: rest2 =>
              match rest2 with
              | [] => none
              | H :: rest3 =>
                  match rest3 with
                  | [] => none
                  | C :: rest4 =>
                      match rest4 with
                      | [] => none
                      | P :: rest5 =>
                          match rest5 with
                          | [] => none
                          | N :: rest6 =>
                              match rest6 with
                              | [] =>
                                  some
                                    (SierpinskiSpaceUp.mk
                                      (sierpinskiSpaceDecodeBHist B)
                                      (sierpinskiSpaceDecodeBHist O)
                                      (sierpinskiSpaceDecodeBHist W)
                                      (sierpinskiSpaceDecodeBHist H)
                                      (sierpinskiSpaceDecodeBHist C)
                                      (sierpinskiSpaceDecodeBHist P)
                                      (sierpinskiSpaceDecodeBHist N))
                              | _ :: _ => none

private theorem sierpinskiSpace_round_trip :
    ∀ x : SierpinskiSpaceUp,
      sierpinskiSpaceFromEventFlow (sierpinskiSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B O W H C P N =>
      rw [sierpinskiSpaceToEventFlow, sierpinskiSpaceFromEventFlow,
        sierpinskiSpace_decode_encode B, sierpinskiSpace_decode_encode O,
        sierpinskiSpace_decode_encode W, sierpinskiSpace_decode_encode H,
        sierpinskiSpace_decode_encode C, sierpinskiSpace_decode_encode P,
        sierpinskiSpace_decode_encode N]

private theorem sierpinskiSpaceToEventFlow_injective {x y : SierpinskiSpaceUp} :
    sierpinskiSpaceToEventFlow x = sierpinskiSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      sierpinskiSpaceFromEventFlow (sierpinskiSpaceToEventFlow x) =
        sierpinskiSpaceFromEventFlow (sierpinskiSpaceToEventFlow y) :=
    congrArg sierpinskiSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (sierpinskiSpace_round_trip x).symm
      (Eq.trans hread (sierpinskiSpace_round_trip y)))

private theorem sierpinskiSpace_fields_faithful :
    ∀ x y : SierpinskiSpaceUp, sierpinskiSpaceFields x = sierpinskiSpaceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk B1 O1 W1 H1 C1 P1 N1 =>
      cases y with
      | mk B2 O2 W2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance sierpinskiSpaceBHistCarrier : BHistCarrier SierpinskiSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := sierpinskiSpaceToEventFlow
  fromEventFlow := sierpinskiSpaceFromEventFlow

instance sierpinskiSpaceChapterTasteGate : ChapterTasteGate SierpinskiSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change sierpinskiSpaceFromEventFlow (sierpinskiSpaceToEventFlow x) = some x
    exact sierpinskiSpace_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (sierpinskiSpaceToEventFlow_injective heq)

instance sierpinskiSpaceFieldFaithful : FieldFaithful SierpinskiSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := sierpinskiSpaceFields
  field_faithful := sierpinskiSpace_fields_faithful

instance sierpinskiSpaceNontrivial :
    BEDC.Meta.TasteGate.Nontrivial SierpinskiSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SierpinskiSpaceUp.mk
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      SierpinskiSpaceUp.mk
        (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate SierpinskiSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  sierpinskiSpaceChapterTasteGate

theorem SierpinskiSpaceTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate SierpinskiSpaceUp) ∧
      Nonempty (FieldFaithful SierpinskiSpaceUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial SierpinskiSpaceUp) ∧
          (∀ h : BHist, sierpinskiSpaceDecodeBHist (sierpinskiSpaceEncodeBHist h) = h) ∧
            (∀ x : SierpinskiSpaceUp,
              sierpinskiSpaceFromEventFlow (sierpinskiSpaceToEventFlow x) = some x) ∧
              (∀ x y : SierpinskiSpaceUp,
                sierpinskiSpaceToEventFlow x = sierpinskiSpaceToEventFlow y → x = y) ∧
                sierpinskiSpaceEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨sierpinskiSpaceChapterTasteGate⟩,
      ⟨sierpinskiSpaceFieldFaithful⟩,
      ⟨sierpinskiSpaceNontrivial⟩,
      sierpinskiSpace_decode_encode,
      sierpinskiSpace_round_trip,
      (fun _ _ heq => sierpinskiSpaceToEventFlow_injective heq),
      rfl⟩

def SierpinskiSpaceCarrier [AskSetup] [PackageSetup]
    (truth openRow window transport replay provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  UnaryHistory truth ∧ UnaryHistory openRow ∧ UnaryHistory window ∧
    UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
      UnaryHistory localName ∧ Cont truth openRow window ∧
        Cont window transport replay ∧ PkgSig bundle provenance pkg ∧
          PkgSig bundle localName pkg

theorem SierpinskiSpaceCarrier_open_set_classifier [AskSetup] [PackageSetup]
    {truth openRow window transport replay provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SierpinskiSpaceCarrier truth openRow window transport replay provenance localName bundle pkg →
      UnaryHistory truth ∧ UnaryHistory openRow ∧ UnaryHistory window ∧
        UnaryHistory replay ∧ Cont truth openRow window ∧ Cont window transport replay ∧
          PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier
  obtain ⟨truthUnary, openUnary, windowUnary, _transportUnary, replayUnary,
    _provenanceUnary, _localNameUnary, truthOpenWindow, windowTransportReplay,
    provenanceSig, localNameSig⟩ := carrier
  exact
    ⟨truthUnary, openUnary, windowUnary, replayUnary, truthOpenWindow,
      windowTransportReplay, provenanceSig, localNameSig⟩

end BEDC.Derived.SierpinskiSpaceUp
