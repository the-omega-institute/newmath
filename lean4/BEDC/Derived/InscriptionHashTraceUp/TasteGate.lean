import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.InscriptionHashTraceUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive InscriptionHashTraceUp : Type where
  | mk :
      (digest inscription classifier refusal audit transport continuation provenance
        name : BHist) → InscriptionHashTraceUp
  deriving DecidableEq

def inscriptionHashTraceEncodeBHist : BHist → RawEvent
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: inscriptionHashTraceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: inscriptionHashTraceEncodeBHist h

def inscriptionHashTraceDecodeBHist : RawEvent → BHist
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (inscriptionHashTraceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (inscriptionHashTraceDecodeBHist tail)

private theorem inscriptionHashTraceDecodeEncodeBHist :
    ∀ h : BHist,
      inscriptionHashTraceDecodeBHist
        (inscriptionHashTraceEncodeBHist h) = h := by
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def inscriptionHashTraceFields : InscriptionHashTraceUp → List BHist
  | InscriptionHashTraceUp.mk digest inscription classifier refusal audit transport
      continuation provenance name =>
      [digest, inscription, classifier, refusal, audit, transport, continuation,
        provenance, name]

def inscriptionHashTraceToEventFlow : InscriptionHashTraceUp → EventFlow
  | x => (inscriptionHashTraceFields x).map inscriptionHashTraceEncodeBHist

def inscriptionHashTraceFromEventFlow : EventFlow → Option InscriptionHashTraceUp
  | [] => none
  | _a :: [] => none
  | _a :: _b :: [] => none
  | _a :: _b :: _c :: [] => none
  | _a :: _b :: _c :: _d :: [] => none
  | _a :: _b :: _c :: _d :: _e :: [] => none
  | _a :: _b :: _c :: _d :: _e :: _f :: [] => none
  | _a :: _b :: _c :: _d :: _e :: _f :: _g :: [] => none
  | _a :: _b :: _c :: _d :: _e :: _f :: _g :: _h :: [] => none
  | digest :: inscription :: classifier :: refusal :: audit :: transport ::
      continuation :: provenance :: name :: [] =>
      some
        (InscriptionHashTraceUp.mk
          (inscriptionHashTraceDecodeBHist digest)
          (inscriptionHashTraceDecodeBHist inscription)
          (inscriptionHashTraceDecodeBHist classifier)
          (inscriptionHashTraceDecodeBHist refusal)
          (inscriptionHashTraceDecodeBHist audit)
          (inscriptionHashTraceDecodeBHist transport)
          (inscriptionHashTraceDecodeBHist continuation)
          (inscriptionHashTraceDecodeBHist provenance)
          (inscriptionHashTraceDecodeBHist name))
  | _a :: _b :: _c :: _d :: _e :: _f :: _g :: _h :: _i :: _j :: _rest => none

private theorem inscriptionHashTraceRoundTrip :
    ∀ x : InscriptionHashTraceUp,
      inscriptionHashTraceFromEventFlow
        (inscriptionHashTraceToEventFlow x) = some x := by
  intro x
  cases x with
  | mk digest inscription classifier refusal audit transport continuation provenance
      name =>
      change
        some
          (InscriptionHashTraceUp.mk
            (inscriptionHashTraceDecodeBHist
              (inscriptionHashTraceEncodeBHist digest))
            (inscriptionHashTraceDecodeBHist
              (inscriptionHashTraceEncodeBHist inscription))
            (inscriptionHashTraceDecodeBHist
              (inscriptionHashTraceEncodeBHist classifier))
            (inscriptionHashTraceDecodeBHist
              (inscriptionHashTraceEncodeBHist refusal))
            (inscriptionHashTraceDecodeBHist
              (inscriptionHashTraceEncodeBHist audit))
            (inscriptionHashTraceDecodeBHist
              (inscriptionHashTraceEncodeBHist transport))
            (inscriptionHashTraceDecodeBHist
              (inscriptionHashTraceEncodeBHist continuation))
            (inscriptionHashTraceDecodeBHist
              (inscriptionHashTraceEncodeBHist provenance))
            (inscriptionHashTraceDecodeBHist
              (inscriptionHashTraceEncodeBHist name))) =
          some
            (InscriptionHashTraceUp.mk digest inscription classifier refusal audit
              transport continuation provenance name)
      rw [inscriptionHashTraceDecodeEncodeBHist digest,
        inscriptionHashTraceDecodeEncodeBHist inscription,
        inscriptionHashTraceDecodeEncodeBHist classifier,
        inscriptionHashTraceDecodeEncodeBHist refusal,
        inscriptionHashTraceDecodeEncodeBHist audit,
        inscriptionHashTraceDecodeEncodeBHist transport,
        inscriptionHashTraceDecodeEncodeBHist continuation,
        inscriptionHashTraceDecodeEncodeBHist provenance,
        inscriptionHashTraceDecodeEncodeBHist name]

private theorem inscriptionHashTraceToEventFlowInjective
    {x y : InscriptionHashTraceUp} :
    inscriptionHashTraceToEventFlow x =
      inscriptionHashTraceToEventFlow y → x = y := by
  intro heq
  have hread :
      inscriptionHashTraceFromEventFlow
          (inscriptionHashTraceToEventFlow x) =
        inscriptionHashTraceFromEventFlow
          (inscriptionHashTraceToEventFlow y) :=
    congrArg inscriptionHashTraceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (inscriptionHashTraceRoundTrip x).symm
      (Eq.trans hread (inscriptionHashTraceRoundTrip y)))

private theorem inscriptionHashTraceFieldsFaithful :
    ∀ x y : InscriptionHashTraceUp,
      inscriptionHashTraceFields x = inscriptionHashTraceFields y → x = y := by
  intro x y hfields
  cases x with
  | mk digest inscription classifier refusal audit transport continuation provenance
      name =>
      cases y with
      | mk digest' inscription' classifier' refusal' audit' transport' continuation'
          provenance' name' =>
          cases hfields
          rfl

instance inscriptionHashTraceBHistCarrier :
    BHistCarrier InscriptionHashTraceUp where
  toEventFlow := inscriptionHashTraceToEventFlow
  fromEventFlow := inscriptionHashTraceFromEventFlow

instance inscriptionHashTraceChapterTasteGate :
    ChapterTasteGate InscriptionHashTraceUp where
  round_trip := by
    intro x
    change
      inscriptionHashTraceFromEventFlow
        (inscriptionHashTraceToEventFlow x) = some x
    exact inscriptionHashTraceRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (inscriptionHashTraceToEventFlowInjective heq)

instance inscriptionHashTraceFieldFaithful :
    FieldFaithful InscriptionHashTraceUp where
  fields := inscriptionHashTraceFields
  field_faithful := inscriptionHashTraceFieldsFaithful

instance inscriptionHashTraceNontrivial :
    Nontrivial InscriptionHashTraceUp where
  witness_pair :=
    ⟨InscriptionHashTraceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      InscriptionHashTraceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate InscriptionHashTraceUp :=
  inscriptionHashTraceChapterTasteGate

theorem InscriptionHashTraceTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate InscriptionHashTraceUp) ∧
      Nonempty (FieldFaithful InscriptionHashTraceUp) ∧
      Nonempty (Nontrivial InscriptionHashTraceUp) ∧
      (∀ h : BHist,
        inscriptionHashTraceDecodeBHist
          (inscriptionHashTraceEncodeBHist h) = h) ∧
      (∀ x : InscriptionHashTraceUp,
        inscriptionHashTraceFromEventFlow
          (inscriptionHashTraceToEventFlow x) = some x) ∧
      (∀ x y : InscriptionHashTraceUp,
        inscriptionHashTraceToEventFlow x =
          inscriptionHashTraceToEventFlow y → x = y) := by
  exact
    ⟨⟨inscriptionHashTraceChapterTasteGate⟩,
      ⟨inscriptionHashTraceFieldFaithful⟩,
      ⟨inscriptionHashTraceNontrivial⟩,
      inscriptionHashTraceDecodeEncodeBHist,
      inscriptionHashTraceRoundTrip,
      fun x y heq => inscriptionHashTraceToEventFlowInjective heq⟩

end BEDC.Derived.InscriptionHashTraceUp.TasteGate
