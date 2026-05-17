import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.KleisliTraceUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive KleisliTraceUp : Type where
  | mk :
      (source bind trace hom transport replay provenance localName : BHist) →
        KleisliTraceUp
  deriving DecidableEq

def kleisliTraceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: kleisliTraceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: kleisliTraceEncodeBHist h

def kleisliTraceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (kleisliTraceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (kleisliTraceDecodeBHist tail)

private theorem KleisliTraceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, kleisliTraceDecodeBHist (kleisliTraceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def kleisliTraceFields : KleisliTraceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | KleisliTraceUp.mk source bind trace hom transport replay provenance localName =>
      [source, bind, trace, hom, transport, replay, provenance, localName]

def kleisliTraceToEventFlow : KleisliTraceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (kleisliTraceFields x).map kleisliTraceEncodeBHist

def kleisliTraceFromEventFlow : EventFlow → Option KleisliTraceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | source :: rest0 =>
      match rest0 with
      | [] => none
      | bind :: rest1 =>
          match rest1 with
          | [] => none
          | trace :: rest2 =>
              match rest2 with
              | [] => none
              | hom :: rest3 =>
                  match rest3 with
                  | [] => none
                  | transport :: rest4 =>
                      match rest4 with
                      | [] => none
                      | replay :: rest5 =>
                          match rest5 with
                          | [] => none
                          | provenance :: rest6 =>
                              match rest6 with
                              | [] => none
                              | localName :: rest7 =>
                                  match rest7 with
                                  | [] =>
                                      some
                                        (KleisliTraceUp.mk
                                          (kleisliTraceDecodeBHist source)
                                          (kleisliTraceDecodeBHist bind)
                                          (kleisliTraceDecodeBHist trace)
                                          (kleisliTraceDecodeBHist hom)
                                          (kleisliTraceDecodeBHist transport)
                                          (kleisliTraceDecodeBHist replay)
                                          (kleisliTraceDecodeBHist provenance)
                                          (kleisliTraceDecodeBHist localName))
                                  | _ :: _ => none

private theorem KleisliTraceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : KleisliTraceUp,
      kleisliTraceFromEventFlow (kleisliTraceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source bind trace hom transport replay provenance localName =>
      change
        some
          (KleisliTraceUp.mk
            (kleisliTraceDecodeBHist (kleisliTraceEncodeBHist source))
            (kleisliTraceDecodeBHist (kleisliTraceEncodeBHist bind))
            (kleisliTraceDecodeBHist (kleisliTraceEncodeBHist trace))
            (kleisliTraceDecodeBHist (kleisliTraceEncodeBHist hom))
            (kleisliTraceDecodeBHist (kleisliTraceEncodeBHist transport))
            (kleisliTraceDecodeBHist (kleisliTraceEncodeBHist replay))
            (kleisliTraceDecodeBHist (kleisliTraceEncodeBHist provenance))
            (kleisliTraceDecodeBHist (kleisliTraceEncodeBHist localName))) =
          some
            (KleisliTraceUp.mk source bind trace hom transport replay provenance localName)
      rw [KleisliTraceTasteGate_single_carrier_alignment_decode_encode source,
        KleisliTraceTasteGate_single_carrier_alignment_decode_encode bind,
        KleisliTraceTasteGate_single_carrier_alignment_decode_encode trace,
        KleisliTraceTasteGate_single_carrier_alignment_decode_encode hom,
        KleisliTraceTasteGate_single_carrier_alignment_decode_encode transport,
        KleisliTraceTasteGate_single_carrier_alignment_decode_encode replay,
        KleisliTraceTasteGate_single_carrier_alignment_decode_encode provenance,
        KleisliTraceTasteGate_single_carrier_alignment_decode_encode localName]

private theorem KleisliTraceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : KleisliTraceUp} :
    kleisliTraceToEventFlow x = kleisliTraceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      kleisliTraceFromEventFlow (kleisliTraceToEventFlow x) =
        kleisliTraceFromEventFlow (kleisliTraceToEventFlow y) :=
    congrArg kleisliTraceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (KleisliTraceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (KleisliTraceTasteGate_single_carrier_alignment_round_trip y)))

private theorem KleisliTraceTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : KleisliTraceUp, kleisliTraceFields x = kleisliTraceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk source₁ bind₁ trace₁ hom₁ transport₁ replay₁ provenance₁ localName₁ =>
      cases y with
      | mk source₂ bind₂ trace₂ hom₂ transport₂ replay₂ provenance₂ localName₂ =>
          injection hfields with hSource tail0
          injection tail0 with hBind tail1
          injection tail1 with hTrace tail2
          injection tail2 with hHom tail3
          injection tail3 with hTransport tail4
          injection tail4 with hReplay tail5
          injection tail5 with hProvenance tail6
          injection tail6 with hLocalName _
          subst hSource
          subst hBind
          subst hTrace
          subst hHom
          subst hTransport
          subst hReplay
          subst hProvenance
          subst hLocalName
          rfl

instance kleisliTraceBHistCarrier : BHistCarrier KleisliTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := kleisliTraceToEventFlow
  fromEventFlow := kleisliTraceFromEventFlow

instance kleisliTraceChapterTasteGate : ChapterTasteGate KleisliTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change kleisliTraceFromEventFlow (kleisliTraceToEventFlow x) = some x
    exact KleisliTraceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (KleisliTraceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance kleisliTraceFieldFaithful : FieldFaithful KleisliTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := kleisliTraceFields
  field_faithful := KleisliTraceTasteGate_single_carrier_alignment_fields_faithful

instance kleisliTraceNontrivial : Nontrivial KleisliTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨KleisliTraceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      KleisliTraceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate KleisliTraceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  kleisliTraceChapterTasteGate

def taste_gate_witness : FieldFaithful KleisliTraceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  kleisliTraceFieldFaithful

theorem KleisliTraceTasteGate_single_carrier_alignment :
    (∀ h : BHist, kleisliTraceDecodeBHist (kleisliTraceEncodeBHist h) = h) ∧
      (∀ x : KleisliTraceUp,
        kleisliTraceFromEventFlow (kleisliTraceToEventFlow x) = some x) ∧
        (∀ x y : KleisliTraceUp,
          kleisliTraceToEventFlow x = kleisliTraceToEventFlow y → x = y) ∧
          Nonempty (FieldFaithful KleisliTraceUp) ∧
            Nonempty (Nontrivial KleisliTraceUp) ∧
              kleisliTraceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨KleisliTraceTasteGate_single_carrier_alignment_decode_encode,
      KleisliTraceTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        KleisliTraceTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      ⟨kleisliTraceFieldFaithful⟩, ⟨kleisliTraceNontrivial⟩, rfl⟩

end BEDC.Derived.KleisliTraceUp.TasteGate
