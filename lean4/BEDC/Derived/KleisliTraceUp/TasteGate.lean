import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.KleisliTraceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive KleisliTraceUp : Type where
  | mk : (source bind trace hom transport replay provenance name : BHist) → KleisliTraceUp
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

private theorem kleisliTraceDecode_encode_bhist :
    ∀ h : BHist, kleisliTraceDecodeBHist (kleisliTraceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def kleisliTraceFields : KleisliTraceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | KleisliTraceUp.mk source bind trace hom transport replay provenance name =>
      [source, bind, trace, hom, transport, replay, provenance, name]

def kleisliTraceToEventFlow : KleisliTraceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (kleisliTraceFields x).map kleisliTraceEncodeBHist

private def kleisliTraceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => kleisliTraceEventAtDefault index rest

def kleisliTraceFromEventFlow (ef : EventFlow) : Option KleisliTraceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (KleisliTraceUp.mk
      (kleisliTraceDecodeBHist (kleisliTraceEventAtDefault 0 ef))
      (kleisliTraceDecodeBHist (kleisliTraceEventAtDefault 1 ef))
      (kleisliTraceDecodeBHist (kleisliTraceEventAtDefault 2 ef))
      (kleisliTraceDecodeBHist (kleisliTraceEventAtDefault 3 ef))
      (kleisliTraceDecodeBHist (kleisliTraceEventAtDefault 4 ef))
      (kleisliTraceDecodeBHist (kleisliTraceEventAtDefault 5 ef))
      (kleisliTraceDecodeBHist (kleisliTraceEventAtDefault 6 ef))
      (kleisliTraceDecodeBHist (kleisliTraceEventAtDefault 7 ef)))

private theorem kleisliTrace_mk_congr
    {source source' bind bind' trace trace' hom hom' transport transport' replay replay'
      provenance provenance' name name' : BHist}
    (hSource : source' = source)
    (hBind : bind' = bind)
    (hTrace : trace' = trace)
    (hHom : hom' = hom)
    (hTransport : transport' = transport)
    (hReplay : replay' = replay)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    KleisliTraceUp.mk source' bind' trace' hom' transport' replay' provenance' name' =
      KleisliTraceUp.mk source bind trace hom transport replay provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hSource
  cases hBind
  cases hTrace
  cases hHom
  cases hTransport
  cases hReplay
  cases hProvenance
  cases hName
  rfl

private theorem kleisliTrace_round_trip :
    ∀ x : KleisliTraceUp,
      kleisliTraceFromEventFlow (kleisliTraceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source bind trace hom transport replay provenance name =>
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
            (kleisliTraceDecodeBHist (kleisliTraceEncodeBHist name))) =
          some (KleisliTraceUp.mk source bind trace hom transport replay provenance name)
      exact
        congrArg some
          (kleisliTrace_mk_congr
            (kleisliTraceDecode_encode_bhist source)
            (kleisliTraceDecode_encode_bhist bind)
            (kleisliTraceDecode_encode_bhist trace)
            (kleisliTraceDecode_encode_bhist hom)
            (kleisliTraceDecode_encode_bhist transport)
            (kleisliTraceDecode_encode_bhist replay)
            (kleisliTraceDecode_encode_bhist provenance)
            (kleisliTraceDecode_encode_bhist name))

private theorem KleisliTraceToEventFlow_injective {x y : KleisliTraceUp} :
    kleisliTraceToEventFlow x = kleisliTraceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      kleisliTraceFromEventFlow (kleisliTraceToEventFlow x) =
        kleisliTraceFromEventFlow (kleisliTraceToEventFlow y) :=
    congrArg kleisliTraceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (kleisliTrace_round_trip x).symm
      (Eq.trans hread (kleisliTrace_round_trip y)))

private theorem kleisliTrace_fields_faithful :
    ∀ x y : KleisliTraceUp, kleisliTraceFields x = kleisliTraceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk source₁ bind₁ trace₁ hom₁ transport₁ replay₁ provenance₁ name₁ =>
      cases y with
      | mk source₂ bind₂ trace₂ hom₂ transport₂ replay₂ provenance₂ name₂ =>
          cases hfields
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
    exact kleisliTrace_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (KleisliTraceToEventFlow_injective heq)

instance kleisliTraceFieldFaithful : FieldFaithful KleisliTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := kleisliTraceFields
  field_faithful := kleisliTrace_fields_faithful

instance kleisliTraceNontrivial : Nontrivial KleisliTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨KleisliTraceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      KleisliTraceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate KleisliTraceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  kleisliTraceChapterTasteGate

theorem KleisliTraceTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate KleisliTraceUp) ∧
      Nonempty (FieldFaithful KleisliTraceUp) ∧
        Nonempty (Nontrivial KleisliTraceUp) ∧
          (∀ h : BHist, kleisliTraceDecodeBHist (kleisliTraceEncodeBHist h) = h) ∧
            (∀ x : KleisliTraceUp,
              kleisliTraceFromEventFlow (kleisliTraceToEventFlow x) = some x) ∧
              (∀ x y : KleisliTraceUp,
                kleisliTraceToEventFlow x = kleisliTraceToEventFlow y → x = y) ∧
                kleisliTraceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  constructor
  · exact ⟨kleisliTraceChapterTasteGate⟩
  · constructor
    · exact ⟨kleisliTraceFieldFaithful⟩
    · constructor
      · exact ⟨kleisliTraceNontrivial⟩
      · constructor
        · exact kleisliTraceDecode_encode_bhist
        · constructor
          · exact kleisliTrace_round_trip
          · constructor
            · intro x y heq
              exact KleisliTraceToEventFlow_injective heq
            · rfl

end BEDC.Derived.KleisliTraceUp
