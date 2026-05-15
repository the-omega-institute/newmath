import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ApophaticKernelBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ApophaticKernelBoundaryUp : Type where
  | mk (name socket question refusal gate transport route provenance localName : BHist) :
      ApophaticKernelBoundaryUp
  deriving DecidableEq

def apophaticKernelBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: apophaticKernelBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: apophaticKernelBoundaryEncodeBHist h

def apophaticKernelBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (apophaticKernelBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (apophaticKernelBoundaryDecodeBHist tail)

private theorem apophaticKernelBoundary_decode_encode_bhist :
    ∀ h : BHist,
      apophaticKernelBoundaryDecodeBHist (apophaticKernelBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem apophaticKernelBoundary_mk_congr
    {name name' socket socket' question question' refusal refusal' gate gate'
      transport transport' route route' provenance provenance' localName localName' : BHist}
    (hName : name' = name)
    (hSocket : socket' = socket)
    (hQuestion : question' = question)
    (hRefusal : refusal' = refusal)
    (hGate : gate' = gate)
    (hTransport : transport' = transport)
    (hRoute : route' = route)
    (hProvenance : provenance' = provenance)
    (hLocalName : localName' = localName) :
    ApophaticKernelBoundaryUp.mk name' socket' question' refusal' gate' transport' route'
        provenance' localName' =
      ApophaticKernelBoundaryUp.mk name socket question refusal gate transport route
        provenance localName := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hName
  cases hSocket
  cases hQuestion
  cases hRefusal
  cases hGate
  cases hTransport
  cases hRoute
  cases hProvenance
  cases hLocalName
  rfl

def apophaticKernelBoundaryFields : ApophaticKernelBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ApophaticKernelBoundaryUp.mk name socket question refusal gate transport route
      provenance localName =>
      [name, socket, question, refusal, gate, transport, route, provenance, localName]

def apophaticKernelBoundaryToEventFlow : ApophaticKernelBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (apophaticKernelBoundaryFields x).map apophaticKernelBoundaryEncodeBHist

def apophaticKernelBoundaryFromEventFlow :
    EventFlow → Option ApophaticKernelBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | name :: rest0 =>
      match rest0 with
      | [] => none
      | socket :: rest1 =>
          match rest1 with
          | [] => none
          | question :: rest2 =>
              match rest2 with
              | [] => none
              | refusal :: rest3 =>
                  match rest3 with
                  | [] => none
                  | gate :: rest4 =>
                      match rest4 with
                      | [] => none
                      | transport :: rest5 =>
                          match rest5 with
                          | [] => none
                          | route :: rest6 =>
                              match rest6 with
                              | [] => none
                              | provenance :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | localName :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some
                                            (ApophaticKernelBoundaryUp.mk
                                              (apophaticKernelBoundaryDecodeBHist name)
                                              (apophaticKernelBoundaryDecodeBHist socket)
                                              (apophaticKernelBoundaryDecodeBHist question)
                                              (apophaticKernelBoundaryDecodeBHist refusal)
                                              (apophaticKernelBoundaryDecodeBHist gate)
                                              (apophaticKernelBoundaryDecodeBHist transport)
                                              (apophaticKernelBoundaryDecodeBHist route)
                                              (apophaticKernelBoundaryDecodeBHist provenance)
                                              (apophaticKernelBoundaryDecodeBHist
                                                localName))
                                      | _ :: _ => none

private theorem apophaticKernelBoundary_round_trip :
    ∀ x : ApophaticKernelBoundaryUp,
      apophaticKernelBoundaryFromEventFlow
        (apophaticKernelBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk name socket question refusal gate transport route provenance localName =>
      change
        some
          (ApophaticKernelBoundaryUp.mk
            (apophaticKernelBoundaryDecodeBHist
              (apophaticKernelBoundaryEncodeBHist name))
            (apophaticKernelBoundaryDecodeBHist
              (apophaticKernelBoundaryEncodeBHist socket))
            (apophaticKernelBoundaryDecodeBHist
              (apophaticKernelBoundaryEncodeBHist question))
            (apophaticKernelBoundaryDecodeBHist
              (apophaticKernelBoundaryEncodeBHist refusal))
            (apophaticKernelBoundaryDecodeBHist
              (apophaticKernelBoundaryEncodeBHist gate))
            (apophaticKernelBoundaryDecodeBHist
              (apophaticKernelBoundaryEncodeBHist transport))
            (apophaticKernelBoundaryDecodeBHist
              (apophaticKernelBoundaryEncodeBHist route))
            (apophaticKernelBoundaryDecodeBHist
              (apophaticKernelBoundaryEncodeBHist provenance))
            (apophaticKernelBoundaryDecodeBHist
              (apophaticKernelBoundaryEncodeBHist localName))) =
          some
            (ApophaticKernelBoundaryUp.mk name socket question refusal gate transport route
              provenance localName)
      exact
        congrArg some
          (apophaticKernelBoundary_mk_congr
            (apophaticKernelBoundary_decode_encode_bhist name)
            (apophaticKernelBoundary_decode_encode_bhist socket)
            (apophaticKernelBoundary_decode_encode_bhist question)
            (apophaticKernelBoundary_decode_encode_bhist refusal)
            (apophaticKernelBoundary_decode_encode_bhist gate)
            (apophaticKernelBoundary_decode_encode_bhist transport)
            (apophaticKernelBoundary_decode_encode_bhist route)
            (apophaticKernelBoundary_decode_encode_bhist provenance)
            (apophaticKernelBoundary_decode_encode_bhist localName))

private theorem apophaticKernelBoundaryToEventFlow_injective
    {x y : ApophaticKernelBoundaryUp} :
    apophaticKernelBoundaryToEventFlow x =
      apophaticKernelBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      apophaticKernelBoundaryFromEventFlow
          (apophaticKernelBoundaryToEventFlow x) =
        apophaticKernelBoundaryFromEventFlow
          (apophaticKernelBoundaryToEventFlow y) :=
    congrArg apophaticKernelBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (apophaticKernelBoundary_round_trip x).symm
      (Eq.trans hread (apophaticKernelBoundary_round_trip y)))

private theorem apophaticKernelBoundary_fields_faithful :
    ∀ x y : ApophaticKernelBoundaryUp,
      apophaticKernelBoundaryFields x = apophaticKernelBoundaryFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk name₁ socket₁ question₁ refusal₁ gate₁ transport₁ route₁ provenance₁
      localName₁ =>
      cases y with
      | mk name₂ socket₂ question₂ refusal₂ gate₂ transport₂ route₂ provenance₂
          localName₂ =>
          simp only [apophaticKernelBoundaryFields] at h
          cases h
          rfl

instance apophaticKernelBoundaryBHistCarrier :
    BHistCarrier ApophaticKernelBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := apophaticKernelBoundaryToEventFlow
  fromEventFlow := apophaticKernelBoundaryFromEventFlow

instance apophaticKernelBoundaryChapterTasteGate :
    ChapterTasteGate ApophaticKernelBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      apophaticKernelBoundaryFromEventFlow
        (apophaticKernelBoundaryToEventFlow x) = some x
    exact apophaticKernelBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (apophaticKernelBoundaryToEventFlow_injective heq)

instance apophaticKernelBoundaryFieldFaithful :
    FieldFaithful ApophaticKernelBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := apophaticKernelBoundaryFields
  field_faithful := apophaticKernelBoundary_fields_faithful

instance apophaticKernelBoundaryNontrivial :
    Nontrivial ApophaticKernelBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ApophaticKernelBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ApophaticKernelBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ApophaticKernelBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  apophaticKernelBoundaryChapterTasteGate

theorem ApophaticKernelBoundaryTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      apophaticKernelBoundaryDecodeBHist (apophaticKernelBoundaryEncodeBHist h) = h) ∧
      (∀ x : ApophaticKernelBoundaryUp,
        apophaticKernelBoundaryFromEventFlow
          (apophaticKernelBoundaryToEventFlow x) = some x) ∧
        (∀ x y : ApophaticKernelBoundaryUp,
          apophaticKernelBoundaryToEventFlow x =
            apophaticKernelBoundaryToEventFlow y → x = y) ∧
          apophaticKernelBoundaryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact apophaticKernelBoundary_decode_encode_bhist
  · constructor
    · exact apophaticKernelBoundary_round_trip
    · constructor
      · intro x y heq
        exact apophaticKernelBoundaryToEventFlow_injective heq
      · rfl

end BEDC.Derived.ApophaticKernelBoundaryUp
