import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.InterHistTransportSealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive InterHistTransportSealUp : Type where
  | mk
      (source target locality invariant observer route transport continuation provenance
        name : BHist) :
      InterHistTransportSealUp
  deriving DecidableEq

def interHistTransportSealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: interHistTransportSealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: interHistTransportSealEncodeBHist h

def interHistTransportSealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (interHistTransportSealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (interHistTransportSealDecodeBHist tail)

private theorem interHistTransportSealDecode_encode_bhist :
    ∀ h : BHist,
      interHistTransportSealDecodeBHist (interHistTransportSealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def interHistTransportSealFields : InterHistTransportSealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | InterHistTransportSealUp.mk source target locality invariant observer route transport
      continuation provenance name =>
      [source, target, locality, invariant, observer, route, transport, continuation,
        provenance, name]

def interHistTransportSealToEventFlow : InterHistTransportSealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (interHistTransportSealFields x).map interHistTransportSealEncodeBHist

def interHistTransportSealFromEventFlow :
    EventFlow → Option InterHistTransportSealUp
  -- BEDC touchpoint anchor: BHist BMark
  | [source, target, locality, invariant, observer, route, transport, continuation,
      provenance, name] =>
      some
        (InterHistTransportSealUp.mk
          (interHistTransportSealDecodeBHist source)
          (interHistTransportSealDecodeBHist target)
          (interHistTransportSealDecodeBHist locality)
          (interHistTransportSealDecodeBHist invariant)
          (interHistTransportSealDecodeBHist observer)
          (interHistTransportSealDecodeBHist route)
          (interHistTransportSealDecodeBHist transport)
          (interHistTransportSealDecodeBHist continuation)
          (interHistTransportSealDecodeBHist provenance)
          (interHistTransportSealDecodeBHist name))
  | _ => none

private theorem interHistTransportSeal_round_trip :
    ∀ x : InterHistTransportSealUp,
      interHistTransportSealFromEventFlow
        (interHistTransportSealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source target locality invariant observer route transport continuation provenance name =>
      change
        some
          (InterHistTransportSealUp.mk
            (interHistTransportSealDecodeBHist
              (interHistTransportSealEncodeBHist source))
            (interHistTransportSealDecodeBHist
              (interHistTransportSealEncodeBHist target))
            (interHistTransportSealDecodeBHist
              (interHistTransportSealEncodeBHist locality))
            (interHistTransportSealDecodeBHist
              (interHistTransportSealEncodeBHist invariant))
            (interHistTransportSealDecodeBHist
              (interHistTransportSealEncodeBHist observer))
            (interHistTransportSealDecodeBHist
              (interHistTransportSealEncodeBHist route))
            (interHistTransportSealDecodeBHist
              (interHistTransportSealEncodeBHist transport))
            (interHistTransportSealDecodeBHist
              (interHistTransportSealEncodeBHist continuation))
            (interHistTransportSealDecodeBHist
              (interHistTransportSealEncodeBHist provenance))
            (interHistTransportSealDecodeBHist
              (interHistTransportSealEncodeBHist name))) =
          some
            (InterHistTransportSealUp.mk source target locality invariant observer route
              transport continuation provenance name)
      simp only [interHistTransportSealDecode_encode_bhist]

private theorem interHistTransportSealToEventFlow_injective
    {x y : InterHistTransportSealUp} :
    interHistTransportSealToEventFlow x =
        interHistTransportSealToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      interHistTransportSealFromEventFlow (interHistTransportSealToEventFlow x) =
        interHistTransportSealFromEventFlow (interHistTransportSealToEventFlow y) :=
    congrArg interHistTransportSealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (interHistTransportSeal_round_trip x).symm
      (Eq.trans hread (interHistTransportSeal_round_trip y)))

private theorem interHistTransportSeal_field_faithful :
    ∀ x y : InterHistTransportSealUp,
      interHistTransportSealFields x = interHistTransportSealFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk source₁ target₁ locality₁ invariant₁ observer₁ route₁ transport₁ continuation₁
      provenance₁ name₁ =>
      cases y with
      | mk source₂ target₂ locality₂ invariant₂ observer₂ route₂ transport₂ continuation₂
          provenance₂ name₂ =>
          cases hfields
          rfl

instance interHistTransportSealBHistCarrier : BHistCarrier InterHistTransportSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := interHistTransportSealToEventFlow
  fromEventFlow := interHistTransportSealFromEventFlow

instance interHistTransportSealChapterTasteGate : ChapterTasteGate InterHistTransportSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change interHistTransportSealFromEventFlow (interHistTransportSealToEventFlow x) = some x
    exact interHistTransportSeal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (interHistTransportSealToEventFlow_injective heq)

instance interHistTransportSealFieldFaithful :
    FieldFaithful InterHistTransportSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := interHistTransportSealFields
  field_faithful := interHistTransportSeal_field_faithful

instance interHistTransportSealNontrivial : Nontrivial InterHistTransportSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨InterHistTransportSealUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      InterHistTransportSealUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate InterHistTransportSealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  interHistTransportSealChapterTasteGate

end BEDC.Derived.InterHistTransportSealUp
