import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ObserverSubjectBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ObserverSubjectBoundaryUp : Type where
  | mk :
      (rows transport routes bundle signature provenance name : BHist) →
      ObserverSubjectBoundaryUp
  deriving DecidableEq

def observerSubjectBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: observerSubjectBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: observerSubjectBoundaryEncodeBHist h

def observerSubjectBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (observerSubjectBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (observerSubjectBoundaryDecodeBHist tail)

private theorem observerSubjectBoundary_decode_encode_bhist :
    ∀ h : BHist,
      observerSubjectBoundaryDecodeBHist (observerSubjectBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def observerSubjectBoundaryToEventFlow : ObserverSubjectBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ObserverSubjectBoundaryUp.mk rows transport routes bundle signature provenance name =>
      [[BMark.b0],
        observerSubjectBoundaryEncodeBHist rows,
        [BMark.b1, BMark.b0],
        observerSubjectBoundaryEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b0],
        observerSubjectBoundaryEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerSubjectBoundaryEncodeBHist bundle,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerSubjectBoundaryEncodeBHist signature,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerSubjectBoundaryEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerSubjectBoundaryEncodeBHist name]

def observerSubjectBoundaryFromEventFlow : EventFlow → Option ObserverSubjectBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | rows :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | transport :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | routes :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | bundle :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | signature :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | provenance :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | name :: rest13 =>
                                                          match rest13 with
                                                          | [] =>
                                                              some
                                                                (ObserverSubjectBoundaryUp.mk
                                                                  (observerSubjectBoundaryDecodeBHist
                                                                    rows)
                                                                  (observerSubjectBoundaryDecodeBHist
                                                                    transport)
                                                                  (observerSubjectBoundaryDecodeBHist
                                                                    routes)
                                                                  (observerSubjectBoundaryDecodeBHist
                                                                    bundle)
                                                                  (observerSubjectBoundaryDecodeBHist
                                                                    signature)
                                                                  (observerSubjectBoundaryDecodeBHist
                                                                    provenance)
                                                                  (observerSubjectBoundaryDecodeBHist
                                                                    name))
                                                          | _ :: _ => none

private theorem observerSubjectBoundary_round_trip :
    ∀ x : ObserverSubjectBoundaryUp,
      observerSubjectBoundaryFromEventFlow (observerSubjectBoundaryToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk rows transport routes bundle signature provenance name =>
      change
        some
          (ObserverSubjectBoundaryUp.mk
            (observerSubjectBoundaryDecodeBHist (observerSubjectBoundaryEncodeBHist rows))
            (observerSubjectBoundaryDecodeBHist (observerSubjectBoundaryEncodeBHist transport))
            (observerSubjectBoundaryDecodeBHist (observerSubjectBoundaryEncodeBHist routes))
            (observerSubjectBoundaryDecodeBHist (observerSubjectBoundaryEncodeBHist bundle))
            (observerSubjectBoundaryDecodeBHist (observerSubjectBoundaryEncodeBHist signature))
            (observerSubjectBoundaryDecodeBHist (observerSubjectBoundaryEncodeBHist provenance))
            (observerSubjectBoundaryDecodeBHist (observerSubjectBoundaryEncodeBHist name))) =
          some
            (ObserverSubjectBoundaryUp.mk rows transport routes bundle signature provenance name)
      rw [observerSubjectBoundary_decode_encode_bhist rows,
        observerSubjectBoundary_decode_encode_bhist transport,
        observerSubjectBoundary_decode_encode_bhist routes,
        observerSubjectBoundary_decode_encode_bhist bundle,
        observerSubjectBoundary_decode_encode_bhist signature,
        observerSubjectBoundary_decode_encode_bhist provenance,
        observerSubjectBoundary_decode_encode_bhist name]

private theorem observerSubjectBoundaryToEventFlow_injective
    {x y : ObserverSubjectBoundaryUp} :
    observerSubjectBoundaryToEventFlow x = observerSubjectBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      observerSubjectBoundaryFromEventFlow (observerSubjectBoundaryToEventFlow x) =
        observerSubjectBoundaryFromEventFlow (observerSubjectBoundaryToEventFlow y) :=
    congrArg observerSubjectBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (observerSubjectBoundary_round_trip x).symm
      (Eq.trans hread (observerSubjectBoundary_round_trip y)))

instance observerSubjectBoundaryBHistCarrier : BHistCarrier ObserverSubjectBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := observerSubjectBoundaryToEventFlow
  fromEventFlow := observerSubjectBoundaryFromEventFlow

instance observerSubjectBoundaryChapterTasteGate :
    ChapterTasteGate ObserverSubjectBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change observerSubjectBoundaryFromEventFlow (observerSubjectBoundaryToEventFlow x) =
      some x
    exact observerSubjectBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (observerSubjectBoundaryToEventFlow_injective heq)

def taste_gate : ChapterTasteGate ObserverSubjectBoundaryUp :=
  inferInstance

instance observerSubjectBoundaryFieldFaithful : FieldFaithful ObserverSubjectBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | ObserverSubjectBoundaryUp.mk rows transport routes bundle signature provenance name =>
        [rows, transport, routes, bundle, signature, provenance, name]
  field_faithful := by
    intro x y h
    cases x with
    | mk rows₁ transport₁ routes₁ bundle₁ signature₁ provenance₁ name₁ =>
        cases y with
        | mk rows₂ transport₂ routes₂ bundle₂ signature₂ provenance₂ name₂ =>
            simp only [] at h
            injection h with hRows hRest₁
            injection hRest₁ with hTransport hRest₂
            injection hRest₂ with hRoutes hRest₃
            injection hRest₃ with hBundle hRest₄
            injection hRest₄ with hSignature hRest₅
            injection hRest₅ with hProvenance hRest₆
            injection hRest₆ with hName _
            subst hRows
            subst hTransport
            subst hRoutes
            subst hBundle
            subst hSignature
            subst hProvenance
            subst hName
            rfl

theorem ObserverSubjectBoundaryTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      observerSubjectBoundaryDecodeBHist (observerSubjectBoundaryEncodeBHist h) = h) ∧
      (∀ x : ObserverSubjectBoundaryUp,
        observerSubjectBoundaryFromEventFlow (observerSubjectBoundaryToEventFlow x) =
          some x) ∧
        (∀ x y : ObserverSubjectBoundaryUp,
          observerSubjectBoundaryToEventFlow x = observerSubjectBoundaryToEventFlow y → x = y) ∧
          observerSubjectBoundaryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact observerSubjectBoundary_decode_encode_bhist
  · constructor
    · exact observerSubjectBoundary_round_trip
    · constructor
      · intro x y heq
        exact observerSubjectBoundaryToEventFlow_injective heq
      · rfl

end BEDC.Derived.ObserverSubjectBoundaryUp
