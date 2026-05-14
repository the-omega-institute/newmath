import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetaCICIdentityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetaCICIdentityUp : Type where
  | mk :
      (generators equality recursors purity boundary transport routes provenance nameCert :
        BHist) →
      MetaCICIdentityUp
  deriving DecidableEq

def metaCICIdentityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metaCICIdentityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metaCICIdentityEncodeBHist h

def metaCICIdentityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metaCICIdentityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metaCICIdentityDecodeBHist tail)

private theorem metaCICIdentity_decode_encode_bhist :
    ∀ h : BHist, metaCICIdentityDecodeBHist (metaCICIdentityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def metaCICIdentityFields : MetaCICIdentityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetaCICIdentityUp.mk generators equality recursors purity boundary transport routes
      provenance nameCert =>
      [generators, equality, recursors, purity, boundary, transport, routes, provenance,
        nameCert]

def metaCICIdentityToEventFlow : MetaCICIdentityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (metaCICIdentityFields x).map metaCICIdentityEncodeBHist

def metaCICIdentityFromEventFlow : EventFlow → Option MetaCICIdentityUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | generators :: rest0 =>
      match rest0 with
      | [] => none
      | equality :: rest1 =>
          match rest1 with
          | [] => none
          | recursors :: rest2 =>
              match rest2 with
              | [] => none
              | purity :: rest3 =>
                  match rest3 with
                  | [] => none
                  | boundary :: rest4 =>
                      match rest4 with
                      | [] => none
                      | transport :: rest5 =>
                          match rest5 with
                          | [] => none
                          | routes :: rest6 =>
                              match rest6 with
                              | [] => none
                              | provenance :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | nameCert :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some
                                            (MetaCICIdentityUp.mk
                                              (metaCICIdentityDecodeBHist generators)
                                              (metaCICIdentityDecodeBHist equality)
                                              (metaCICIdentityDecodeBHist recursors)
                                              (metaCICIdentityDecodeBHist purity)
                                              (metaCICIdentityDecodeBHist boundary)
                                              (metaCICIdentityDecodeBHist transport)
                                              (metaCICIdentityDecodeBHist routes)
                                              (metaCICIdentityDecodeBHist provenance)
                                              (metaCICIdentityDecodeBHist nameCert))
                                      | _ :: _ => none

private theorem metaCICIdentity_round_trip :
    ∀ x : MetaCICIdentityUp,
      metaCICIdentityFromEventFlow (metaCICIdentityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk generators equality recursors purity boundary transport routes provenance nameCert =>
      change
        some
          (MetaCICIdentityUp.mk
            (metaCICIdentityDecodeBHist (metaCICIdentityEncodeBHist generators))
            (metaCICIdentityDecodeBHist (metaCICIdentityEncodeBHist equality))
            (metaCICIdentityDecodeBHist (metaCICIdentityEncodeBHist recursors))
            (metaCICIdentityDecodeBHist (metaCICIdentityEncodeBHist purity))
            (metaCICIdentityDecodeBHist (metaCICIdentityEncodeBHist boundary))
            (metaCICIdentityDecodeBHist (metaCICIdentityEncodeBHist transport))
            (metaCICIdentityDecodeBHist (metaCICIdentityEncodeBHist routes))
            (metaCICIdentityDecodeBHist (metaCICIdentityEncodeBHist provenance))
            (metaCICIdentityDecodeBHist (metaCICIdentityEncodeBHist nameCert))) =
          some
            (MetaCICIdentityUp.mk generators equality recursors purity boundary transport routes
              provenance nameCert)
      rw [metaCICIdentity_decode_encode_bhist generators,
        metaCICIdentity_decode_encode_bhist equality,
        metaCICIdentity_decode_encode_bhist recursors,
        metaCICIdentity_decode_encode_bhist purity,
        metaCICIdentity_decode_encode_bhist boundary,
        metaCICIdentity_decode_encode_bhist transport,
        metaCICIdentity_decode_encode_bhist routes,
        metaCICIdentity_decode_encode_bhist provenance,
        metaCICIdentity_decode_encode_bhist nameCert]

private theorem metaCICIdentityToEventFlow_injective {x y : MetaCICIdentityUp} :
    metaCICIdentityToEventFlow x = metaCICIdentityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metaCICIdentityFromEventFlow (metaCICIdentityToEventFlow x) =
        metaCICIdentityFromEventFlow (metaCICIdentityToEventFlow y) :=
    congrArg metaCICIdentityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (metaCICIdentity_round_trip x).symm
      (Eq.trans hread (metaCICIdentity_round_trip y)))

private theorem metaCICIdentity_fields_faithful :
    ∀ x y : MetaCICIdentityUp, metaCICIdentityFields x = metaCICIdentityFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk generators₁ equality₁ recursors₁ purity₁ boundary₁ transport₁ routes₁ provenance₁
      nameCert₁ =>
      cases y with
      | mk generators₂ equality₂ recursors₂ purity₂ boundary₂ transport₂ routes₂ provenance₂
          nameCert₂ =>
          injection hfields with hGenerators tail0
          injection tail0 with hEquality tail1
          injection tail1 with hRecursors tail2
          injection tail2 with hPurity tail3
          injection tail3 with hBoundary tail4
          injection tail4 with hTransport tail5
          injection tail5 with hRoutes tail6
          injection tail6 with hProvenance tail7
          injection tail7 with hNameCert _
          subst hGenerators
          subst hEquality
          subst hRecursors
          subst hPurity
          subst hBoundary
          subst hTransport
          subst hRoutes
          subst hProvenance
          subst hNameCert
          rfl

instance metaCICIdentityBHistCarrier : BHistCarrier MetaCICIdentityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metaCICIdentityToEventFlow
  fromEventFlow := metaCICIdentityFromEventFlow

instance metaCICIdentityChapterTasteGate :
    ChapterTasteGate MetaCICIdentityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change metaCICIdentityFromEventFlow (metaCICIdentityToEventFlow x) = some x
    exact metaCICIdentity_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metaCICIdentityToEventFlow_injective heq)

instance metaCICIdentityFieldFaithful : FieldFaithful MetaCICIdentityUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := metaCICIdentityFields
  field_faithful := metaCICIdentity_fields_faithful

def taste_gate : ChapterTasteGate MetaCICIdentityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change metaCICIdentityFromEventFlow (metaCICIdentityToEventFlow x) = some x
    exact metaCICIdentity_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metaCICIdentityToEventFlow_injective heq)

theorem MetaCICIdentityTasteGate_single_carrier_alignment :
    (∀ h : BHist, metaCICIdentityDecodeBHist (metaCICIdentityEncodeBHist h) = h) ∧
      (∀ x : MetaCICIdentityUp,
        metaCICIdentityFromEventFlow (metaCICIdentityToEventFlow x) = some x) ∧
        (∀ x y : MetaCICIdentityUp,
          metaCICIdentityToEventFlow x = metaCICIdentityToEventFlow y -> x = y) ∧
          metaCICIdentityEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact metaCICIdentity_decode_encode_bhist
  · constructor
    · exact metaCICIdentity_round_trip
    · constructor
      · intro x y heq
        exact metaCICIdentityToEventFlow_injective heq
      · rfl

end BEDC.Derived.MetaCICIdentityUp
