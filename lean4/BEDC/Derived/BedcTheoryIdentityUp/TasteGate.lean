import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BedcTheoryIdentityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

/-- BEDC theory identity packet with the nine displayed BHist rows. -/
inductive BedcTheoryIdentityUp : Type where
  | mk :
      (generators equality recursors purity boundary transports routes provenance nameCert :
        BHist) →
      BedcTheoryIdentityUp
  deriving DecidableEq

def bedcTheoryIdentityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bedcTheoryIdentityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bedcTheoryIdentityEncodeBHist h

def bedcTheoryIdentityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bedcTheoryIdentityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bedcTheoryIdentityDecodeBHist tail)

private theorem bedcTheoryIdentity_decode_encode_bhist :
    ∀ h : BHist, bedcTheoryIdentityDecodeBHist (bedcTheoryIdentityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def bedcTheoryIdentityFields : BedcTheoryIdentityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BedcTheoryIdentityUp.mk generators equality recursors purity boundary transports routes
      provenance nameCert =>
      [generators, equality, recursors, purity, boundary, transports, routes, provenance,
        nameCert]

def bedcTheoryIdentityToEventFlow : BedcTheoryIdentityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (bedcTheoryIdentityFields x).map bedcTheoryIdentityEncodeBHist

def bedcTheoryIdentityFromEventFlow : EventFlow → Option BedcTheoryIdentityUp
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
                      | transports :: rest5 =>
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
                                            (BedcTheoryIdentityUp.mk
                                              (bedcTheoryIdentityDecodeBHist generators)
                                              (bedcTheoryIdentityDecodeBHist equality)
                                              (bedcTheoryIdentityDecodeBHist recursors)
                                              (bedcTheoryIdentityDecodeBHist purity)
                                              (bedcTheoryIdentityDecodeBHist boundary)
                                              (bedcTheoryIdentityDecodeBHist transports)
                                              (bedcTheoryIdentityDecodeBHist routes)
                                              (bedcTheoryIdentityDecodeBHist provenance)
                                              (bedcTheoryIdentityDecodeBHist nameCert))
                                      | _ :: _ => none

private theorem bedcTheoryIdentity_round_trip :
    ∀ x : BedcTheoryIdentityUp,
      bedcTheoryIdentityFromEventFlow (bedcTheoryIdentityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk generators equality recursors purity boundary transports routes provenance nameCert =>
      change
        some
          (BedcTheoryIdentityUp.mk
            (bedcTheoryIdentityDecodeBHist (bedcTheoryIdentityEncodeBHist generators))
            (bedcTheoryIdentityDecodeBHist (bedcTheoryIdentityEncodeBHist equality))
            (bedcTheoryIdentityDecodeBHist (bedcTheoryIdentityEncodeBHist recursors))
            (bedcTheoryIdentityDecodeBHist (bedcTheoryIdentityEncodeBHist purity))
            (bedcTheoryIdentityDecodeBHist (bedcTheoryIdentityEncodeBHist boundary))
            (bedcTheoryIdentityDecodeBHist (bedcTheoryIdentityEncodeBHist transports))
            (bedcTheoryIdentityDecodeBHist (bedcTheoryIdentityEncodeBHist routes))
            (bedcTheoryIdentityDecodeBHist (bedcTheoryIdentityEncodeBHist provenance))
            (bedcTheoryIdentityDecodeBHist (bedcTheoryIdentityEncodeBHist nameCert))) =
          some
            (BedcTheoryIdentityUp.mk generators equality recursors purity boundary transports
              routes provenance nameCert)
      rw [bedcTheoryIdentity_decode_encode_bhist generators,
        bedcTheoryIdentity_decode_encode_bhist equality,
        bedcTheoryIdentity_decode_encode_bhist recursors,
        bedcTheoryIdentity_decode_encode_bhist purity,
        bedcTheoryIdentity_decode_encode_bhist boundary,
        bedcTheoryIdentity_decode_encode_bhist transports,
        bedcTheoryIdentity_decode_encode_bhist routes,
        bedcTheoryIdentity_decode_encode_bhist provenance,
        bedcTheoryIdentity_decode_encode_bhist nameCert]

private theorem bedcTheoryIdentityToEventFlow_injective {x y : BedcTheoryIdentityUp} :
    bedcTheoryIdentityToEventFlow x = bedcTheoryIdentityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bedcTheoryIdentityFromEventFlow (bedcTheoryIdentityToEventFlow x) =
        bedcTheoryIdentityFromEventFlow (bedcTheoryIdentityToEventFlow y) :=
    congrArg bedcTheoryIdentityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (bedcTheoryIdentity_round_trip x).symm
      (Eq.trans hread (bedcTheoryIdentity_round_trip y)))

private theorem bedcTheoryIdentity_fields_faithful :
    ∀ x y : BedcTheoryIdentityUp, bedcTheoryIdentityFields x = bedcTheoryIdentityFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk generators₁ equality₁ recursors₁ purity₁ boundary₁ transports₁ routes₁ provenance₁
      nameCert₁ =>
      cases y with
      | mk generators₂ equality₂ recursors₂ purity₂ boundary₂ transports₂ routes₂ provenance₂
          nameCert₂ =>
          injection hfields with hGenerators tail0
          injection tail0 with hEquality tail1
          injection tail1 with hRecursors tail2
          injection tail2 with hPurity tail3
          injection tail3 with hBoundary tail4
          injection tail4 with hTransports tail5
          injection tail5 with hRoutes tail6
          injection tail6 with hProvenance tail7
          injection tail7 with hNameCert _
          subst hGenerators
          subst hEquality
          subst hRecursors
          subst hPurity
          subst hBoundary
          subst hTransports
          subst hRoutes
          subst hProvenance
          subst hNameCert
          rfl

instance bedcTheoryIdentityBHistCarrier : BHistCarrier BedcTheoryIdentityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bedcTheoryIdentityToEventFlow
  fromEventFlow := bedcTheoryIdentityFromEventFlow

instance bedcTheoryIdentityChapterTasteGate :
    ChapterTasteGate BedcTheoryIdentityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change bedcTheoryIdentityFromEventFlow (bedcTheoryIdentityToEventFlow x) = some x
    exact bedcTheoryIdentity_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (bedcTheoryIdentityToEventFlow_injective heq)

instance bedcTheoryIdentityFieldFaithful : FieldFaithful BedcTheoryIdentityUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bedcTheoryIdentityFields
  field_faithful := bedcTheoryIdentity_fields_faithful

def taste_gate : ChapterTasteGate BedcTheoryIdentityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change bedcTheoryIdentityFromEventFlow (bedcTheoryIdentityToEventFlow x) = some x
    exact bedcTheoryIdentity_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (bedcTheoryIdentityToEventFlow_injective heq)

theorem BedcTheoryIdentityTasteGate_single_carrier_alignment :
    (∀ h : BHist, bedcTheoryIdentityDecodeBHist (bedcTheoryIdentityEncodeBHist h) = h) ∧
      (∀ x : BedcTheoryIdentityUp,
        bedcTheoryIdentityFromEventFlow (bedcTheoryIdentityToEventFlow x) = some x) ∧
        (∀ x y : BedcTheoryIdentityUp,
          bedcTheoryIdentityToEventFlow x = bedcTheoryIdentityToEventFlow y → x = y) ∧
          bedcTheoryIdentityEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact bedcTheoryIdentity_decode_encode_bhist
  · constructor
    · exact bedcTheoryIdentity_round_trip
    · constructor
      · intro x y heq
        exact bedcTheoryIdentityToEventFlow_injective heq
      · rfl

end BEDC.Derived.BedcTheoryIdentityUp
