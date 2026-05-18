import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.QuadrantSubstrateUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive QuadrantSubstrateUp : Type where
  | mk (universality closure locator substrate contrast transport route provenance
      localNameCert : BHist) : QuadrantSubstrateUp
  deriving DecidableEq

def quadrantSubstrateEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: quadrantSubstrateEncodeBHist h
  | BHist.e1 h => BMark.b1 :: quadrantSubstrateEncodeBHist h

def quadrantSubstrateDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (quadrantSubstrateDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (quadrantSubstrateDecodeBHist tail)

private theorem quadrantSubstrateDecode_encode_bhist :
    ∀ h : BHist, quadrantSubstrateDecodeBHist (quadrantSubstrateEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def quadrantSubstrateToEventFlow : QuadrantSubstrateUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | QuadrantSubstrateUp.mk universality closure locator substrate contrast transport route
      provenance localNameCert =>
      [[BMark.b0],
        quadrantSubstrateEncodeBHist universality,
        [BMark.b1, BMark.b0],
        quadrantSubstrateEncodeBHist closure,
        [BMark.b1, BMark.b1, BMark.b0],
        quadrantSubstrateEncodeBHist locator,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        quadrantSubstrateEncodeBHist substrate,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        quadrantSubstrateEncodeBHist contrast,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        quadrantSubstrateEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        quadrantSubstrateEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        quadrantSubstrateEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        quadrantSubstrateEncodeBHist localNameCert]

def quadrantSubstrateFromEventFlow : EventFlow → Option QuadrantSubstrateUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | universality :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | closure :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | locator :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | substrate :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | contrast :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | transport :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | route :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | provenance :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | localNameCert ::
                                                                          rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (QuadrantSubstrateUp.mk
                                                                                  (quadrantSubstrateDecodeBHist
                                                                                    universality)
                                                                                  (quadrantSubstrateDecodeBHist
                                                                                    closure)
                                                                                  (quadrantSubstrateDecodeBHist
                                                                                    locator)
                                                                                  (quadrantSubstrateDecodeBHist
                                                                                    substrate)
                                                                                  (quadrantSubstrateDecodeBHist
                                                                                    contrast)
                                                                                  (quadrantSubstrateDecodeBHist
                                                                                    transport)
                                                                                  (quadrantSubstrateDecodeBHist
                                                                                    route)
                                                                                  (quadrantSubstrateDecodeBHist
                                                                                    provenance)
                                                                                  (quadrantSubstrateDecodeBHist
                                                                                    localNameCert))
                                                                          | _ :: _ => none

private theorem quadrantSubstrate_round_trip :
    ∀ x : QuadrantSubstrateUp,
      quadrantSubstrateFromEventFlow (quadrantSubstrateToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk universality closure locator substrate contrast transport route provenance localNameCert =>
      change
        some
          (QuadrantSubstrateUp.mk
            (quadrantSubstrateDecodeBHist (quadrantSubstrateEncodeBHist universality))
            (quadrantSubstrateDecodeBHist (quadrantSubstrateEncodeBHist closure))
            (quadrantSubstrateDecodeBHist (quadrantSubstrateEncodeBHist locator))
            (quadrantSubstrateDecodeBHist (quadrantSubstrateEncodeBHist substrate))
            (quadrantSubstrateDecodeBHist (quadrantSubstrateEncodeBHist contrast))
            (quadrantSubstrateDecodeBHist (quadrantSubstrateEncodeBHist transport))
            (quadrantSubstrateDecodeBHist (quadrantSubstrateEncodeBHist route))
            (quadrantSubstrateDecodeBHist (quadrantSubstrateEncodeBHist provenance))
            (quadrantSubstrateDecodeBHist (quadrantSubstrateEncodeBHist localNameCert))) =
          some
            (QuadrantSubstrateUp.mk universality closure locator substrate contrast
              transport route provenance localNameCert)
      rw [quadrantSubstrateDecode_encode_bhist universality,
        quadrantSubstrateDecode_encode_bhist closure,
        quadrantSubstrateDecode_encode_bhist locator,
        quadrantSubstrateDecode_encode_bhist substrate,
        quadrantSubstrateDecode_encode_bhist contrast,
        quadrantSubstrateDecode_encode_bhist transport,
        quadrantSubstrateDecode_encode_bhist route,
        quadrantSubstrateDecode_encode_bhist provenance,
        quadrantSubstrateDecode_encode_bhist localNameCert]

private theorem quadrantSubstrateToEventFlow_injective
    {x y : QuadrantSubstrateUp} :
    quadrantSubstrateToEventFlow x = quadrantSubstrateToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      quadrantSubstrateFromEventFlow (quadrantSubstrateToEventFlow x) =
        quadrantSubstrateFromEventFlow (quadrantSubstrateToEventFlow y) :=
    congrArg quadrantSubstrateFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (quadrantSubstrate_round_trip x).symm
      (Eq.trans hread (quadrantSubstrate_round_trip y)))

instance quadrantSubstrateBHistCarrier : BHistCarrier QuadrantSubstrateUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := quadrantSubstrateToEventFlow
  fromEventFlow := quadrantSubstrateFromEventFlow

instance quadrantSubstrateChapterTasteGate :
    ChapterTasteGate QuadrantSubstrateUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change quadrantSubstrateFromEventFlow (quadrantSubstrateToEventFlow x) = some x
    exact quadrantSubstrate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (quadrantSubstrateToEventFlow_injective heq)

def quadrantSubstrateFields : QuadrantSubstrateUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | QuadrantSubstrateUp.mk universality closure locator substrate contrast transport route
      provenance localNameCert =>
      [universality, closure, locator, substrate, contrast, transport, route, provenance,
        localNameCert]

private theorem quadrantSubstrate_field_faithful_concrete :
    ∀ x y : QuadrantSubstrateUp, quadrantSubstrateFields x = quadrantSubstrateFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk universality₁ closure₁ locator₁ substrate₁ contrast₁ transport₁ route₁ provenance₁
      localNameCert₁ =>
      cases y with
      | mk universality₂ closure₂ locator₂ substrate₂ contrast₂ transport₂ route₂ provenance₂
          localNameCert₂ =>
          simp only [quadrantSubstrateFields] at h
          injection h with hUniversality tUniversality
          injection tUniversality with hClosure tClosure
          injection tClosure with hLocator tLocator
          injection tLocator with hSubstrate tSubstrate
          injection tSubstrate with hContrast tContrast
          injection tContrast with hTransport tTransport
          injection tTransport with hRoute tRoute
          injection tRoute with hProvenance tProvenance
          injection tProvenance with hLocalNameCert _
          subst hUniversality
          subst hClosure
          subst hLocator
          subst hSubstrate
          subst hContrast
          subst hTransport
          subst hRoute
          subst hProvenance
          subst hLocalNameCert
          rfl

instance quadrantSubstrateFieldFaithful :
    FieldFaithful QuadrantSubstrateUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := quadrantSubstrateFields
  field_faithful := quadrantSubstrate_field_faithful_concrete

instance quadrantSubstrateNontrivial : Nontrivial QuadrantSubstrateUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨QuadrantSubstrateUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      QuadrantSubstrateUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate QuadrantSubstrateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  quadrantSubstrateChapterTasteGate

theorem QuadrantSubstrateTasteGate_single_carrier_alignment :
    (∀ h : BHist, quadrantSubstrateDecodeBHist (quadrantSubstrateEncodeBHist h) = h) ∧
      (∀ x : QuadrantSubstrateUp,
        quadrantSubstrateFromEventFlow (quadrantSubstrateToEventFlow x) = some x) ∧
        (∀ x y : QuadrantSubstrateUp,
          quadrantSubstrateToEventFlow x = quadrantSubstrateToEventFlow y → x = y) ∧
          quadrantSubstrateEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact quadrantSubstrateDecode_encode_bhist
  · constructor
    · exact quadrantSubstrate_round_trip
    · constructor
      · intro x y heq
        exact quadrantSubstrateToEventFlow_injective heq
      · rfl

end BEDC.Derived.QuadrantSubstrateUp
