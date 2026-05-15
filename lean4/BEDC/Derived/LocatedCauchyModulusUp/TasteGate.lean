import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedCauchyModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedCauchyModulusUp : Type where
  | mk :
      (stream readback radius tailModulus limitSeal realSeal transport routes provenance
        name : BHist) →
      LocatedCauchyModulusUp
  deriving DecidableEq

def locatedCauchyModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedCauchyModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedCauchyModulusEncodeBHist h

def locatedCauchyModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedCauchyModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedCauchyModulusDecodeBHist tail)

private theorem locatedCauchyModulusDecodeEncode :
    ∀ h : BHist,
      locatedCauchyModulusDecodeBHist
        (locatedCauchyModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def locatedCauchyModulusFields :
    LocatedCauchyModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedCauchyModulusUp.mk stream readback radius tailModulus limitSeal realSeal
      transport routes provenance name =>
      [stream, readback, radius, tailModulus, limitSeal, realSeal, transport, routes,
        provenance, name]

def locatedCauchyModulusToEventFlow :
    LocatedCauchyModulusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (locatedCauchyModulusFields x).map locatedCauchyModulusEncodeBHist

def locatedCauchyModulusFromEventFlow :
    EventFlow → Option LocatedCauchyModulusUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | stream :: rest0 =>
      match rest0 with
      | [] => none
      | readback :: rest1 =>
          match rest1 with
          | [] => none
          | radius :: rest2 =>
              match rest2 with
              | [] => none
              | tailModulus :: rest3 =>
                  match rest3 with
                  | [] => none
                  | limitSeal :: rest4 =>
                      match rest4 with
                      | [] => none
                      | realSeal :: rest5 =>
                          match rest5 with
                          | [] => none
                          | transport :: rest6 =>
                              match rest6 with
                              | [] => none
                              | routes :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | provenance :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | name :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (LocatedCauchyModulusUp.mk
                                                  (locatedCauchyModulusDecodeBHist stream)
                                                  (locatedCauchyModulusDecodeBHist readback)
                                                  (locatedCauchyModulusDecodeBHist radius)
                                                  (locatedCauchyModulusDecodeBHist tailModulus)
                                                  (locatedCauchyModulusDecodeBHist limitSeal)
                                                  (locatedCauchyModulusDecodeBHist realSeal)
                                                  (locatedCauchyModulusDecodeBHist transport)
                                                  (locatedCauchyModulusDecodeBHist routes)
                                                  (locatedCauchyModulusDecodeBHist provenance)
                                                  (locatedCauchyModulusDecodeBHist name))
                                          | _ :: _ => none

private theorem locatedCauchyModulusRoundTrip :
    ∀ x : LocatedCauchyModulusUp,
      locatedCauchyModulusFromEventFlow
        (locatedCauchyModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk stream readback radius tailModulus limitSeal realSeal transport routes provenance
      name =>
      change
        some
          (LocatedCauchyModulusUp.mk
            (locatedCauchyModulusDecodeBHist
              (locatedCauchyModulusEncodeBHist stream))
            (locatedCauchyModulusDecodeBHist
              (locatedCauchyModulusEncodeBHist readback))
            (locatedCauchyModulusDecodeBHist
              (locatedCauchyModulusEncodeBHist radius))
            (locatedCauchyModulusDecodeBHist
              (locatedCauchyModulusEncodeBHist tailModulus))
            (locatedCauchyModulusDecodeBHist
              (locatedCauchyModulusEncodeBHist limitSeal))
            (locatedCauchyModulusDecodeBHist
              (locatedCauchyModulusEncodeBHist realSeal))
            (locatedCauchyModulusDecodeBHist
              (locatedCauchyModulusEncodeBHist transport))
            (locatedCauchyModulusDecodeBHist
              (locatedCauchyModulusEncodeBHist routes))
            (locatedCauchyModulusDecodeBHist
              (locatedCauchyModulusEncodeBHist provenance))
            (locatedCauchyModulusDecodeBHist
              (locatedCauchyModulusEncodeBHist name))) =
          some
            (LocatedCauchyModulusUp.mk stream readback radius tailModulus limitSeal
              realSeal transport routes provenance name)
      rw [locatedCauchyModulusDecodeEncode stream,
        locatedCauchyModulusDecodeEncode readback,
        locatedCauchyModulusDecodeEncode radius,
        locatedCauchyModulusDecodeEncode tailModulus,
        locatedCauchyModulusDecodeEncode limitSeal,
        locatedCauchyModulusDecodeEncode realSeal,
        locatedCauchyModulusDecodeEncode transport,
        locatedCauchyModulusDecodeEncode routes,
        locatedCauchyModulusDecodeEncode provenance,
        locatedCauchyModulusDecodeEncode name]

private theorem locatedCauchyModulusToEventFlow_injective
    {x y : LocatedCauchyModulusUp} :
    locatedCauchyModulusToEventFlow x =
      locatedCauchyModulusToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedCauchyModulusFromEventFlow
          (locatedCauchyModulusToEventFlow x) =
        locatedCauchyModulusFromEventFlow
          (locatedCauchyModulusToEventFlow y) :=
    congrArg locatedCauchyModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (locatedCauchyModulusRoundTrip x).symm
      (Eq.trans hread (locatedCauchyModulusRoundTrip y)))

private theorem locatedCauchyModulusFieldFaithful :
    ∀ x y : LocatedCauchyModulusUp,
      locatedCauchyModulusFields x = locatedCauchyModulusFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk stream₁ readback₁ radius₁ tailModulus₁ limitSeal₁ realSeal₁ transport₁ routes₁
      provenance₁ name₁ =>
      cases y with
      | mk stream₂ readback₂ radius₂ tailModulus₂ limitSeal₂ realSeal₂ transport₂ routes₂
          provenance₂ name₂ =>
          injection h with hStream hRest₁
          injection hRest₁ with hReadback hRest₂
          injection hRest₂ with hRadius hRest₃
          injection hRest₃ with hTailModulus hRest₄
          injection hRest₄ with hLimitSeal hRest₅
          injection hRest₅ with hRealSeal hRest₆
          injection hRest₆ with hTransport hRest₇
          injection hRest₇ with hRoutes hRest₈
          injection hRest₈ with hProvenance hRest₉
          injection hRest₉ with hName _
          subst hStream
          subst hReadback
          subst hRadius
          subst hTailModulus
          subst hLimitSeal
          subst hRealSeal
          subst hTransport
          subst hRoutes
          subst hProvenance
          subst hName
          rfl

instance locatedCauchyModulusBHistCarrier :
    BHistCarrier LocatedCauchyModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedCauchyModulusToEventFlow
  fromEventFlow := locatedCauchyModulusFromEventFlow

instance locatedCauchyModulusChapterTasteGate :
    ChapterTasteGate LocatedCauchyModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      locatedCauchyModulusFromEventFlow
        (locatedCauchyModulusToEventFlow x) = some x
    exact locatedCauchyModulusRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (locatedCauchyModulusToEventFlow_injective heq)

instance locatedCauchyModulusFieldFaithfulInstance :
    FieldFaithful LocatedCauchyModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := locatedCauchyModulusFields
  field_faithful := locatedCauchyModulusFieldFaithful

instance locatedCauchyModulusNontrivial :
    Nontrivial LocatedCauchyModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LocatedCauchyModulusUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      LocatedCauchyModulusUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate LocatedCauchyModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locatedCauchyModulusChapterTasteGate

theorem LocatedCauchyModulusTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      locatedCauchyModulusDecodeBHist
        (locatedCauchyModulusEncodeBHist h) = h) ∧
      (∀ x : LocatedCauchyModulusUp,
        locatedCauchyModulusFromEventFlow
          (locatedCauchyModulusToEventFlow x) = some x) ∧
        (∀ x y : LocatedCauchyModulusUp,
          locatedCauchyModulusToEventFlow x =
            locatedCauchyModulusToEventFlow y → x = y) ∧
          locatedCauchyModulusEncodeBHist BHist.Empty = ([] : List BMark) ∧
            (∀ x y : LocatedCauchyModulusUp,
              locatedCauchyModulusFields x = locatedCauchyModulusFields y → x = y) ∧
              (∃ x y : LocatedCauchyModulusUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact locatedCauchyModulusDecodeEncode
  · constructor
    · exact locatedCauchyModulusRoundTrip
    · constructor
      · intro x y heq
        exact locatedCauchyModulusToEventFlow_injective heq
      · constructor
        · rfl
        · constructor
          · exact locatedCauchyModulusFieldFaithful
          · exact
              Exists.intro
                (LocatedCauchyModulusUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty)
                (Exists.intro
                  (LocatedCauchyModulusUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
                    BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                    BHist.Empty)
                  (by
                    intro h
                    cases h))

end BEDC.Derived.LocatedCauchyModulusUp
