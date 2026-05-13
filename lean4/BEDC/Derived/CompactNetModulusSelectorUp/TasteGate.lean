import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactNetModulusSelectorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactNetModulusSelectorUp : Type where
  | mk :
      (source target tolerance probeSpine centers radii moduli fold precision transports
        routes provenance name : BHist) →
      CompactNetModulusSelectorUp
  deriving DecidableEq

def compactNetModulusSelectorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactNetModulusSelectorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactNetModulusSelectorEncodeBHist h

def compactNetModulusSelectorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactNetModulusSelectorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactNetModulusSelectorDecodeBHist tail)

private theorem compactNetModulusSelectorDecode_encode_bhist :
    ∀ h : BHist,
      compactNetModulusSelectorDecodeBHist
        (compactNetModulusSelectorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def compactNetModulusSelectorFields :
    CompactNetModulusSelectorUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactNetModulusSelectorUp.mk source target tolerance probeSpine centers radii
      moduli fold precision transports routes provenance name =>
      [source, target, tolerance, probeSpine, centers, radii, moduli, fold, precision,
        transports, routes, provenance, name]

def compactNetModulusSelectorToEventFlow :
    CompactNetModulusSelectorUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (compactNetModulusSelectorFields x).map compactNetModulusSelectorEncodeBHist

def compactNetModulusSelectorFromEventFlow :
    EventFlow → Option CompactNetModulusSelectorUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | source :: rest0 =>
      match rest0 with
      | [] => none
      | target :: rest1 =>
          match rest1 with
          | [] => none
          | tolerance :: rest2 =>
              match rest2 with
              | [] => none
              | probeSpine :: rest3 =>
                  match rest3 with
                  | [] => none
                  | centers :: rest4 =>
                      match rest4 with
                      | [] => none
                      | radii :: rest5 =>
                          match rest5 with
                          | [] => none
                          | moduli :: rest6 =>
                              match rest6 with
                              | [] => none
                              | fold :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | precision :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | transports :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | routes :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | provenance :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | name :: rest12 =>
                                                      match rest12 with
                                                      | [] =>
                                                          some
                                                            (CompactNetModulusSelectorUp.mk
                                                              (compactNetModulusSelectorDecodeBHist
                                                                source)
                                                              (compactNetModulusSelectorDecodeBHist
                                                                target)
                                                              (compactNetModulusSelectorDecodeBHist
                                                                tolerance)
                                                              (compactNetModulusSelectorDecodeBHist
                                                                probeSpine)
                                                              (compactNetModulusSelectorDecodeBHist
                                                                centers)
                                                              (compactNetModulusSelectorDecodeBHist
                                                                radii)
                                                              (compactNetModulusSelectorDecodeBHist
                                                                moduli)
                                                              (compactNetModulusSelectorDecodeBHist
                                                                fold)
                                                              (compactNetModulusSelectorDecodeBHist
                                                                precision)
                                                              (compactNetModulusSelectorDecodeBHist
                                                                transports)
                                                              (compactNetModulusSelectorDecodeBHist
                                                                routes)
                                                              (compactNetModulusSelectorDecodeBHist
                                                                provenance)
                                                              (compactNetModulusSelectorDecodeBHist
                                                                name))
                                                      | _ :: _ => none

private theorem compactNetModulusSelector_round_trip :
    ∀ x : CompactNetModulusSelectorUp,
      compactNetModulusSelectorFromEventFlow
        (compactNetModulusSelectorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source target tolerance probeSpine centers radii moduli fold precision transports
      routes provenance name =>
      change
        some
          (CompactNetModulusSelectorUp.mk
            (compactNetModulusSelectorDecodeBHist
              (compactNetModulusSelectorEncodeBHist source))
            (compactNetModulusSelectorDecodeBHist
              (compactNetModulusSelectorEncodeBHist target))
            (compactNetModulusSelectorDecodeBHist
              (compactNetModulusSelectorEncodeBHist tolerance))
            (compactNetModulusSelectorDecodeBHist
              (compactNetModulusSelectorEncodeBHist probeSpine))
            (compactNetModulusSelectorDecodeBHist
              (compactNetModulusSelectorEncodeBHist centers))
            (compactNetModulusSelectorDecodeBHist
              (compactNetModulusSelectorEncodeBHist radii))
            (compactNetModulusSelectorDecodeBHist
              (compactNetModulusSelectorEncodeBHist moduli))
            (compactNetModulusSelectorDecodeBHist
              (compactNetModulusSelectorEncodeBHist fold))
            (compactNetModulusSelectorDecodeBHist
              (compactNetModulusSelectorEncodeBHist precision))
            (compactNetModulusSelectorDecodeBHist
              (compactNetModulusSelectorEncodeBHist transports))
            (compactNetModulusSelectorDecodeBHist
              (compactNetModulusSelectorEncodeBHist routes))
            (compactNetModulusSelectorDecodeBHist
              (compactNetModulusSelectorEncodeBHist provenance))
            (compactNetModulusSelectorDecodeBHist
              (compactNetModulusSelectorEncodeBHist name))) =
          some
            (CompactNetModulusSelectorUp.mk source target tolerance probeSpine centers radii
              moduli fold precision transports routes provenance name)
      rw [compactNetModulusSelectorDecode_encode_bhist source,
        compactNetModulusSelectorDecode_encode_bhist target,
        compactNetModulusSelectorDecode_encode_bhist tolerance,
        compactNetModulusSelectorDecode_encode_bhist probeSpine,
        compactNetModulusSelectorDecode_encode_bhist centers,
        compactNetModulusSelectorDecode_encode_bhist radii,
        compactNetModulusSelectorDecode_encode_bhist moduli,
        compactNetModulusSelectorDecode_encode_bhist fold,
        compactNetModulusSelectorDecode_encode_bhist precision,
        compactNetModulusSelectorDecode_encode_bhist transports,
        compactNetModulusSelectorDecode_encode_bhist routes,
        compactNetModulusSelectorDecode_encode_bhist provenance,
        compactNetModulusSelectorDecode_encode_bhist name]

private theorem compactNetModulusSelectorToEventFlow_injective
    {x y : CompactNetModulusSelectorUp} :
    compactNetModulusSelectorToEventFlow x =
      compactNetModulusSelectorToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactNetModulusSelectorFromEventFlow
          (compactNetModulusSelectorToEventFlow x) =
        compactNetModulusSelectorFromEventFlow
          (compactNetModulusSelectorToEventFlow y) :=
    congrArg compactNetModulusSelectorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (compactNetModulusSelector_round_trip x).symm
      (Eq.trans hread (compactNetModulusSelector_round_trip y)))

instance compactNetModulusSelectorBHistCarrier :
    BHistCarrier CompactNetModulusSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactNetModulusSelectorToEventFlow
  fromEventFlow := compactNetModulusSelectorFromEventFlow

instance compactNetModulusSelectorChapterTasteGate :
    ChapterTasteGate CompactNetModulusSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      compactNetModulusSelectorFromEventFlow
        (compactNetModulusSelectorToEventFlow x) = some x
    exact compactNetModulusSelector_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (compactNetModulusSelectorToEventFlow_injective heq)

def taste_gate : ChapterTasteGate CompactNetModulusSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      compactNetModulusSelectorFromEventFlow
        (compactNetModulusSelectorToEventFlow x) = some x
    exact compactNetModulusSelector_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (compactNetModulusSelectorToEventFlow_injective heq)

instance compactNetModulusSelectorFieldFaithful :
    FieldFaithful CompactNetModulusSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := compactNetModulusSelectorFields
  field_faithful := by
    intro x y h
    cases x with
    | mk source₁ target₁ tolerance₁ probeSpine₁ centers₁ radii₁ moduli₁ fold₁
        precision₁ transports₁ routes₁ provenance₁ name₁ =>
        cases y with
        | mk source₂ target₂ tolerance₂ probeSpine₂ centers₂ radii₂ moduli₂ fold₂
            precision₂ transports₂ routes₂ provenance₂ name₂ =>
            injection h with hSource hRest₁
            injection hRest₁ with hTarget hRest₂
            injection hRest₂ with hTolerance hRest₃
            injection hRest₃ with hProbeSpine hRest₄
            injection hRest₄ with hCenters hRest₅
            injection hRest₅ with hRadii hRest₆
            injection hRest₆ with hModuli hRest₇
            injection hRest₇ with hFold hRest₈
            injection hRest₈ with hPrecision hRest₉
            injection hRest₉ with hTransports hRest₁₀
            injection hRest₁₀ with hRoutes hRest₁₁
            injection hRest₁₁ with hProvenance hRest₁₂
            injection hRest₁₂ with hName _
            subst hSource
            subst hTarget
            subst hTolerance
            subst hProbeSpine
            subst hCenters
            subst hRadii
            subst hModuli
            subst hFold
            subst hPrecision
            subst hTransports
            subst hRoutes
            subst hProvenance
            subst hName
            rfl

instance compactNetModulusSelectorNontrivial :
    Nontrivial CompactNetModulusSelectorUp where
  witness_pair :=
    ⟨CompactNetModulusSelectorUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      CompactNetModulusSelectorUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem CompactNetModulusSelectorTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      compactNetModulusSelectorDecodeBHist (compactNetModulusSelectorEncodeBHist h) = h) ∧
      (∀ x : CompactNetModulusSelectorUp,
        compactNetModulusSelectorFromEventFlow
          (compactNetModulusSelectorToEventFlow x) = some x) ∧
        (∀ x y : CompactNetModulusSelectorUp,
          compactNetModulusSelectorToEventFlow x =
            compactNetModulusSelectorToEventFlow y → x = y) ∧
          compactNetModulusSelectorEncodeBHist BHist.Empty = ([] : List BMark) ∧
            (∀ x y : CompactNetModulusSelectorUp,
              compactNetModulusSelectorFields x =
                compactNetModulusSelectorFields y → x = y) ∧
              (∃ x y : CompactNetModulusSelectorUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact compactNetModulusSelectorDecode_encode_bhist
  · constructor
    · exact compactNetModulusSelector_round_trip
    · constructor
      · intro x y heq
        exact compactNetModulusSelectorToEventFlow_injective heq
      · constructor
        · rfl
        · constructor
          · intro x y h
            cases x with
            | mk source₁ target₁ tolerance₁ probeSpine₁ centers₁ radii₁ moduli₁ fold₁
                precision₁ transports₁ routes₁ provenance₁ name₁ =>
                cases y with
                | mk source₂ target₂ tolerance₂ probeSpine₂ centers₂ radii₂ moduli₂ fold₂
                    precision₂ transports₂ routes₂ provenance₂ name₂ =>
                    injection h with hSource hRest₁
                    injection hRest₁ with hTarget hRest₂
                    injection hRest₂ with hTolerance hRest₃
                    injection hRest₃ with hProbeSpine hRest₄
                    injection hRest₄ with hCenters hRest₅
                    injection hRest₅ with hRadii hRest₆
                    injection hRest₆ with hModuli hRest₇
                    injection hRest₇ with hFold hRest₈
                    injection hRest₈ with hPrecision hRest₉
                    injection hRest₉ with hTransports hRest₁₀
                    injection hRest₁₀ with hRoutes hRest₁₁
                    injection hRest₁₁ with hProvenance hRest₁₂
                    injection hRest₁₂ with hName _
                    subst hSource
                    subst hTarget
                    subst hTolerance
                    subst hProbeSpine
                    subst hCenters
                    subst hRadii
                    subst hModuli
                    subst hFold
                    subst hPrecision
                    subst hTransports
                    subst hRoutes
                    subst hProvenance
                    subst hName
                    rfl
          · exact
              ⟨CompactNetModulusSelectorUp.mk BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
                CompactNetModulusSelectorUp.mk (BHist.e0 BHist.Empty) BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
                by
                  intro h
                  cases h⟩

end BEDC.Derived.CompactNetModulusSelectorUp
