import BEDC.Derived.DecimalIntervalRealUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DecimalIntervalRealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def decimalIntervalRealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: decimalIntervalRealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: decimalIntervalRealEncodeBHist h

def decimalIntervalRealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (decimalIntervalRealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (decimalIntervalRealDecodeBHist tail)

private theorem decimalIntervalRealDecodeEncode :
    ∀ h : BHist, decimalIntervalRealDecodeBHist (decimalIntervalRealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def decimalIntervalRealFields : DecimalIntervalRealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DecimalIntervalRealUp.mk lower upper tolerance windows bracket readback realSeal
      locatedRow transport replay provenance name =>
      [lower, upper, tolerance, windows, bracket, readback, realSeal, locatedRow, transport,
        replay, provenance, name]

def decimalIntervalRealToEventFlow : DecimalIntervalRealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (decimalIntervalRealFields x).map decimalIntervalRealEncodeBHist

def decimalIntervalRealFromEventFlow : EventFlow → Option DecimalIntervalRealUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | lower :: rest0 =>
      match rest0 with
      | [] => none
      | upper :: rest1 =>
          match rest1 with
          | [] => none
          | tolerance :: rest2 =>
              match rest2 with
              | [] => none
              | windows :: rest3 =>
                  match rest3 with
                  | [] => none
                  | bracket :: rest4 =>
                      match rest4 with
                      | [] => none
                      | readback :: rest5 =>
                          match rest5 with
                          | [] => none
                          | realSeal :: rest6 =>
                              match rest6 with
                              | [] => none
                              | locatedRow :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | transport :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | replay :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | provenance :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | name :: rest11 =>
                                                  match rest11 with
                                                  | [] =>
                                                      some
                                                        (DecimalIntervalRealUp.mk
                                                          (decimalIntervalRealDecodeBHist lower)
                                                          (decimalIntervalRealDecodeBHist upper)
                                                          (decimalIntervalRealDecodeBHist
                                                            tolerance)
                                                          (decimalIntervalRealDecodeBHist
                                                            windows)
                                                          (decimalIntervalRealDecodeBHist
                                                            bracket)
                                                          (decimalIntervalRealDecodeBHist
                                                            readback)
                                                          (decimalIntervalRealDecodeBHist
                                                            realSeal)
                                                          (decimalIntervalRealDecodeBHist
                                                            locatedRow)
                                                          (decimalIntervalRealDecodeBHist
                                                            transport)
                                                          (decimalIntervalRealDecodeBHist replay)
                                                          (decimalIntervalRealDecodeBHist
                                                            provenance)
                                                          (decimalIntervalRealDecodeBHist name))
                                                  | _ :: _ => none

private theorem decimalIntervalRealRoundTrip (x : DecimalIntervalRealUp) :
    decimalIntervalRealFromEventFlow (decimalIntervalRealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk lower upper tolerance windows bracket readback realSeal locatedRow transport replay
      provenance name =>
      change
        some
          (DecimalIntervalRealUp.mk
            (decimalIntervalRealDecodeBHist (decimalIntervalRealEncodeBHist lower))
            (decimalIntervalRealDecodeBHist (decimalIntervalRealEncodeBHist upper))
            (decimalIntervalRealDecodeBHist (decimalIntervalRealEncodeBHist tolerance))
            (decimalIntervalRealDecodeBHist (decimalIntervalRealEncodeBHist windows))
            (decimalIntervalRealDecodeBHist (decimalIntervalRealEncodeBHist bracket))
            (decimalIntervalRealDecodeBHist (decimalIntervalRealEncodeBHist readback))
            (decimalIntervalRealDecodeBHist (decimalIntervalRealEncodeBHist realSeal))
            (decimalIntervalRealDecodeBHist (decimalIntervalRealEncodeBHist locatedRow))
            (decimalIntervalRealDecodeBHist (decimalIntervalRealEncodeBHist transport))
            (decimalIntervalRealDecodeBHist (decimalIntervalRealEncodeBHist replay))
            (decimalIntervalRealDecodeBHist (decimalIntervalRealEncodeBHist provenance))
            (decimalIntervalRealDecodeBHist (decimalIntervalRealEncodeBHist name))) =
          some
            (DecimalIntervalRealUp.mk lower upper tolerance windows bracket readback realSeal
              locatedRow transport replay provenance name)
      rw [decimalIntervalRealDecodeEncode lower, decimalIntervalRealDecodeEncode upper,
        decimalIntervalRealDecodeEncode tolerance, decimalIntervalRealDecodeEncode windows,
        decimalIntervalRealDecodeEncode bracket, decimalIntervalRealDecodeEncode readback,
        decimalIntervalRealDecodeEncode realSeal, decimalIntervalRealDecodeEncode locatedRow,
        decimalIntervalRealDecodeEncode transport, decimalIntervalRealDecodeEncode replay,
        decimalIntervalRealDecodeEncode provenance, decimalIntervalRealDecodeEncode name]

private theorem decimalIntervalRealToEventFlow_injective
    {x y : DecimalIntervalRealUp} :
    decimalIntervalRealToEventFlow x = decimalIntervalRealToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      decimalIntervalRealFromEventFlow (decimalIntervalRealToEventFlow x) =
        decimalIntervalRealFromEventFlow (decimalIntervalRealToEventFlow y) :=
    congrArg decimalIntervalRealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (decimalIntervalRealRoundTrip x).symm
      (Eq.trans hread (decimalIntervalRealRoundTrip y)))

private theorem decimalIntervalRealFields_faithful :
    ∀ x y : DecimalIntervalRealUp,
      decimalIntervalRealFields x = decimalIntervalRealFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk lower₁ upper₁ tolerance₁ windows₁ bracket₁ readback₁ realSeal₁ locatedRow₁
      transport₁ replay₁ provenance₁ name₁ =>
      cases y with
      | mk lower₂ upper₂ tolerance₂ windows₂ bracket₂ readback₂ realSeal₂ locatedRow₂
          transport₂ replay₂ provenance₂ name₂ =>
          injection hfields with hLower tail0
          injection tail0 with hUpper tail1
          injection tail1 with hTolerance tail2
          injection tail2 with hWindows tail3
          injection tail3 with hBracket tail4
          injection tail4 with hReadback tail5
          injection tail5 with hRealSeal tail6
          injection tail6 with hLocatedRow tail7
          injection tail7 with hTransport tail8
          injection tail8 with hReplay tail9
          injection tail9 with hProvenance tail10
          injection tail10 with hName _
          subst hLower
          subst hUpper
          subst hTolerance
          subst hWindows
          subst hBracket
          subst hReadback
          subst hRealSeal
          subst hLocatedRow
          subst hTransport
          subst hReplay
          subst hProvenance
          subst hName
          rfl

instance decimalIntervalRealBHistCarrier : BHistCarrier DecimalIntervalRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := decimalIntervalRealToEventFlow
  fromEventFlow := decimalIntervalRealFromEventFlow

instance decimalIntervalRealChapterTasteGate : ChapterTasteGate DecimalIntervalRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := decimalIntervalRealRoundTrip
  layer_separation := by
    intro x y hxy heq
    exact hxy (decimalIntervalRealToEventFlow_injective heq)

instance decimalIntervalRealFieldFaithful : FieldFaithful DecimalIntervalRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := decimalIntervalRealFields
  field_faithful := decimalIntervalRealFields_faithful

instance decimalIntervalRealNontrivial : BEDC.Meta.TasteGate.Nontrivial DecimalIntervalRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DecimalIntervalRealUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DecimalIntervalRealUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        injection h with hLower
        cases hLower⟩

def decimalIntervalReal_taste_gate : ChapterTasteGate DecimalIntervalRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := decimalIntervalRealRoundTrip
  layer_separation := by
    intro x y hxy heq
    exact hxy (decimalIntervalRealToEventFlow_injective heq)

theorem DecimalIntervalRealTasteGate_single_carrier_alignment :
    (∀ h : BHist, decimalIntervalRealDecodeBHist (decimalIntervalRealEncodeBHist h) = h) ∧
      (∀ x : DecimalIntervalRealUp,
        decimalIntervalRealFromEventFlow (decimalIntervalRealToEventFlow x) = some x) ∧
        (∀ x y : DecimalIntervalRealUp,
          decimalIntervalRealToEventFlow x = decimalIntervalRealToEventFlow y → x = y) ∧
          decimalIntervalRealEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact decimalIntervalRealDecodeEncode
  · constructor
    · exact decimalIntervalRealRoundTrip
    · constructor
      · intro x y heq
        exact decimalIntervalRealToEventFlow_injective heq
      · rfl

end BEDC.Derived.DecimalIntervalRealUp
