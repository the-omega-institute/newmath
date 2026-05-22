import BEDC.Derived.CauchyTailDiameterUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyTailDiameterUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def cauchyTailDiameterEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyTailDiameterEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyTailDiameterEncodeBHist h

def cauchyTailDiameterDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyTailDiameterDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyTailDiameterDecodeBHist tail)

private theorem cauchyTailDiameter_decode_encode_bhist :
    ∀ h : BHist, cauchyTailDiameterDecodeBHist (cauchyTailDiameterEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem cauchyTailDiameter_mk_congr
    {source source' threshold threshold' leftIndex leftIndex' rightIndex rightIndex'
      tolerance tolerance' bound bound' window window' transport transport' replay replay'
      provenance provenance' localName localName' : BHist}
    (hSource : source' = source)
    (hThreshold : threshold' = threshold)
    (hLeftIndex : leftIndex' = leftIndex)
    (hRightIndex : rightIndex' = rightIndex)
    (hTolerance : tolerance' = tolerance)
    (hBound : bound' = bound)
    (hWindow : window' = window)
    (hTransport : transport' = transport)
    (hReplay : replay' = replay)
    (hProvenance : provenance' = provenance)
    (hLocalName : localName' = localName) :
    BEDC.Derived.CauchyTailDiameterUp.mk source' threshold' leftIndex' rightIndex' tolerance' bound' window'
        transport' replay' provenance' localName' =
      BEDC.Derived.CauchyTailDiameterUp.mk source threshold leftIndex rightIndex tolerance bound window
        transport replay provenance localName := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hSource
  cases hThreshold
  cases hLeftIndex
  cases hRightIndex
  cases hTolerance
  cases hBound
  cases hWindow
  cases hTransport
  cases hReplay
  cases hProvenance
  cases hLocalName
  rfl

def cauchyTailDiameterFields : BEDC.Derived.CauchyTailDiameterUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BEDC.Derived.CauchyTailDiameterUp.mk source threshold leftIndex rightIndex tolerance bound window
      transport replay provenance localName =>
      [source, threshold, leftIndex, rightIndex, tolerance, bound, window, transport, replay,
        provenance, localName]

def cauchyTailDiameterToEventFlow : BEDC.Derived.CauchyTailDiameterUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BEDC.Derived.CauchyTailDiameterUp.mk source threshold leftIndex rightIndex tolerance bound window
      transport replay provenance localName =>
      [cauchyTailDiameterEncodeBHist source,
        cauchyTailDiameterEncodeBHist threshold,
        cauchyTailDiameterEncodeBHist leftIndex,
        cauchyTailDiameterEncodeBHist rightIndex,
        cauchyTailDiameterEncodeBHist tolerance,
        cauchyTailDiameterEncodeBHist bound,
        cauchyTailDiameterEncodeBHist window,
        cauchyTailDiameterEncodeBHist transport,
        cauchyTailDiameterEncodeBHist replay,
        cauchyTailDiameterEncodeBHist provenance,
        cauchyTailDiameterEncodeBHist localName]

def cauchyTailDiameterFromEventFlow : EventFlow → Option BEDC.Derived.CauchyTailDiameterUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | source :: rest0 =>
      match rest0 with
      | [] => none
      | threshold :: rest1 =>
          match rest1 with
          | [] => none
          | leftIndex :: rest2 =>
              match rest2 with
              | [] => none
              | rightIndex :: rest3 =>
                  match rest3 with
                  | [] => none
                  | tolerance :: rest4 =>
                      match rest4 with
                      | [] => none
                      | bound :: rest5 =>
                          match rest5 with
                          | [] => none
                          | window :: rest6 =>
                              match rest6 with
                              | [] => none
                              | transport :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | replay :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | provenance :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | localName :: rest10 =>
                                              match rest10 with
                                              | [] =>
                                                  some
                                                    (BEDC.Derived.CauchyTailDiameterUp.mk
                                                      (cauchyTailDiameterDecodeBHist source)
                                                      (cauchyTailDiameterDecodeBHist threshold)
                                                      (cauchyTailDiameterDecodeBHist leftIndex)
                                                      (cauchyTailDiameterDecodeBHist rightIndex)
                                                      (cauchyTailDiameterDecodeBHist tolerance)
                                                      (cauchyTailDiameterDecodeBHist bound)
                                                      (cauchyTailDiameterDecodeBHist window)
                                                      (cauchyTailDiameterDecodeBHist transport)
                                                      (cauchyTailDiameterDecodeBHist replay)
                                                      (cauchyTailDiameterDecodeBHist provenance)
                                                      (cauchyTailDiameterDecodeBHist localName))
                                              | _ :: _ => none

private theorem cauchyTailDiameter_round_trip :
    ∀ x : BEDC.Derived.CauchyTailDiameterUp,
      cauchyTailDiameterFromEventFlow (cauchyTailDiameterToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source threshold leftIndex rightIndex tolerance bound window transport replay provenance
      localName =>
      change
        some
          (BEDC.Derived.CauchyTailDiameterUp.mk
            (cauchyTailDiameterDecodeBHist (cauchyTailDiameterEncodeBHist source))
            (cauchyTailDiameterDecodeBHist (cauchyTailDiameterEncodeBHist threshold))
            (cauchyTailDiameterDecodeBHist (cauchyTailDiameterEncodeBHist leftIndex))
            (cauchyTailDiameterDecodeBHist (cauchyTailDiameterEncodeBHist rightIndex))
            (cauchyTailDiameterDecodeBHist (cauchyTailDiameterEncodeBHist tolerance))
            (cauchyTailDiameterDecodeBHist (cauchyTailDiameterEncodeBHist bound))
            (cauchyTailDiameterDecodeBHist (cauchyTailDiameterEncodeBHist window))
            (cauchyTailDiameterDecodeBHist (cauchyTailDiameterEncodeBHist transport))
            (cauchyTailDiameterDecodeBHist (cauchyTailDiameterEncodeBHist replay))
            (cauchyTailDiameterDecodeBHist (cauchyTailDiameterEncodeBHist provenance))
            (cauchyTailDiameterDecodeBHist (cauchyTailDiameterEncodeBHist localName))) =
          some
            (BEDC.Derived.CauchyTailDiameterUp.mk source threshold leftIndex rightIndex tolerance bound
              window transport replay provenance localName)
      exact
        congrArg some
          (cauchyTailDiameter_mk_congr
            (cauchyTailDiameter_decode_encode_bhist source)
            (cauchyTailDiameter_decode_encode_bhist threshold)
            (cauchyTailDiameter_decode_encode_bhist leftIndex)
            (cauchyTailDiameter_decode_encode_bhist rightIndex)
            (cauchyTailDiameter_decode_encode_bhist tolerance)
            (cauchyTailDiameter_decode_encode_bhist bound)
            (cauchyTailDiameter_decode_encode_bhist window)
            (cauchyTailDiameter_decode_encode_bhist transport)
            (cauchyTailDiameter_decode_encode_bhist replay)
            (cauchyTailDiameter_decode_encode_bhist provenance)
            (cauchyTailDiameter_decode_encode_bhist localName))

private theorem cauchyTailDiameterToEventFlow_injective
    {x y : CauchyTailDiameterUp} :
    cauchyTailDiameterToEventFlow x = cauchyTailDiameterToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyTailDiameterFromEventFlow (cauchyTailDiameterToEventFlow x) =
        cauchyTailDiameterFromEventFlow (cauchyTailDiameterToEventFlow y) :=
    congrArg cauchyTailDiameterFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyTailDiameter_round_trip x).symm
      (Eq.trans hread (cauchyTailDiameter_round_trip y)))

private theorem cauchyTailDiameter_field_faithful :
    ∀ x y : BEDC.Derived.CauchyTailDiameterUp, cauchyTailDiameterFields x = cauchyTailDiameterFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk source₁ threshold₁ leftIndex₁ rightIndex₁ tolerance₁ bound₁ window₁ transport₁ replay₁
      provenance₁ localName₁ =>
      cases y with
      | mk source₂ threshold₂ leftIndex₂ rightIndex₂ tolerance₂ bound₂ window₂ transport₂
          replay₂ provenance₂ localName₂ =>
          injection h with hSource t1
          injection t1 with hThreshold t2
          injection t2 with hLeftIndex t3
          injection t3 with hRightIndex t4
          injection t4 with hTolerance t5
          injection t5 with hBound t6
          injection t6 with hWindow t7
          injection t7 with hTransport t8
          injection t8 with hReplay t9
          injection t9 with hProvenance t10
          injection t10 with hLocalName _
          subst hSource
          subst hThreshold
          subst hLeftIndex
          subst hRightIndex
          subst hTolerance
          subst hBound
          subst hWindow
          subst hTransport
          subst hReplay
          subst hProvenance
          subst hLocalName
          rfl

instance cauchyTailDiameterBHistCarrier : BHistCarrier BEDC.Derived.CauchyTailDiameterUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyTailDiameterToEventFlow
  fromEventFlow := cauchyTailDiameterFromEventFlow

instance cauchyTailDiameterChapterTasteGate : ChapterTasteGate BEDC.Derived.CauchyTailDiameterUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyTailDiameterFromEventFlow (cauchyTailDiameterToEventFlow x) = some x
    exact cauchyTailDiameter_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyTailDiameterToEventFlow_injective heq)

instance cauchyTailDiameterFieldFaithful : FieldFaithful BEDC.Derived.CauchyTailDiameterUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyTailDiameterFields
  field_faithful := cauchyTailDiameter_field_faithful

instance cauchyTailDiameterNontrivial : Nontrivial BEDC.Derived.CauchyTailDiameterUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BEDC.Derived.CauchyTailDiameterUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BEDC.Derived.CauchyTailDiameterUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BEDC.Derived.CauchyTailDiameterUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyTailDiameterChapterTasteGate

theorem CauchyTailDiameterUpTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchyTailDiameterDecodeBHist (cauchyTailDiameterEncodeBHist h) = h) ∧
      (∀ x : BEDC.Derived.CauchyTailDiameterUp,
        cauchyTailDiameterFromEventFlow (cauchyTailDiameterToEventFlow x) = some x) ∧
        (∀ x y : BEDC.Derived.CauchyTailDiameterUp,
          cauchyTailDiameterToEventFlow x = cauchyTailDiameterToEventFlow y → x = y) ∧
          cauchyTailDiameterEncodeBHist BHist.Empty = ([] : List BMark) :=
  -- BEDC touchpoint anchor: BHist BMark
  ⟨cauchyTailDiameter_decode_encode_bhist,
    ⟨cauchyTailDiameter_round_trip,
      ⟨fun _x _y heq => cauchyTailDiameterToEventFlow_injective heq, rfl⟩⟩⟩

end BEDC.Derived.CauchyTailDiameterUp
