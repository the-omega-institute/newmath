import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CofinalStreamTailSelectorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CofinalStreamTailSelectorUp : Type where
  | mk :
      (precision window regseqHandoff dyadicReadback realSeal selectorProvenance
        hsameTransport contReplay pkgProvenance localName : BHist) →
      CofinalStreamTailSelectorUp

def cofinalStreamTailSelectorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cofinalStreamTailSelectorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cofinalStreamTailSelectorEncodeBHist h

def cofinalStreamTailSelectorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cofinalStreamTailSelectorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cofinalStreamTailSelectorDecodeBHist tail)

private theorem cofinalStreamTailSelector_decode_encode_bhist :
    ∀ h : BHist,
      cofinalStreamTailSelectorDecodeBHist
          (cofinalStreamTailSelectorEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cofinalStreamTailSelectorToEventFlow :
    CofinalStreamTailSelectorUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CofinalStreamTailSelectorUp.mk precision window regseqHandoff dyadicReadback realSeal
      selectorProvenance hsameTransport contReplay pkgProvenance localName =>
      [[BMark.b0],
        cofinalStreamTailSelectorEncodeBHist precision,
        [BMark.b1, BMark.b0],
        cofinalStreamTailSelectorEncodeBHist window,
        [BMark.b1, BMark.b1, BMark.b0],
        cofinalStreamTailSelectorEncodeBHist regseqHandoff,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cofinalStreamTailSelectorEncodeBHist dyadicReadback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cofinalStreamTailSelectorEncodeBHist realSeal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cofinalStreamTailSelectorEncodeBHist selectorProvenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cofinalStreamTailSelectorEncodeBHist hsameTransport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        cofinalStreamTailSelectorEncodeBHist contReplay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        cofinalStreamTailSelectorEncodeBHist pkgProvenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        cofinalStreamTailSelectorEncodeBHist localName]

private def cofinalStreamTailSelectorEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      cofinalStreamTailSelectorEventAtDefault index rest

def cofinalStreamTailSelectorFromEventFlow
    (ef : EventFlow) : Option CofinalStreamTailSelectorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CofinalStreamTailSelectorUp.mk
      (cofinalStreamTailSelectorDecodeBHist
        (cofinalStreamTailSelectorEventAtDefault 1 ef))
      (cofinalStreamTailSelectorDecodeBHist
        (cofinalStreamTailSelectorEventAtDefault 3 ef))
      (cofinalStreamTailSelectorDecodeBHist
        (cofinalStreamTailSelectorEventAtDefault 5 ef))
      (cofinalStreamTailSelectorDecodeBHist
        (cofinalStreamTailSelectorEventAtDefault 7 ef))
      (cofinalStreamTailSelectorDecodeBHist
        (cofinalStreamTailSelectorEventAtDefault 9 ef))
      (cofinalStreamTailSelectorDecodeBHist
        (cofinalStreamTailSelectorEventAtDefault 11 ef))
      (cofinalStreamTailSelectorDecodeBHist
        (cofinalStreamTailSelectorEventAtDefault 13 ef))
      (cofinalStreamTailSelectorDecodeBHist
        (cofinalStreamTailSelectorEventAtDefault 15 ef))
      (cofinalStreamTailSelectorDecodeBHist
        (cofinalStreamTailSelectorEventAtDefault 17 ef))
      (cofinalStreamTailSelectorDecodeBHist
        (cofinalStreamTailSelectorEventAtDefault 19 ef)))

private theorem cofinalStreamTailSelector_round_trip :
    ∀ x : CofinalStreamTailSelectorUp,
      cofinalStreamTailSelectorFromEventFlow
          (cofinalStreamTailSelectorToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk precision window regseqHandoff dyadicReadback realSeal selectorProvenance
      hsameTransport contReplay pkgProvenance localName =>
      change
        some
            (CofinalStreamTailSelectorUp.mk
              (cofinalStreamTailSelectorDecodeBHist
                (cofinalStreamTailSelectorEncodeBHist precision))
              (cofinalStreamTailSelectorDecodeBHist
                (cofinalStreamTailSelectorEncodeBHist window))
              (cofinalStreamTailSelectorDecodeBHist
                (cofinalStreamTailSelectorEncodeBHist regseqHandoff))
              (cofinalStreamTailSelectorDecodeBHist
                (cofinalStreamTailSelectorEncodeBHist dyadicReadback))
              (cofinalStreamTailSelectorDecodeBHist
                (cofinalStreamTailSelectorEncodeBHist realSeal))
              (cofinalStreamTailSelectorDecodeBHist
                (cofinalStreamTailSelectorEncodeBHist selectorProvenance))
              (cofinalStreamTailSelectorDecodeBHist
                (cofinalStreamTailSelectorEncodeBHist hsameTransport))
              (cofinalStreamTailSelectorDecodeBHist
                (cofinalStreamTailSelectorEncodeBHist contReplay))
              (cofinalStreamTailSelectorDecodeBHist
                (cofinalStreamTailSelectorEncodeBHist pkgProvenance))
              (cofinalStreamTailSelectorDecodeBHist
                (cofinalStreamTailSelectorEncodeBHist localName))) =
          some
            (CofinalStreamTailSelectorUp.mk precision window regseqHandoff dyadicReadback
              realSeal selectorProvenance hsameTransport contReplay pkgProvenance
              localName)
      rw [cofinalStreamTailSelector_decode_encode_bhist precision]
      rw [cofinalStreamTailSelector_decode_encode_bhist window]
      rw [cofinalStreamTailSelector_decode_encode_bhist regseqHandoff]
      rw [cofinalStreamTailSelector_decode_encode_bhist dyadicReadback]
      rw [cofinalStreamTailSelector_decode_encode_bhist realSeal]
      rw [cofinalStreamTailSelector_decode_encode_bhist selectorProvenance]
      rw [cofinalStreamTailSelector_decode_encode_bhist hsameTransport]
      rw [cofinalStreamTailSelector_decode_encode_bhist contReplay]
      rw [cofinalStreamTailSelector_decode_encode_bhist pkgProvenance]
      rw [cofinalStreamTailSelector_decode_encode_bhist localName]

theorem cofinalStreamTailSelectorToEventFlow_injective
    {x y : CofinalStreamTailSelectorUp} :
    cofinalStreamTailSelectorToEventFlow x =
      cofinalStreamTailSelectorToEventFlow y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  cases x with
  | mk precision₁ window₁ regseqHandoff₁ dyadicReadback₁ realSeal₁ selectorProvenance₁
      hsameTransport₁ contReplay₁ pkgProvenance₁ localName₁ =>
      cases y with
      | mk precision₂ window₂ regseqHandoff₂ dyadicReadback₂ realSeal₂ selectorProvenance₂
          hsameTransport₂ contReplay₂ pkgProvenance₂ localName₂ =>
          injection heq with _ htail₀
          injection htail₀ with hPrecision htail₁
          injection htail₁ with _ htail₂
          injection htail₂ with hWindow htail₃
          injection htail₃ with _ htail₄
          injection htail₄ with hRegseqHandoff htail₅
          injection htail₅ with _ htail₆
          injection htail₆ with hDyadicReadback htail₇
          injection htail₇ with _ htail₈
          injection htail₈ with hRealSeal htail₉
          injection htail₉ with _ htail₁₀
          injection htail₁₀ with hSelectorProvenance htail₁₁
          injection htail₁₁ with _ htail₁₂
          injection htail₁₂ with hHsameTransport htail₁₃
          injection htail₁₃ with _ htail₁₄
          injection htail₁₄ with hContReplay htail₁₅
          injection htail₁₅ with _ htail₁₆
          injection htail₁₆ with hPkgProvenance htail₁₇
          injection htail₁₇ with _ htail₁₈
          injection htail₁₈ with hLocalName _
          have hPrecision' : precision₁ = precision₂ := by
            have decoded := congrArg cofinalStreamTailSelectorDecodeBHist hPrecision
            exact Eq.trans (cofinalStreamTailSelector_decode_encode_bhist precision₁).symm
              (Eq.trans decoded (cofinalStreamTailSelector_decode_encode_bhist precision₂))
          cases hPrecision'
          have hWindow' : window₁ = window₂ := by
            have decoded := congrArg cofinalStreamTailSelectorDecodeBHist hWindow
            exact Eq.trans (cofinalStreamTailSelector_decode_encode_bhist window₁).symm
              (Eq.trans decoded (cofinalStreamTailSelector_decode_encode_bhist window₂))
          cases hWindow'
          have hRegseqHandoff' : regseqHandoff₁ = regseqHandoff₂ := by
            have decoded := congrArg cofinalStreamTailSelectorDecodeBHist hRegseqHandoff
            exact Eq.trans (cofinalStreamTailSelector_decode_encode_bhist regseqHandoff₁).symm
              (Eq.trans decoded
                (cofinalStreamTailSelector_decode_encode_bhist regseqHandoff₂))
          cases hRegseqHandoff'
          have hDyadicReadback' : dyadicReadback₁ = dyadicReadback₂ := by
            have decoded := congrArg cofinalStreamTailSelectorDecodeBHist hDyadicReadback
            exact Eq.trans (cofinalStreamTailSelector_decode_encode_bhist dyadicReadback₁).symm
              (Eq.trans decoded
                (cofinalStreamTailSelector_decode_encode_bhist dyadicReadback₂))
          cases hDyadicReadback'
          have hRealSeal' : realSeal₁ = realSeal₂ := by
            have decoded := congrArg cofinalStreamTailSelectorDecodeBHist hRealSeal
            exact Eq.trans (cofinalStreamTailSelector_decode_encode_bhist realSeal₁).symm
              (Eq.trans decoded (cofinalStreamTailSelector_decode_encode_bhist realSeal₂))
          cases hRealSeal'
          have hSelectorProvenance' : selectorProvenance₁ = selectorProvenance₂ := by
            have decoded := congrArg cofinalStreamTailSelectorDecodeBHist hSelectorProvenance
            exact Eq.trans
              (cofinalStreamTailSelector_decode_encode_bhist selectorProvenance₁).symm
              (Eq.trans decoded
                (cofinalStreamTailSelector_decode_encode_bhist selectorProvenance₂))
          cases hSelectorProvenance'
          have hHsameTransport' : hsameTransport₁ = hsameTransport₂ := by
            have decoded := congrArg cofinalStreamTailSelectorDecodeBHist hHsameTransport
            exact Eq.trans
              (cofinalStreamTailSelector_decode_encode_bhist hsameTransport₁).symm
              (Eq.trans decoded
                (cofinalStreamTailSelector_decode_encode_bhist hsameTransport₂))
          cases hHsameTransport'
          have hContReplay' : contReplay₁ = contReplay₂ := by
            have decoded := congrArg cofinalStreamTailSelectorDecodeBHist hContReplay
            exact Eq.trans (cofinalStreamTailSelector_decode_encode_bhist contReplay₁).symm
              (Eq.trans decoded (cofinalStreamTailSelector_decode_encode_bhist contReplay₂))
          cases hContReplay'
          have hPkgProvenance' : pkgProvenance₁ = pkgProvenance₂ := by
            have decoded := congrArg cofinalStreamTailSelectorDecodeBHist hPkgProvenance
            exact Eq.trans (cofinalStreamTailSelector_decode_encode_bhist pkgProvenance₁).symm
              (Eq.trans decoded
                (cofinalStreamTailSelector_decode_encode_bhist pkgProvenance₂))
          cases hPkgProvenance'
          have hLocalName' : localName₁ = localName₂ := by
            have decoded := congrArg cofinalStreamTailSelectorDecodeBHist hLocalName
            exact Eq.trans (cofinalStreamTailSelector_decode_encode_bhist localName₁).symm
              (Eq.trans decoded (cofinalStreamTailSelector_decode_encode_bhist localName₂))
          cases hLocalName'
          rfl

instance cofinalStreamTailSelectorBHistCarrier :
    BHistCarrier CofinalStreamTailSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cofinalStreamTailSelectorToEventFlow
  fromEventFlow := cofinalStreamTailSelectorFromEventFlow

instance cofinalStreamTailSelectorChapterTasteGate :
    ChapterTasteGate CofinalStreamTailSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cofinalStreamTailSelectorFromEventFlow
          (cofinalStreamTailSelectorToEventFlow x) =
        some x
    exact cofinalStreamTailSelector_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cofinalStreamTailSelectorToEventFlow_injective heq)

instance cofinalStreamTailSelectorFieldFaithful :
    FieldFaithful CofinalStreamTailSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | CofinalStreamTailSelectorUp.mk precision window regseqHandoff dyadicReadback realSeal
        selectorProvenance hsameTransport contReplay pkgProvenance localName =>
        [precision, window, regseqHandoff, dyadicReadback, realSeal, selectorProvenance,
          hsameTransport, contReplay, pkgProvenance, localName]
  field_faithful := by
    intro x y h
    cases x with
    | mk precision₁ window₁ regseqHandoff₁ dyadicReadback₁ realSeal₁
        selectorProvenance₁ hsameTransport₁ contReplay₁ pkgProvenance₁ localName₁ =>
        cases y with
        | mk precision₂ window₂ regseqHandoff₂ dyadicReadback₂ realSeal₂
            selectorProvenance₂ hsameTransport₂ contReplay₂ pkgProvenance₂ localName₂ =>
            cases h
            rfl

instance cofinalStreamTailSelectorNontrivial :
    Nontrivial CofinalStreamTailSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair := by
    refine
      ⟨CofinalStreamTailSelectorUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
        CofinalStreamTailSelectorUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty, ?_⟩
    intro h
    cases h

def taste_gate : ChapterTasteGate CofinalStreamTailSelectorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cofinalStreamTailSelectorChapterTasteGate

theorem CofinalStreamTailSelectorTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cofinalStreamTailSelectorDecodeBHist (cofinalStreamTailSelectorEncodeBHist h) = h) ∧
      (∀ x : CofinalStreamTailSelectorUp,
        cofinalStreamTailSelectorFromEventFlow (cofinalStreamTailSelectorToEventFlow x) =
          some x) ∧
      (∀ x y : CofinalStreamTailSelectorUp,
        cofinalStreamTailSelectorToEventFlow x = cofinalStreamTailSelectorToEventFlow y →
          x = y) ∧
      Nonempty (ChapterTasteGate CofinalStreamTailSelectorUp) ∧
      Nonempty (FieldFaithful CofinalStreamTailSelectorUp) ∧
      Nonempty (Nontrivial CofinalStreamTailSelectorUp) ∧
      cofinalStreamTailSelectorEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact cofinalStreamTailSelector_decode_encode_bhist
  · constructor
    · exact cofinalStreamTailSelector_round_trip
    · constructor
      · intro x y heq
        exact cofinalStreamTailSelectorToEventFlow_injective heq
      · constructor
        · exact ⟨cofinalStreamTailSelectorChapterTasteGate⟩
        · constructor
          · exact ⟨cofinalStreamTailSelectorFieldFaithful⟩
          · constructor
            · exact ⟨cofinalStreamTailSelectorNontrivial⟩
            · rfl

end BEDC.Derived.CofinalStreamTailSelectorUp
