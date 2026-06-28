import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CofinalStreamTailSelectorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
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

theorem CofinalStreamTailSelectorObligationSurface (x : CofinalStreamTailSelectorUp) :
    ∃ precision window regseqHandoff dyadicReadback realSeal selectorProvenance
        hsameTransport contReplay pkgProvenance localName : BHist,
      x =
          CofinalStreamTailSelectorUp.mk precision window regseqHandoff dyadicReadback
            realSeal selectorProvenance hsameTransport contReplay pkgProvenance
            localName ∧
        BHistCarrier.toEventFlow x = cofinalStreamTailSelectorToEventFlow x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk precision window regseqHandoff dyadicReadback realSeal selectorProvenance
      hsameTransport contReplay pkgProvenance localName =>
      refine
        ⟨precision, window, regseqHandoff, dyadicReadback, realSeal,
          selectorProvenance, hsameTransport, contReplay, pkgProvenance,
          localName, ?_⟩
      constructor
      · rfl
      · rfl

theorem CofinalStreamTailSelectorSealOrder (x : CofinalStreamTailSelectorUp) :
    ∃ precision window regseqHandoff dyadicReadback realSeal selectorProvenance
        hsameTransport contReplay pkgProvenance localName : BHist,
      x =
          CofinalStreamTailSelectorUp.mk precision window regseqHandoff dyadicReadback
            realSeal selectorProvenance hsameTransport contReplay pkgProvenance
            localName ∧
        cofinalStreamTailSelectorToEventFlow x =
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
            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
              BMark.b0],
            cofinalStreamTailSelectorEncodeBHist hsameTransport,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
              BMark.b1, BMark.b0],
            cofinalStreamTailSelectorEncodeBHist contReplay,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
              BMark.b1, BMark.b1, BMark.b0],
            cofinalStreamTailSelectorEncodeBHist pkgProvenance,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
              BMark.b1, BMark.b1, BMark.b1, BMark.b0],
            cofinalStreamTailSelectorEncodeBHist localName] := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk precision window regseqHandoff dyadicReadback realSeal selectorProvenance
      hsameTransport contReplay pkgProvenance localName =>
      refine
        ⟨precision, window, regseqHandoff, dyadicReadback, realSeal,
          selectorProvenance, hsameTransport, contReplay, pkgProvenance,
          localName, ?_⟩
      constructor
      · rfl
      · rfl

def CofinalStreamTailSelectorCarrier [AskSetup] [PackageSetup]
    (epsilon W R D A sigma H C P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory epsilon ∧
    UnaryHistory W ∧
      UnaryHistory R ∧
        UnaryHistory D ∧
          UnaryHistory A ∧
            UnaryHistory sigma ∧
              UnaryHistory H ∧
                UnaryHistory C ∧
                  UnaryHistory P ∧ UnaryHistory N ∧ PkgSig bundle P pkg

theorem CofinalStreamTailSelectorPublicCertificate [AskSetup] [PackageSetup]
    {epsilon W R D A sigma H C P N sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CofinalStreamTailSelectorCarrier epsilon W R D A sigma H C P N bundle pkg →
      Cont W R sealRead →
        PkgSig bundle P pkg →
          SemanticNameCert
              (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row epsilon ∨ hsame row W ∨ hsame row R ∨ hsame row D ∨
                  hsame row A ∨ hsame row sigma ∨ hsame row H ∨ hsame row C ∨
                    hsame row P ∨ hsame row N ∨ hsame row sealRead)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle P pkg ∧ Cont W R sealRead)
              hsame ∧
            UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert
  intro carrier windowRegularRoute packageProof
  obtain ⟨_epsilonUnary, windowUnary, regularUnary, _dyadicUnary, _approxUnary,
    _selectorUnary, _handoffUnary, _contReplayUnary, _pkgUnary, _localUnary,
    _carrierPkg⟩ := carrier
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed windowUnary regularUnary windowRegularRoute
  refine ⟨?_, sealUnary⟩
  refine
    { core :=
        { carrier_inhabited := ⟨sealRead, hsame_refl sealRead, sealUnary⟩
          equiv_refl := ?_
          equiv_symm := ?_
          equiv_trans := ?_
          carrier_respects_equiv := ?_ }
      pattern_sound := ?_
      ledger_sound := ?_ }
  · intro row _source
    exact hsame_refl row
  · intro _row _other sameRows
    exact hsame_symm sameRows
  · intro _row _middle _other sameLeft sameRight
    exact hsame_trans sameLeft sameRight
  · intro _row _other sameRows sourceRow
    exact
      ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
        unary_transport sourceRow.right sameRows⟩
  · intro _row sourceRow
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr sourceRow.left)))))))))
  · intro _row sourceRow
    exact ⟨sourceRow.right, packageProof, windowRegularRoute⟩

end BEDC.Derived.CofinalStreamTailSelectorUp
