import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.QuotientStreamRefusalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive QuotientStreamRefusalUp : Type where
  | mk (stream regular cauchySeal realSeal refusal transport route provenance name : BHist) :
      QuotientStreamRefusalUp
  deriving DecidableEq

def quotientStreamRefusalEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: quotientStreamRefusalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: quotientStreamRefusalEncodeBHist h

def quotientStreamRefusalDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (quotientStreamRefusalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (quotientStreamRefusalDecodeBHist tail)

private theorem quotientStreamRefusalDecode_encode_bhist :
    ∀ h : BHist, quotientStreamRefusalDecodeBHist (quotientStreamRefusalEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def quotientStreamRefusalToEventFlow : QuotientStreamRefusalUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | QuotientStreamRefusalUp.mk stream regular cauchySeal realSeal refusal transport route
      provenance name =>
      [[BMark.b0],
        quotientStreamRefusalEncodeBHist stream,
        [BMark.b1, BMark.b0],
        quotientStreamRefusalEncodeBHist regular,
        [BMark.b1, BMark.b1, BMark.b0],
        quotientStreamRefusalEncodeBHist cauchySeal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        quotientStreamRefusalEncodeBHist realSeal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        quotientStreamRefusalEncodeBHist refusal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        quotientStreamRefusalEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        quotientStreamRefusalEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        quotientStreamRefusalEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        quotientStreamRefusalEncodeBHist name]

private def quotientStreamRefusalDecodePacket
    (stream regular cauchySeal realSeal refusal transport route provenance name : RawEvent) :
    QuotientStreamRefusalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  QuotientStreamRefusalUp.mk
    (quotientStreamRefusalDecodeBHist stream)
    (quotientStreamRefusalDecodeBHist regular)
    (quotientStreamRefusalDecodeBHist cauchySeal)
    (quotientStreamRefusalDecodeBHist realSeal)
    (quotientStreamRefusalDecodeBHist refusal)
    (quotientStreamRefusalDecodeBHist transport)
    (quotientStreamRefusalDecodeBHist route)
    (quotientStreamRefusalDecodeBHist provenance)
    (quotientStreamRefusalDecodeBHist name)

def quotientStreamRefusalFromEventFlow : EventFlow → Option QuotientStreamRefusalUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | stream :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | regular :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | cauchySeal :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | realSeal :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | refusal :: rest9 =>
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
                                                                      | name :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (quotientStreamRefusalDecodePacket
                                                                                  stream regular
                                                                                  cauchySeal
                                                                                  realSeal
                                                                                  refusal transport
                                                                                  route
                                                                                  provenance name)
                                                                          | _ :: _ => none

private theorem quotientStreamRefusal_round_trip :
    ∀ x : QuotientStreamRefusalUp,
      quotientStreamRefusalFromEventFlow (quotientStreamRefusalToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk stream regular cauchySeal realSeal refusal transport route provenance name =>
      change
        some
            (quotientStreamRefusalDecodePacket
              (quotientStreamRefusalEncodeBHist stream)
              (quotientStreamRefusalEncodeBHist regular)
              (quotientStreamRefusalEncodeBHist cauchySeal)
              (quotientStreamRefusalEncodeBHist realSeal)
              (quotientStreamRefusalEncodeBHist refusal)
              (quotientStreamRefusalEncodeBHist transport)
              (quotientStreamRefusalEncodeBHist route)
              (quotientStreamRefusalEncodeBHist provenance)
              (quotientStreamRefusalEncodeBHist name)) =
          some
            (QuotientStreamRefusalUp.mk stream regular cauchySeal realSeal refusal transport route
              provenance name)
      unfold quotientStreamRefusalDecodePacket
      rw [quotientStreamRefusalDecode_encode_bhist stream,
        quotientStreamRefusalDecode_encode_bhist regular,
        quotientStreamRefusalDecode_encode_bhist cauchySeal,
        quotientStreamRefusalDecode_encode_bhist realSeal,
        quotientStreamRefusalDecode_encode_bhist refusal,
        quotientStreamRefusalDecode_encode_bhist transport,
        quotientStreamRefusalDecode_encode_bhist route,
        quotientStreamRefusalDecode_encode_bhist provenance,
        quotientStreamRefusalDecode_encode_bhist name]

private theorem quotientStreamRefusalToEventFlow_injective {x y : QuotientStreamRefusalUp} :
    quotientStreamRefusalToEventFlow x = quotientStreamRefusalToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      quotientStreamRefusalFromEventFlow (quotientStreamRefusalToEventFlow x) =
        quotientStreamRefusalFromEventFlow (quotientStreamRefusalToEventFlow y) :=
    congrArg quotientStreamRefusalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (quotientStreamRefusal_round_trip x).symm
      (Eq.trans hread (quotientStreamRefusal_round_trip y)))

instance quotientStreamRefusalBHistCarrier : BHistCarrier QuotientStreamRefusalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := quotientStreamRefusalToEventFlow
  fromEventFlow := quotientStreamRefusalFromEventFlow

instance quotientStreamRefusalChapterTasteGate : ChapterTasteGate QuotientStreamRefusalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change quotientStreamRefusalFromEventFlow (quotientStreamRefusalToEventFlow x) = some x
    exact quotientStreamRefusal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (quotientStreamRefusalToEventFlow_injective heq)

instance quotientStreamRefusalFieldFaithful : FieldFaithful QuotientStreamRefusalUp where
  fields := fun x =>
    match x with
    | QuotientStreamRefusalUp.mk stream regular cauchySeal realSeal refusal transport route
        provenance name =>
        [stream, regular, cauchySeal, realSeal, refusal, transport, route, provenance, name]
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y h
    cases x with
    | mk stream₁ regular₁ cauchySeal₁ realSeal₁ refusal₁ transport₁ route₁ provenance₁ name₁ =>
        cases y with
        | mk stream₂ regular₂ cauchySeal₂ realSeal₂ refusal₂ transport₂ route₂ provenance₂ name₂ =>
            injection h with hStream hTail₁
            injection hTail₁ with hRegular hTail₂
            injection hTail₂ with hCauchySeal hTail₃
            injection hTail₃ with hRealSeal hTail₄
            injection hTail₄ with hRefusal hTail₅
            injection hTail₅ with hTransport hTail₆
            injection hTail₆ with hRoute hTail₇
            injection hTail₇ with hProvenance hTail₈
            injection hTail₈ with hName _
            subst hStream
            subst hRegular
            subst hCauchySeal
            subst hRealSeal
            subst hRefusal
            subst hTransport
            subst hRoute
            subst hProvenance
            subst hName
            rfl

instance quotientStreamRefusalNontrivial : Nontrivial QuotientStreamRefusalUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨QuotientStreamRefusalUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      QuotientStreamRefusalUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate QuotientStreamRefusalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  quotientStreamRefusalChapterTasteGate

theorem QuotientStreamRefusalTasteGate_single_carrier_alignment :
    (∀ h : BHist, quotientStreamRefusalDecodeBHist (quotientStreamRefusalEncodeBHist h) = h) ∧
      (∀ x : QuotientStreamRefusalUp,
        quotientStreamRefusalFromEventFlow (quotientStreamRefusalToEventFlow x) = some x) ∧
        (∀ x y : QuotientStreamRefusalUp,
          quotientStreamRefusalToEventFlow x = quotientStreamRefusalToEventFlow y → x = y) ∧
          quotientStreamRefusalEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact quotientStreamRefusalDecode_encode_bhist
  · constructor
    · exact quotientStreamRefusal_round_trip
    · constructor
      · intro x y heq
        exact quotientStreamRefusalToEventFlow_injective heq
      · rfl

def QuotientStreamRefusalPacket [AskSetup] [PackageSetup]
    (s r l e f h c p n : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory ProbeBundle
  UnaryHistory s ∧ UnaryHistory r ∧ UnaryHistory l ∧ UnaryHistory e ∧ UnaryHistory f ∧
    UnaryHistory h ∧ UnaryHistory c ∧ UnaryHistory p ∧ UnaryHistory n ∧
      Cont s r l ∧ Cont l e h ∧ Cont h f c ∧ Cont c n p ∧ PkgSig bundle p pkg

theorem QuotientStreamRefusalPacket_route_ordering [AskSetup] [PackageSetup]
    {s r l e f h c p n sealRow refusalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    QuotientStreamRefusalPacket s r l e f h c p n bundle pkg →
      Cont l e sealRow →
        Cont sealRow f refusalRead →
          PkgSig bundle refusalRead pkg →
            UnaryHistory s ∧ UnaryHistory r ∧ UnaryHistory l ∧ UnaryHistory e ∧
              UnaryHistory sealRow ∧ UnaryHistory refusalRead ∧ Cont s r l ∧
                Cont l e sealRow ∧ Cont sealRow f refusalRead ∧
                  PkgSig bundle p pkg ∧ PkgSig bundle refusalRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory ProbeBundle
  intro packet sealRoute refusalRoute refusalPkg
  obtain ⟨sUnary, rUnary, lUnary, eUnary, fUnary, _hUnary, _cUnary, _pUnary,
    _nUnary, sourceRoute, _sealRoute, _refusalRoute, _packageRoute, packagePkg⟩ :=
    packet
  have sealUnary : UnaryHistory sealRow := unary_cont_closed lUnary eUnary sealRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed sealUnary fUnary refusalRoute
  exact
    ⟨sUnary, rUnary, lUnary, eUnary, sealUnary, refusalUnary, sourceRoute, sealRoute,
      refusalRoute, packagePkg, refusalPkg⟩

end BEDC.Derived.QuotientStreamRefusalUp
