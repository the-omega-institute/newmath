import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BHistOctaSequenceNameCertUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BHistOctaSequenceNameCertUp : Type where
  | mk (a b c d e f g h route provenance nameRow : BHist) :
      BHistOctaSequenceNameCertUp
  deriving DecidableEq

def bHistOctaSequenceNameCertEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bHistOctaSequenceNameCertEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bHistOctaSequenceNameCertEncodeBHist h

def bHistOctaSequenceNameCertDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bHistOctaSequenceNameCertDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bHistOctaSequenceNameCertDecodeBHist tail)

private theorem BHistOctaSequenceNameCert_alignment_decode_encode_bhist :
    forall h : BHist,
      bHistOctaSequenceNameCertDecodeBHist
        (bHistOctaSequenceNameCertEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem BHistOctaSequenceNameCert_alignment_mk_congr
    {a a' b b' c c' d d' e e' f f' g g' h h' route route' provenance provenance'
      nameRow nameRow' : BHist}
    (ha : a' = a)
    (hb : b' = b)
    (hc : c' = c)
    (hd : d' = d)
    (he : e' = e)
    (hf : f' = f)
    (hg : g' = g)
    (hh : h' = h)
    (hroute : route' = route)
    (hprovenance : provenance' = provenance)
    (hnameRow : nameRow' = nameRow) :
    BHistOctaSequenceNameCertUp.mk a' b' c' d' e' f' g' h' route' provenance'
        nameRow' =
      BHistOctaSequenceNameCertUp.mk a b c d e f g h route provenance nameRow := by
  -- BEDC touchpoint anchor: BHist BMark
  cases ha
  cases hb
  cases hc
  cases hd
  cases he
  cases hf
  cases hg
  cases hh
  cases hroute
  cases hprovenance
  cases hnameRow
  rfl

def bHistOctaSequenceNameCertToEventFlow :
    BHistOctaSequenceNameCertUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BHistOctaSequenceNameCertUp.mk a b c d e f g h route provenance nameRow =>
      [bHistOctaSequenceNameCertEncodeBHist a,
        bHistOctaSequenceNameCertEncodeBHist b,
        bHistOctaSequenceNameCertEncodeBHist c,
        bHistOctaSequenceNameCertEncodeBHist d,
        bHistOctaSequenceNameCertEncodeBHist e,
        bHistOctaSequenceNameCertEncodeBHist f,
        bHistOctaSequenceNameCertEncodeBHist g,
        bHistOctaSequenceNameCertEncodeBHist h,
        bHistOctaSequenceNameCertEncodeBHist route,
        bHistOctaSequenceNameCertEncodeBHist provenance,
        bHistOctaSequenceNameCertEncodeBHist nameRow]

def bHistOctaSequenceNameCertFromEventFlow :
    EventFlow -> Option BHistOctaSequenceNameCertUp
  -- BEDC touchpoint anchor: BHist BMark
  | [a, b, c, d, e, f, g, h, route, provenance, nameRow] =>
      some
        (BHistOctaSequenceNameCertUp.mk
          (bHistOctaSequenceNameCertDecodeBHist a)
          (bHistOctaSequenceNameCertDecodeBHist b)
          (bHistOctaSequenceNameCertDecodeBHist c)
          (bHistOctaSequenceNameCertDecodeBHist d)
          (bHistOctaSequenceNameCertDecodeBHist e)
          (bHistOctaSequenceNameCertDecodeBHist f)
          (bHistOctaSequenceNameCertDecodeBHist g)
          (bHistOctaSequenceNameCertDecodeBHist h)
          (bHistOctaSequenceNameCertDecodeBHist route)
          (bHistOctaSequenceNameCertDecodeBHist provenance)
          (bHistOctaSequenceNameCertDecodeBHist nameRow))
  | _ => none

private theorem BHistOctaSequenceNameCert_alignment_round_trip :
    forall x : BHistOctaSequenceNameCertUp,
      bHistOctaSequenceNameCertFromEventFlow
        (bHistOctaSequenceNameCertToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk a b c d e f g h route provenance nameRow =>
      change
        some
          (BHistOctaSequenceNameCertUp.mk
            (bHistOctaSequenceNameCertDecodeBHist
              (bHistOctaSequenceNameCertEncodeBHist a))
            (bHistOctaSequenceNameCertDecodeBHist
              (bHistOctaSequenceNameCertEncodeBHist b))
            (bHistOctaSequenceNameCertDecodeBHist
              (bHistOctaSequenceNameCertEncodeBHist c))
            (bHistOctaSequenceNameCertDecodeBHist
              (bHistOctaSequenceNameCertEncodeBHist d))
            (bHistOctaSequenceNameCertDecodeBHist
              (bHistOctaSequenceNameCertEncodeBHist e))
            (bHistOctaSequenceNameCertDecodeBHist
              (bHistOctaSequenceNameCertEncodeBHist f))
            (bHistOctaSequenceNameCertDecodeBHist
              (bHistOctaSequenceNameCertEncodeBHist g))
            (bHistOctaSequenceNameCertDecodeBHist
              (bHistOctaSequenceNameCertEncodeBHist h))
            (bHistOctaSequenceNameCertDecodeBHist
              (bHistOctaSequenceNameCertEncodeBHist route))
            (bHistOctaSequenceNameCertDecodeBHist
              (bHistOctaSequenceNameCertEncodeBHist provenance))
            (bHistOctaSequenceNameCertDecodeBHist
              (bHistOctaSequenceNameCertEncodeBHist nameRow))) =
          some
            (BHistOctaSequenceNameCertUp.mk a b c d e f g h route provenance
              nameRow)
      exact
        congrArg some
          (BHistOctaSequenceNameCert_alignment_mk_congr
            (BHistOctaSequenceNameCert_alignment_decode_encode_bhist a)
            (BHistOctaSequenceNameCert_alignment_decode_encode_bhist b)
            (BHistOctaSequenceNameCert_alignment_decode_encode_bhist c)
            (BHistOctaSequenceNameCert_alignment_decode_encode_bhist d)
            (BHistOctaSequenceNameCert_alignment_decode_encode_bhist e)
            (BHistOctaSequenceNameCert_alignment_decode_encode_bhist f)
            (BHistOctaSequenceNameCert_alignment_decode_encode_bhist g)
            (BHistOctaSequenceNameCert_alignment_decode_encode_bhist h)
            (BHistOctaSequenceNameCert_alignment_decode_encode_bhist route)
            (BHistOctaSequenceNameCert_alignment_decode_encode_bhist provenance)
            (BHistOctaSequenceNameCert_alignment_decode_encode_bhist nameRow))

private theorem BHistOctaSequenceNameCert_alignment_toEventFlow_injective
    {x y : BHistOctaSequenceNameCertUp} :
    bHistOctaSequenceNameCertToEventFlow x =
      bHistOctaSequenceNameCertToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bHistOctaSequenceNameCertFromEventFlow
          (bHistOctaSequenceNameCertToEventFlow x) =
        bHistOctaSequenceNameCertFromEventFlow
          (bHistOctaSequenceNameCertToEventFlow y) :=
    congrArg bHistOctaSequenceNameCertFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BHistOctaSequenceNameCert_alignment_round_trip x).symm
      (Eq.trans hread (BHistOctaSequenceNameCert_alignment_round_trip y)))

instance bHistOctaSequenceNameCertBHistCarrier :
    BHistCarrier BHistOctaSequenceNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bHistOctaSequenceNameCertToEventFlow
  fromEventFlow := bHistOctaSequenceNameCertFromEventFlow

instance bHistOctaSequenceNameCertChapterTasteGate :
    ChapterTasteGate BHistOctaSequenceNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bHistOctaSequenceNameCertFromEventFlow
        (bHistOctaSequenceNameCertToEventFlow x) = some x
    exact BHistOctaSequenceNameCert_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BHistOctaSequenceNameCert_alignment_toEventFlow_injective heq)

instance bHistOctaSequenceNameCertFieldFaithful :
    FieldFaithful BHistOctaSequenceNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | BHistOctaSequenceNameCertUp.mk a b c d e f g h route provenance nameRow =>
        [a, b, c, d, e, f, g, h, route, provenance, nameRow]
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y hfields
    cases x with
    | mk a b c d e f g h route provenance nameRow =>
        cases y with
        | mk a' b' c' d' e' f' g' h' route' provenance' nameRow' =>
            cases hfields
            rfl

def BHistOctaSequenceNameCertCarrier [AskSetup] [PackageSetup]
    (a b c d e f g h route provenance nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory a /\ UnaryHistory b /\ UnaryHistory c /\ UnaryHistory d /\
    UnaryHistory e /\ UnaryHistory f /\ UnaryHistory g /\ UnaryHistory h /\
      UnaryHistory provenance /\ Cont a b route /\ Cont c d route /\ Cont e f route /\
        Cont g h route /\ PkgSig bundle provenance pkg /\ hsame provenance nameRow /\
          hsame nameRow a

theorem BHistOctaSequenceNameCert_alignment [AskSetup] [PackageSetup]
    {a b c d e f g h route provenance nameRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BHistOctaSequenceNameCertCarrier a b c d e f g h route provenance nameRow
        bundle pkg ->
      SemanticNameCert
        (fun row : BHist => hsame row nameRow /\ UnaryHistory row)
        (fun row : BHist =>
          hsame row a \/ hsame row b \/ hsame row c \/ hsame row d \/
            hsame row e \/ hsame row f \/ hsame row g \/ hsame row h)
        (fun _row : BHist =>
          Cont a b route /\ Cont c d route /\ Cont e f route /\ Cont g h route /\
            PkgSig bundle provenance pkg /\ hsame provenance nameRow)
        hsame := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier
  obtain
    ⟨aUnary, _bUnary, _cUnary, _dUnary, _eUnary, _fUnary, _gUnary, _hUnary,
      provenanceUnary, routeAB, routeCD, routeEF, routeGH, provenancePkg,
      sameProvenanceName, sameNameA⟩ := carrier
  have nameUnary : UnaryHistory nameRow :=
    unary_transport provenanceUnary sameProvenanceName
  exact {
    core := {
      carrier_inhabited := Exists.intro nameRow ⟨hsame_refl nameRow, nameUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same source
        cases same
        exact source
    }
    pattern_sound := by
      intro _row source
      exact Or.inl (hsame_trans source.left sameNameA)
    ledger_sound := by
      intro _row _source
      exact
        ⟨routeAB, routeCD, routeEF, routeGH, provenancePkg, sameProvenanceName⟩
  }

end BEDC.Derived.BHistOctaSequenceNameCertUp
