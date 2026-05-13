import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetaCICSubjectReductionBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetaCICSubjectReductionBoundaryUp : Type where
  | mk :
      (beta app lam pi preservation obstruction audit transport route provenance name : BHist) →
        MetaCICSubjectReductionBoundaryUp
  deriving DecidableEq

def metaCICSubjectReductionBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metaCICSubjectReductionBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metaCICSubjectReductionBoundaryEncodeBHist h

def metaCICSubjectReductionBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metaCICSubjectReductionBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metaCICSubjectReductionBoundaryDecodeBHist tail)

private theorem metaCICSubjectReductionBoundaryDecode_encode_bhist :
    ∀ h : BHist,
      metaCICSubjectReductionBoundaryDecodeBHist
        (metaCICSubjectReductionBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem metaCICSubjectReductionBoundary_mk_congr
    {beta beta' app app' lam lam' pi pi' preservation preservation' obstruction obstruction'
      audit audit' transport transport' route route' provenance provenance' name name' : BHist}
    (hBeta : beta' = beta)
    (hApp : app' = app)
    (hLam : lam' = lam)
    (hPi : pi' = pi)
    (hPreservation : preservation' = preservation)
    (hObstruction : obstruction' = obstruction)
    (hAudit : audit' = audit)
    (hTransport : transport' = transport)
    (hRoute : route' = route)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    MetaCICSubjectReductionBoundaryUp.mk beta' app' lam' pi' preservation' obstruction'
        audit' transport' route' provenance' name' =
      MetaCICSubjectReductionBoundaryUp.mk beta app lam pi preservation obstruction audit
        transport route provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hBeta
  cases hApp
  cases hLam
  cases hPi
  cases hPreservation
  cases hObstruction
  cases hAudit
  cases hTransport
  cases hRoute
  cases hProvenance
  cases hName
  rfl

def metaCICSubjectReductionBoundaryToEventFlow :
    MetaCICSubjectReductionBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MetaCICSubjectReductionBoundaryUp.mk beta app lam pi preservation obstruction audit
      transport route provenance name =>
      [[BMark.b0],
        metaCICSubjectReductionBoundaryEncodeBHist beta,
        [BMark.b1, BMark.b0],
        metaCICSubjectReductionBoundaryEncodeBHist app,
        [BMark.b1, BMark.b1, BMark.b0],
        metaCICSubjectReductionBoundaryEncodeBHist lam,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICSubjectReductionBoundaryEncodeBHist pi,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICSubjectReductionBoundaryEncodeBHist preservation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICSubjectReductionBoundaryEncodeBHist obstruction,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICSubjectReductionBoundaryEncodeBHist audit,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        metaCICSubjectReductionBoundaryEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        metaCICSubjectReductionBoundaryEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        metaCICSubjectReductionBoundaryEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICSubjectReductionBoundaryEncodeBHist name]

def metaCICSubjectReductionBoundaryFromEventFlow :
    EventFlow → Option MetaCICSubjectReductionBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | _tag0 :: beta :: _tag1 :: app :: _tag2 :: lam :: _tag3 :: pi :: _tag4 ::
      preservation :: _tag5 :: obstruction :: _tag6 :: audit :: _tag7 :: transport ::
      _tag8 :: route :: _tag9 :: provenance :: _tag10 :: name :: [] =>
      some
        (MetaCICSubjectReductionBoundaryUp.mk
          (metaCICSubjectReductionBoundaryDecodeBHist beta)
          (metaCICSubjectReductionBoundaryDecodeBHist app)
          (metaCICSubjectReductionBoundaryDecodeBHist lam)
          (metaCICSubjectReductionBoundaryDecodeBHist pi)
          (metaCICSubjectReductionBoundaryDecodeBHist preservation)
          (metaCICSubjectReductionBoundaryDecodeBHist obstruction)
          (metaCICSubjectReductionBoundaryDecodeBHist audit)
          (metaCICSubjectReductionBoundaryDecodeBHist transport)
          (metaCICSubjectReductionBoundaryDecodeBHist route)
          (metaCICSubjectReductionBoundaryDecodeBHist provenance)
          (metaCICSubjectReductionBoundaryDecodeBHist name))
  | _ => none

private theorem metaCICSubjectReductionBoundary_round_trip :
    ∀ x : MetaCICSubjectReductionBoundaryUp,
      metaCICSubjectReductionBoundaryFromEventFlow
        (metaCICSubjectReductionBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk beta app lam pi preservation obstruction audit transport route provenance name =>
      exact
        congrArg some
          (metaCICSubjectReductionBoundary_mk_congr
            (metaCICSubjectReductionBoundaryDecode_encode_bhist beta)
            (metaCICSubjectReductionBoundaryDecode_encode_bhist app)
            (metaCICSubjectReductionBoundaryDecode_encode_bhist lam)
            (metaCICSubjectReductionBoundaryDecode_encode_bhist pi)
            (metaCICSubjectReductionBoundaryDecode_encode_bhist preservation)
            (metaCICSubjectReductionBoundaryDecode_encode_bhist obstruction)
            (metaCICSubjectReductionBoundaryDecode_encode_bhist audit)
            (metaCICSubjectReductionBoundaryDecode_encode_bhist transport)
            (metaCICSubjectReductionBoundaryDecode_encode_bhist route)
            (metaCICSubjectReductionBoundaryDecode_encode_bhist provenance)
            (metaCICSubjectReductionBoundaryDecode_encode_bhist name))

private theorem metaCICSubjectReductionBoundaryToEventFlow_injective
    {x y : MetaCICSubjectReductionBoundaryUp} :
    metaCICSubjectReductionBoundaryToEventFlow x =
        metaCICSubjectReductionBoundaryToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metaCICSubjectReductionBoundaryFromEventFlow
          (metaCICSubjectReductionBoundaryToEventFlow x) =
        metaCICSubjectReductionBoundaryFromEventFlow
          (metaCICSubjectReductionBoundaryToEventFlow y) :=
    congrArg metaCICSubjectReductionBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (metaCICSubjectReductionBoundary_round_trip x).symm
      (Eq.trans hread (metaCICSubjectReductionBoundary_round_trip y)))

instance metaCICSubjectReductionBoundaryBHistCarrier :
    BHistCarrier MetaCICSubjectReductionBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metaCICSubjectReductionBoundaryToEventFlow
  fromEventFlow := metaCICSubjectReductionBoundaryFromEventFlow

instance metaCICSubjectReductionBoundaryChapterTasteGate :
    ChapterTasteGate MetaCICSubjectReductionBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metaCICSubjectReductionBoundaryFromEventFlow
          (metaCICSubjectReductionBoundaryToEventFlow x) = some x
    exact metaCICSubjectReductionBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metaCICSubjectReductionBoundaryToEventFlow_injective heq)

instance metaCICSubjectReductionBoundaryFieldFaithful :
    FieldFaithful MetaCICSubjectReductionBoundaryUp where
  fields := fun x =>
    match x with
    | MetaCICSubjectReductionBoundaryUp.mk beta app lam pi preservation obstruction audit
        transport route provenance name =>
        [beta, app, lam, pi, preservation, obstruction, audit, transport, route,
          provenance, name]
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y h
    cases x with
    | mk beta₁ app₁ lam₁ pi₁ preservation₁ obstruction₁ audit₁ transport₁ route₁
        provenance₁ name₁ =>
      cases y with
      | mk beta₂ app₂ lam₂ pi₂ preservation₂ obstruction₂ audit₂ transport₂ route₂
          provenance₂ name₂ =>
        injection h with hBeta t1
        injection t1 with hApp t2
        injection t2 with hLam t3
        injection t3 with hPi t4
        injection t4 with hPreservation t5
        injection t5 with hObstruction t6
        injection t6 with hAudit t7
        injection t7 with hTransport t8
        injection t8 with hRoute t9
        injection t9 with hProvenance t10
        injection t10 with hName _
        cases hBeta
        cases hApp
        cases hLam
        cases hPi
        cases hPreservation
        cases hObstruction
        cases hAudit
        cases hTransport
        cases hRoute
        cases hProvenance
        cases hName
        rfl

theorem MetaCICSubjectReductionBoundaryTasteGate_single_carrier_alignment :
    (forall h : BHist,
      metaCICSubjectReductionBoundaryDecodeBHist
        (metaCICSubjectReductionBoundaryEncodeBHist h) = h) /\
      (forall x : MetaCICSubjectReductionBoundaryUp,
        metaCICSubjectReductionBoundaryFromEventFlow
          (metaCICSubjectReductionBoundaryToEventFlow x) = some x) /\
      (forall x y : MetaCICSubjectReductionBoundaryUp,
        metaCICSubjectReductionBoundaryToEventFlow x =
          metaCICSubjectReductionBoundaryToEventFlow y -> x = y) /\
      metaCICSubjectReductionBoundaryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact metaCICSubjectReductionBoundaryDecode_encode_bhist
  · constructor
    · exact metaCICSubjectReductionBoundary_round_trip
    · constructor
      · intro x y heq
        exact metaCICSubjectReductionBoundaryToEventFlow_injective heq
      · rfl

end BEDC.Derived.MetaCICSubjectReductionBoundaryUp
