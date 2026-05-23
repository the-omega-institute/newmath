import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BoundedNormalEqualityCheckerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BoundedNormalEqualityCheckerUp : Type where
  | mk :
      (left right fuel normalLeft normalRight equality witness closed transport route
        provenance nameCert : BHist) →
      BoundedNormalEqualityCheckerUp
  deriving DecidableEq

private def boundedNormalEqualityCheckerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: boundedNormalEqualityCheckerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: boundedNormalEqualityCheckerEncodeBHist h

private def boundedNormalEqualityCheckerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (boundedNormalEqualityCheckerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (boundedNormalEqualityCheckerDecodeBHist tail)

private theorem boundedNormalEqualityCheckerDecode_encode_bhist :
    ∀ h : BHist,
      boundedNormalEqualityCheckerDecodeBHist
        (boundedNormalEqualityCheckerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem boundedNormalEqualityChecker_mk_congr
    {left left' right right' fuel fuel' normalLeft normalLeft' normalRight normalRight'
      equality equality' witness witness' closed closed' transport transport' route route'
      provenance provenance' nameCert nameCert' : BHist}
    (hLeft : left' = left)
    (hRight : right' = right)
    (hFuel : fuel' = fuel)
    (hNormalLeft : normalLeft' = normalLeft)
    (hNormalRight : normalRight' = normalRight)
    (hEquality : equality' = equality)
    (hWitness : witness' = witness)
    (hClosed : closed' = closed)
    (hTransport : transport' = transport)
    (hRoute : route' = route)
    (hProvenance : provenance' = provenance)
    (hNameCert : nameCert' = nameCert) :
    BoundedNormalEqualityCheckerUp.mk left' right' fuel' normalLeft' normalRight' equality'
        witness' closed' transport' route' provenance' nameCert' =
      BoundedNormalEqualityCheckerUp.mk left right fuel normalLeft normalRight equality witness
        closed transport route provenance nameCert := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hLeft
  cases hRight
  cases hFuel
  cases hNormalLeft
  cases hNormalRight
  cases hEquality
  cases hWitness
  cases hClosed
  cases hTransport
  cases hRoute
  cases hProvenance
  cases hNameCert
  rfl

private def boundedNormalEqualityCheckerToEventFlow :
    BoundedNormalEqualityCheckerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BoundedNormalEqualityCheckerUp.mk left right fuel normalLeft normalRight equality witness
      closed transport route provenance nameCert =>
      [[BMark.b0],
        boundedNormalEqualityCheckerEncodeBHist left,
        [BMark.b1, BMark.b0],
        boundedNormalEqualityCheckerEncodeBHist right,
        [BMark.b1, BMark.b1, BMark.b0],
        boundedNormalEqualityCheckerEncodeBHist fuel,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        boundedNormalEqualityCheckerEncodeBHist normalLeft,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        boundedNormalEqualityCheckerEncodeBHist normalRight,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        boundedNormalEqualityCheckerEncodeBHist equality,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        boundedNormalEqualityCheckerEncodeBHist witness,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        boundedNormalEqualityCheckerEncodeBHist closed,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        boundedNormalEqualityCheckerEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        boundedNormalEqualityCheckerEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        boundedNormalEqualityCheckerEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        boundedNormalEqualityCheckerEncodeBHist nameCert]

private def boundedNormalEqualityCheckerFromEventFlow :
    EventFlow → Option BoundedNormalEqualityCheckerUp
  -- BEDC touchpoint anchor: BHist BMark
  | [
      _tag0, left, _tag1, right, _tag2, fuel, _tag3, normalLeft, _tag4,
      normalRight, _tag5, equality, _tag6, witness, _tag7, closed, _tag8,
      transport, _tag9, route, _tag10, provenance, _tag11, nameCert] =>
      some
        (BoundedNormalEqualityCheckerUp.mk
          (boundedNormalEqualityCheckerDecodeBHist left)
          (boundedNormalEqualityCheckerDecodeBHist right)
          (boundedNormalEqualityCheckerDecodeBHist fuel)
          (boundedNormalEqualityCheckerDecodeBHist normalLeft)
          (boundedNormalEqualityCheckerDecodeBHist normalRight)
          (boundedNormalEqualityCheckerDecodeBHist equality)
          (boundedNormalEqualityCheckerDecodeBHist witness)
          (boundedNormalEqualityCheckerDecodeBHist closed)
          (boundedNormalEqualityCheckerDecodeBHist transport)
          (boundedNormalEqualityCheckerDecodeBHist route)
          (boundedNormalEqualityCheckerDecodeBHist provenance)
          (boundedNormalEqualityCheckerDecodeBHist nameCert))
  | _ => none

private theorem boundedNormalEqualityChecker_round_trip :
    ∀ x : BoundedNormalEqualityCheckerUp,
      boundedNormalEqualityCheckerFromEventFlow
        (boundedNormalEqualityCheckerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk left right fuel normalLeft normalRight equality witness closed transport route
      provenance nameCert =>
      change
        some
          (BoundedNormalEqualityCheckerUp.mk
            (boundedNormalEqualityCheckerDecodeBHist
              (boundedNormalEqualityCheckerEncodeBHist left))
            (boundedNormalEqualityCheckerDecodeBHist
              (boundedNormalEqualityCheckerEncodeBHist right))
            (boundedNormalEqualityCheckerDecodeBHist
              (boundedNormalEqualityCheckerEncodeBHist fuel))
            (boundedNormalEqualityCheckerDecodeBHist
              (boundedNormalEqualityCheckerEncodeBHist normalLeft))
            (boundedNormalEqualityCheckerDecodeBHist
              (boundedNormalEqualityCheckerEncodeBHist normalRight))
            (boundedNormalEqualityCheckerDecodeBHist
              (boundedNormalEqualityCheckerEncodeBHist equality))
            (boundedNormalEqualityCheckerDecodeBHist
              (boundedNormalEqualityCheckerEncodeBHist witness))
            (boundedNormalEqualityCheckerDecodeBHist
              (boundedNormalEqualityCheckerEncodeBHist closed))
            (boundedNormalEqualityCheckerDecodeBHist
              (boundedNormalEqualityCheckerEncodeBHist transport))
            (boundedNormalEqualityCheckerDecodeBHist
              (boundedNormalEqualityCheckerEncodeBHist route))
            (boundedNormalEqualityCheckerDecodeBHist
              (boundedNormalEqualityCheckerEncodeBHist provenance))
            (boundedNormalEqualityCheckerDecodeBHist
              (boundedNormalEqualityCheckerEncodeBHist nameCert))) =
          some
            (BoundedNormalEqualityCheckerUp.mk left right fuel normalLeft normalRight equality
              witness closed transport route provenance nameCert)
      exact
        congrArg some
          (boundedNormalEqualityChecker_mk_congr
            (boundedNormalEqualityCheckerDecode_encode_bhist left)
            (boundedNormalEqualityCheckerDecode_encode_bhist right)
            (boundedNormalEqualityCheckerDecode_encode_bhist fuel)
            (boundedNormalEqualityCheckerDecode_encode_bhist normalLeft)
            (boundedNormalEqualityCheckerDecode_encode_bhist normalRight)
            (boundedNormalEqualityCheckerDecode_encode_bhist equality)
            (boundedNormalEqualityCheckerDecode_encode_bhist witness)
            (boundedNormalEqualityCheckerDecode_encode_bhist closed)
            (boundedNormalEqualityCheckerDecode_encode_bhist transport)
            (boundedNormalEqualityCheckerDecode_encode_bhist route)
            (boundedNormalEqualityCheckerDecode_encode_bhist provenance)
            (boundedNormalEqualityCheckerDecode_encode_bhist nameCert))

private theorem boundedNormalEqualityCheckerToEventFlow_injective
    {x y : BoundedNormalEqualityCheckerUp} :
    boundedNormalEqualityCheckerToEventFlow x = boundedNormalEqualityCheckerToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      boundedNormalEqualityCheckerFromEventFlow (boundedNormalEqualityCheckerToEventFlow x) =
        boundedNormalEqualityCheckerFromEventFlow (boundedNormalEqualityCheckerToEventFlow y) :=
    congrArg boundedNormalEqualityCheckerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (boundedNormalEqualityChecker_round_trip x).symm
      (Eq.trans hread (boundedNormalEqualityChecker_round_trip y)))

instance boundedNormalEqualityCheckerBHistCarrier :
    BHistCarrier BoundedNormalEqualityCheckerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := boundedNormalEqualityCheckerToEventFlow
  fromEventFlow := boundedNormalEqualityCheckerFromEventFlow

instance boundedNormalEqualityCheckerChapterTasteGate :
    ChapterTasteGate BoundedNormalEqualityCheckerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      boundedNormalEqualityCheckerFromEventFlow
        (boundedNormalEqualityCheckerToEventFlow x) = some x
    exact boundedNormalEqualityChecker_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (boundedNormalEqualityCheckerToEventFlow_injective heq)

theorem BoundedNormalEqualityCheckerTasteGate_single_carrier_alignment :
    ∀ h : BHist,
      boundedNormalEqualityCheckerDecodeBHist
        (boundedNormalEqualityCheckerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  exact boundedNormalEqualityCheckerDecode_encode_bhist

end BEDC.Derived.BoundedNormalEqualityCheckerUp
