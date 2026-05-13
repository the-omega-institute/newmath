import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.KernelMorphismUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive KernelMorphismUp : Type where
  | mk :
      (source target map markPreservation histPreservation extPreservation contPreservation
        sigPreservation packagePreservation provenance nameCert : BHist) →
      KernelMorphismUp
  deriving DecidableEq

private def kernelMorphismEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: kernelMorphismEncodeBHist h
  | BHist.e1 h => BMark.b1 :: kernelMorphismEncodeBHist h

private def kernelMorphismDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (kernelMorphismDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (kernelMorphismDecodeBHist tail)

private theorem kernelMorphismDecode_encode_bhist :
    ∀ h : BHist, kernelMorphismDecodeBHist (kernelMorphismEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem kernelMorphism_mk_congr
    {source source' target target' map map' markPreservation markPreservation'
      histPreservation histPreservation' extPreservation extPreservation'
      contPreservation contPreservation' sigPreservation sigPreservation'
      packagePreservation packagePreservation' provenance provenance' nameCert nameCert' :
        BHist}
    (hSource : source' = source)
    (hTarget : target' = target)
    (hMap : map' = map)
    (hMarkPreservation : markPreservation' = markPreservation)
    (hHistPreservation : histPreservation' = histPreservation)
    (hExtPreservation : extPreservation' = extPreservation)
    (hContPreservation : contPreservation' = contPreservation)
    (hSigPreservation : sigPreservation' = sigPreservation)
    (hPackagePreservation : packagePreservation' = packagePreservation)
    (hProvenance : provenance' = provenance)
    (hNameCert : nameCert' = nameCert) :
    KernelMorphismUp.mk source' target' map' markPreservation' histPreservation'
        extPreservation' contPreservation' sigPreservation' packagePreservation'
        provenance' nameCert' =
      KernelMorphismUp.mk source target map markPreservation histPreservation extPreservation
        contPreservation sigPreservation packagePreservation provenance nameCert := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hSource
  cases hTarget
  cases hMap
  cases hMarkPreservation
  cases hHistPreservation
  cases hExtPreservation
  cases hContPreservation
  cases hSigPreservation
  cases hPackagePreservation
  cases hProvenance
  cases hNameCert
  rfl

private def kernelMorphismToEventFlow : KernelMorphismUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | KernelMorphismUp.mk source target map markPreservation histPreservation extPreservation
      contPreservation sigPreservation packagePreservation provenance nameCert =>
      [[BMark.b0],
        kernelMorphismEncodeBHist source,
        [BMark.b1, BMark.b0],
        kernelMorphismEncodeBHist target,
        [BMark.b1, BMark.b1, BMark.b0],
        kernelMorphismEncodeBHist map,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        kernelMorphismEncodeBHist markPreservation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        kernelMorphismEncodeBHist histPreservation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        kernelMorphismEncodeBHist extPreservation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        kernelMorphismEncodeBHist contPreservation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        kernelMorphismEncodeBHist sigPreservation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        kernelMorphismEncodeBHist packagePreservation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        kernelMorphismEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        kernelMorphismEncodeBHist nameCert]

private def kernelMorphismFromEventFlow : EventFlow → Option KernelMorphismUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | source :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | target :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | map :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | markPreservation :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | histPreservation :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | extPreservation :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | contPreservation :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | sigPreservation :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | packagePreservation :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | provenance :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] => none
                                                                                  | _tag10 :: rest20 =>
                                                                                      match rest20 with
                                                                                      | [] => none
                                                                                      | nameCert :: rest21 =>
                                                                                          match rest21 with
                                                                                          | [] =>
                                                                                              some
                                                                                                (KernelMorphismUp.mk
                                                                                                  (kernelMorphismDecodeBHist source)
                                                                                                  (kernelMorphismDecodeBHist target)
                                                                                                  (kernelMorphismDecodeBHist map)
                                                                                                  (kernelMorphismDecodeBHist markPreservation)
                                                                                                  (kernelMorphismDecodeBHist histPreservation)
                                                                                                  (kernelMorphismDecodeBHist extPreservation)
                                                                                                  (kernelMorphismDecodeBHist contPreservation)
                                                                                                  (kernelMorphismDecodeBHist sigPreservation)
                                                                                                  (kernelMorphismDecodeBHist packagePreservation)
                                                                                                  (kernelMorphismDecodeBHist provenance)
                                                                                                  (kernelMorphismDecodeBHist nameCert))
                                                                                          | _ :: _ => none

private theorem kernelMorphism_round_trip :
    ∀ x : KernelMorphismUp,
      kernelMorphismFromEventFlow (kernelMorphismToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source target map markPreservation histPreservation extPreservation
      contPreservation sigPreservation packagePreservation provenance nameCert =>
      change
        some
          (KernelMorphismUp.mk
            (kernelMorphismDecodeBHist (kernelMorphismEncodeBHist source))
            (kernelMorphismDecodeBHist (kernelMorphismEncodeBHist target))
            (kernelMorphismDecodeBHist (kernelMorphismEncodeBHist map))
            (kernelMorphismDecodeBHist (kernelMorphismEncodeBHist markPreservation))
            (kernelMorphismDecodeBHist (kernelMorphismEncodeBHist histPreservation))
            (kernelMorphismDecodeBHist (kernelMorphismEncodeBHist extPreservation))
            (kernelMorphismDecodeBHist (kernelMorphismEncodeBHist contPreservation))
            (kernelMorphismDecodeBHist (kernelMorphismEncodeBHist sigPreservation))
            (kernelMorphismDecodeBHist (kernelMorphismEncodeBHist packagePreservation))
            (kernelMorphismDecodeBHist (kernelMorphismEncodeBHist provenance))
            (kernelMorphismDecodeBHist (kernelMorphismEncodeBHist nameCert))) =
          some
            (KernelMorphismUp.mk source target map markPreservation histPreservation
              extPreservation contPreservation sigPreservation packagePreservation provenance
              nameCert)
      exact
        congrArg some
          (kernelMorphism_mk_congr
            (kernelMorphismDecode_encode_bhist source)
            (kernelMorphismDecode_encode_bhist target)
            (kernelMorphismDecode_encode_bhist map)
            (kernelMorphismDecode_encode_bhist markPreservation)
            (kernelMorphismDecode_encode_bhist histPreservation)
            (kernelMorphismDecode_encode_bhist extPreservation)
            (kernelMorphismDecode_encode_bhist contPreservation)
            (kernelMorphismDecode_encode_bhist sigPreservation)
            (kernelMorphismDecode_encode_bhist packagePreservation)
            (kernelMorphismDecode_encode_bhist provenance)
            (kernelMorphismDecode_encode_bhist nameCert))

private theorem kernelMorphismToEventFlow_injective {x y : KernelMorphismUp} :
    kernelMorphismToEventFlow x = kernelMorphismToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      kernelMorphismFromEventFlow (kernelMorphismToEventFlow x) =
        kernelMorphismFromEventFlow (kernelMorphismToEventFlow y) :=
    congrArg kernelMorphismFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (kernelMorphism_round_trip x).symm
      (Eq.trans hread (kernelMorphism_round_trip y)))

instance kernelMorphismBHistCarrier : BHistCarrier KernelMorphismUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := kernelMorphismToEventFlow
  fromEventFlow := kernelMorphismFromEventFlow

instance kernelMorphismChapterTasteGate : ChapterTasteGate KernelMorphismUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change kernelMorphismFromEventFlow (kernelMorphismToEventFlow x) = some x
    exact kernelMorphism_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (kernelMorphismToEventFlow_injective heq)

theorem KernelMorphismTasteGate_single_carrier_alignment :
    (∀ h : BHist, kernelMorphismDecodeBHist (kernelMorphismEncodeBHist h) = h) ∧
      (∀ x : KernelMorphismUp,
        kernelMorphismFromEventFlow (kernelMorphismToEventFlow x) = some x) ∧
        (∀ x y : KernelMorphismUp,
          kernelMorphismToEventFlow x = kernelMorphismToEventFlow y → x = y) ∧
          kernelMorphismEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact kernelMorphismDecode_encode_bhist
  · constructor
    · exact kernelMorphism_round_trip
    · constructor
      · intro x y heq
        exact kernelMorphismToEventFlow_injective heq
      · rfl

end BEDC.Derived.KernelMorphismUp
