import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ClassifierMorphismUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ClassifierMorphismUp : Type where
  | mk :
      (source target graph extPreservation sigPreservation contPreservation transport
        provenance nameCert : BHist) →
      ClassifierMorphismUp
  deriving DecidableEq

private def classifierMorphismEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: classifierMorphismEncodeBHist h
  | BHist.e1 h => BMark.b1 :: classifierMorphismEncodeBHist h

private def classifierMorphismDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (classifierMorphismDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (classifierMorphismDecodeBHist tail)

private theorem classifierMorphismDecodeEncodeBHist :
    ∀ h : BHist, classifierMorphismDecodeBHist (classifierMorphismEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem classifierMorphismMkCongr
    {source source' target target' graph graph' extPreservation extPreservation'
      sigPreservation sigPreservation' contPreservation contPreservation' transport transport'
      provenance provenance' nameCert nameCert' : BHist} :
    source = source' →
      target = target' →
        graph = graph' →
          extPreservation = extPreservation' →
            sigPreservation = sigPreservation' →
              contPreservation = contPreservation' →
                transport = transport' →
                  provenance = provenance' →
                    nameCert = nameCert' →
                      ClassifierMorphismUp.mk source target graph extPreservation
                        sigPreservation contPreservation transport provenance nameCert =
                        ClassifierMorphismUp.mk source' target' graph' extPreservation'
                          sigPreservation' contPreservation' transport' provenance' nameCert' := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hsource htarget hgraph hextPreservation hsigPreservation hcontPreservation
    htransport hprovenance hnameCert
  cases hsource
  cases htarget
  cases hgraph
  cases hextPreservation
  cases hsigPreservation
  cases hcontPreservation
  cases htransport
  cases hprovenance
  cases hnameCert
  rfl

private def classifierMorphismToEventFlow : ClassifierMorphismUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ClassifierMorphismUp.mk source target graph extPreservation sigPreservation
      contPreservation transport provenance nameCert =>
      [classifierMorphismEncodeBHist source,
        classifierMorphismEncodeBHist target,
        classifierMorphismEncodeBHist graph,
        classifierMorphismEncodeBHist extPreservation,
        classifierMorphismEncodeBHist sigPreservation,
        classifierMorphismEncodeBHist contPreservation,
        classifierMorphismEncodeBHist transport,
        classifierMorphismEncodeBHist provenance,
        classifierMorphismEncodeBHist nameCert]

private def classifierMorphismFromEventFlow : EventFlow → Option ClassifierMorphismUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | source :: rest0 =>
      match rest0 with
      | [] => none
      | target :: rest1 =>
          match rest1 with
          | [] => none
          | graph :: rest2 =>
              match rest2 with
              | [] => none
              | extPreservation :: rest3 =>
                  match rest3 with
                  | [] => none
                  | sigPreservation :: rest4 =>
                      match rest4 with
                      | [] => none
                      | contPreservation :: rest5 =>
                          match rest5 with
                          | [] => none
                          | transport :: rest6 =>
                              match rest6 with
                              | [] => none
                              | provenance :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | nameCert :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some
                                            (ClassifierMorphismUp.mk
                                              (classifierMorphismDecodeBHist source)
                                              (classifierMorphismDecodeBHist target)
                                              (classifierMorphismDecodeBHist graph)
                                              (classifierMorphismDecodeBHist extPreservation)
                                              (classifierMorphismDecodeBHist sigPreservation)
                                              (classifierMorphismDecodeBHist contPreservation)
                                              (classifierMorphismDecodeBHist transport)
                                              (classifierMorphismDecodeBHist provenance)
                                              (classifierMorphismDecodeBHist nameCert))
                                      | _ :: _ => none

private theorem classifierMorphism_round_trip :
    ∀ x : ClassifierMorphismUp,
      classifierMorphismFromEventFlow (classifierMorphismToEventFlow x) = some x
  -- BEDC touchpoint anchor: BHist BMark
  | ClassifierMorphismUp.mk source target graph extPreservation sigPreservation contPreservation
      transport provenance nameCert =>
      congrArg some
        (classifierMorphismMkCongr
          (classifierMorphismDecodeEncodeBHist source)
          (classifierMorphismDecodeEncodeBHist target)
          (classifierMorphismDecodeEncodeBHist graph)
          (classifierMorphismDecodeEncodeBHist extPreservation)
          (classifierMorphismDecodeEncodeBHist sigPreservation)
          (classifierMorphismDecodeEncodeBHist contPreservation)
          (classifierMorphismDecodeEncodeBHist transport)
          (classifierMorphismDecodeEncodeBHist provenance)
          (classifierMorphismDecodeEncodeBHist nameCert))

private theorem classifierMorphismToEventFlow_injective {x y : ClassifierMorphismUp} :
    classifierMorphismToEventFlow x = classifierMorphismToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      classifierMorphismFromEventFlow (classifierMorphismToEventFlow x) =
        classifierMorphismFromEventFlow (classifierMorphismToEventFlow y) :=
    congrArg classifierMorphismFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (classifierMorphism_round_trip x).symm
      (Eq.trans hread (classifierMorphism_round_trip y)))

instance classifierMorphismBHistCarrier : BHistCarrier ClassifierMorphismUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := classifierMorphismToEventFlow
  fromEventFlow := classifierMorphismFromEventFlow

instance classifierMorphismChapterTasteGate : ChapterTasteGate ClassifierMorphismUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change classifierMorphismFromEventFlow (classifierMorphismToEventFlow x) = some x
    exact classifierMorphism_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (classifierMorphismToEventFlow_injective heq)

theorem ClassifierMorphismUp_taste_gate_boundary :
    (∀ h : BHist, classifierMorphismDecodeBHist (classifierMorphismEncodeBHist h) = h) ∧
      (∀ x : ClassifierMorphismUp,
        classifierMorphismFromEventFlow (classifierMorphismToEventFlow x) = some x) ∧
        (∀ x y : ClassifierMorphismUp,
          classifierMorphismToEventFlow x = classifierMorphismToEventFlow y → x = y) ∧
          ∃ x : ClassifierMorphismUp,
            x =
                ClassifierMorphismUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty ∧
              classifierMorphismFromEventFlow (classifierMorphismToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  let x : ClassifierMorphismUp :=
    ClassifierMorphismUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
      BHist.Empty BHist.Empty BHist.Empty BHist.Empty
  constructor
  · exact classifierMorphismDecodeEncodeBHist
  · constructor
    · exact classifierMorphism_round_trip
    · constructor
      · intro left right heq
        exact classifierMorphismToEventFlow_injective heq
      · exact ⟨x, rfl, classifierMorphism_round_trip x⟩

end BEDC.Derived.ClassifierMorphismUp
