import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetaCICRedexFrontierUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetaCICRedexFrontierUp : Type where
  | mk :
      (betaRedex appArgument lambdaDomain piDomain obstruction betaBoundary transport replay
        provenance nameCert : BHist) →
      MetaCICRedexFrontierUp
  deriving DecidableEq

def metaCICRedexFrontierEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metaCICRedexFrontierEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metaCICRedexFrontierEncodeBHist h

def metaCICRedexFrontierDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metaCICRedexFrontierDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metaCICRedexFrontierDecodeBHist tail)

private theorem metaCICRedexFrontierDecode_encode_bhist :
    ∀ h : BHist, metaCICRedexFrontierDecodeBHist
      (metaCICRedexFrontierEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def metaCICRedexFrontierToEventFlow : MetaCICRedexFrontierUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MetaCICRedexFrontierUp.mk betaRedex appArgument lambdaDomain piDomain obstruction
      betaBoundary transport replay provenance nameCert =>
      [[BMark.b0],
        metaCICRedexFrontierEncodeBHist betaRedex,
        [BMark.b1, BMark.b0],
        metaCICRedexFrontierEncodeBHist appArgument,
        [BMark.b1, BMark.b1, BMark.b0],
        metaCICRedexFrontierEncodeBHist lambdaDomain,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICRedexFrontierEncodeBHist piDomain,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICRedexFrontierEncodeBHist obstruction,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICRedexFrontierEncodeBHist betaBoundary,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICRedexFrontierEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        metaCICRedexFrontierEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        metaCICRedexFrontierEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        metaCICRedexFrontierEncodeBHist nameCert]

def metaCICRedexFrontierFromEventFlow : EventFlow → Option MetaCICRedexFrontierUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | betaRedex :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | appArgument :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | lambdaDomain :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | piDomain :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | obstruction :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | betaBoundary :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | transport :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | replay :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | provenance :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | nameCert :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] =>
                                                                                      some
                                                                                        (MetaCICRedexFrontierUp.mk
                                                                                          (metaCICRedexFrontierDecodeBHist
                                                                                            betaRedex)
                                                                                          (metaCICRedexFrontierDecodeBHist
                                                                                            appArgument)
                                                                                          (metaCICRedexFrontierDecodeBHist
                                                                                            lambdaDomain)
                                                                                          (metaCICRedexFrontierDecodeBHist
                                                                                            piDomain)
                                                                                          (metaCICRedexFrontierDecodeBHist
                                                                                            obstruction)
                                                                                          (metaCICRedexFrontierDecodeBHist
                                                                                            betaBoundary)
                                                                                          (metaCICRedexFrontierDecodeBHist
                                                                                            transport)
                                                                                          (metaCICRedexFrontierDecodeBHist
                                                                                            replay)
                                                                                          (metaCICRedexFrontierDecodeBHist
                                                                                            provenance)
                                                                                          (metaCICRedexFrontierDecodeBHist
                                                                                            nameCert))
                                                                                  | _ :: _ => none

private theorem metaCICRedexFrontier_round_trip :
    ∀ x : MetaCICRedexFrontierUp,
      metaCICRedexFrontierFromEventFlow (metaCICRedexFrontierToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk betaRedex appArgument lambdaDomain piDomain obstruction betaBoundary transport replay
      provenance nameCert =>
      change
        some
          (MetaCICRedexFrontierUp.mk
            (metaCICRedexFrontierDecodeBHist
              (metaCICRedexFrontierEncodeBHist betaRedex))
            (metaCICRedexFrontierDecodeBHist
              (metaCICRedexFrontierEncodeBHist appArgument))
            (metaCICRedexFrontierDecodeBHist
              (metaCICRedexFrontierEncodeBHist lambdaDomain))
            (metaCICRedexFrontierDecodeBHist
              (metaCICRedexFrontierEncodeBHist piDomain))
            (metaCICRedexFrontierDecodeBHist
              (metaCICRedexFrontierEncodeBHist obstruction))
            (metaCICRedexFrontierDecodeBHist
              (metaCICRedexFrontierEncodeBHist betaBoundary))
            (metaCICRedexFrontierDecodeBHist
              (metaCICRedexFrontierEncodeBHist transport))
            (metaCICRedexFrontierDecodeBHist
              (metaCICRedexFrontierEncodeBHist replay))
            (metaCICRedexFrontierDecodeBHist
              (metaCICRedexFrontierEncodeBHist provenance))
            (metaCICRedexFrontierDecodeBHist
              (metaCICRedexFrontierEncodeBHist nameCert))) =
          some
            (MetaCICRedexFrontierUp.mk betaRedex appArgument lambdaDomain piDomain
              obstruction betaBoundary transport replay provenance nameCert)
      rw [metaCICRedexFrontierDecode_encode_bhist betaRedex,
        metaCICRedexFrontierDecode_encode_bhist appArgument,
        metaCICRedexFrontierDecode_encode_bhist lambdaDomain,
        metaCICRedexFrontierDecode_encode_bhist piDomain,
        metaCICRedexFrontierDecode_encode_bhist obstruction,
        metaCICRedexFrontierDecode_encode_bhist betaBoundary,
        metaCICRedexFrontierDecode_encode_bhist transport,
        metaCICRedexFrontierDecode_encode_bhist replay,
        metaCICRedexFrontierDecode_encode_bhist provenance,
        metaCICRedexFrontierDecode_encode_bhist nameCert]

private theorem metaCICRedexFrontierToEventFlow_injective
    {x y : MetaCICRedexFrontierUp} :
    metaCICRedexFrontierToEventFlow x = metaCICRedexFrontierToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metaCICRedexFrontierFromEventFlow (metaCICRedexFrontierToEventFlow x) =
        metaCICRedexFrontierFromEventFlow (metaCICRedexFrontierToEventFlow y) :=
    congrArg metaCICRedexFrontierFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (metaCICRedexFrontier_round_trip x).symm
      (Eq.trans hread (metaCICRedexFrontier_round_trip y)))

instance metaCICRedexFrontierBHistCarrier : BHistCarrier MetaCICRedexFrontierUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metaCICRedexFrontierToEventFlow
  fromEventFlow := metaCICRedexFrontierFromEventFlow

instance metaCICRedexFrontierChapterTasteGate : ChapterTasteGate MetaCICRedexFrontierUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change metaCICRedexFrontierFromEventFlow
      (metaCICRedexFrontierToEventFlow x) = some x
    exact metaCICRedexFrontier_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metaCICRedexFrontierToEventFlow_injective heq)

def taste_gate : ChapterTasteGate MetaCICRedexFrontierUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metaCICRedexFrontierChapterTasteGate

instance metaCICRedexFrontierFieldFaithful : FieldFaithful MetaCICRedexFrontierUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | MetaCICRedexFrontierUp.mk betaRedex appArgument lambdaDomain piDomain obstruction
        betaBoundary transport replay provenance nameCert =>
        [betaRedex, appArgument, lambdaDomain, piDomain, obstruction, betaBoundary, transport,
          replay, provenance, nameCert]
  field_faithful := by
    intro x y h
    cases x with
    | mk betaRedex₁ appArgument₁ lambdaDomain₁ piDomain₁ obstruction₁ betaBoundary₁
        transport₁ replay₁ provenance₁ nameCert₁ =>
        cases y with
        | mk betaRedex₂ appArgument₂ lambdaDomain₂ piDomain₂ obstruction₂ betaBoundary₂
            transport₂ replay₂ provenance₂ nameCert₂ =>
            simp only [] at h
            cases h
            rfl

theorem MetaCICRedexFrontierCarrier_beta_boundary_route
    (x : MetaCICRedexFrontierUp) :
    ∃ betaRedex appArgument lambdaDomain piDomain obstruction betaBoundary transport replay
        provenance nameCert : BHist,
      x = MetaCICRedexFrontierUp.mk betaRedex appArgument lambdaDomain piDomain obstruction
        betaBoundary transport replay provenance nameCert ∧
        metaCICRedexFrontierFromEventFlow (metaCICRedexFrontierToEventFlow x) = some x ∧
          metaCICRedexFrontierEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk betaRedex appArgument lambdaDomain piDomain obstruction betaBoundary transport replay
      provenance nameCert =>
      refine
        ⟨betaRedex, appArgument, lambdaDomain, piDomain, obstruction, betaBoundary,
          transport, replay, provenance, nameCert, ?_⟩
      constructor
      · rfl
      · constructor
        · exact metaCICRedexFrontier_round_trip
            (MetaCICRedexFrontierUp.mk betaRedex appArgument lambdaDomain piDomain
              obstruction betaBoundary transport replay provenance nameCert)
        · rfl

theorem MetaCICRedexFrontierTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      metaCICRedexFrontierDecodeBHist (metaCICRedexFrontierEncodeBHist h) = h) ∧
      (∀ x : MetaCICRedexFrontierUp,
        metaCICRedexFrontierFromEventFlow (metaCICRedexFrontierToEventFlow x) = some x) ∧
        (∀ x y : MetaCICRedexFrontierUp,
          metaCICRedexFrontierToEventFlow x = metaCICRedexFrontierToEventFlow y → x = y) ∧
          metaCICRedexFrontierEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact metaCICRedexFrontierDecode_encode_bhist
  · constructor
    · exact metaCICRedexFrontier_round_trip
    · constructor
      · intro x y heq
        exact metaCICRedexFrontierToEventFlow_injective heq
      · rfl

end BEDC.Derived.MetaCICRedexFrontierUp
