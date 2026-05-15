import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.GammaZetaFactorSealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive GammaZetaFactorSealUp : Type where
  | mk
      (gammaDomain reflectedInput factorSlot zetaApplication transport replay provenance
        nameCert : BHist) :
      GammaZetaFactorSealUp
  deriving DecidableEq

def gammaZetaFactorSealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: gammaZetaFactorSealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: gammaZetaFactorSealEncodeBHist h

def gammaZetaFactorSealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (gammaZetaFactorSealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (gammaZetaFactorSealDecodeBHist tail)

private theorem GammaZetaFactorSealTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      gammaZetaFactorSealDecodeBHist
        (gammaZetaFactorSealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem GammaZetaFactorSealTasteGate_single_carrier_alignment_mk_congr
    {gammaDomain gammaDomain' reflectedInput reflectedInput' factorSlot factorSlot'
      zetaApplication zetaApplication' transport transport' replay replay'
      provenance provenance' nameCert nameCert' : BHist}
    (hGammaDomain : gammaDomain' = gammaDomain)
    (hReflectedInput : reflectedInput' = reflectedInput)
    (hFactorSlot : factorSlot' = factorSlot)
    (hZetaApplication : zetaApplication' = zetaApplication)
    (hTransport : transport' = transport)
    (hReplay : replay' = replay)
    (hProvenance : provenance' = provenance)
    (hNameCert : nameCert' = nameCert) :
    GammaZetaFactorSealUp.mk gammaDomain' reflectedInput' factorSlot'
        zetaApplication' transport' replay' provenance' nameCert' =
      GammaZetaFactorSealUp.mk gammaDomain reflectedInput factorSlot
        zetaApplication transport replay provenance nameCert := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hGammaDomain
  cases hReflectedInput
  cases hFactorSlot
  cases hZetaApplication
  cases hTransport
  cases hReplay
  cases hProvenance
  cases hNameCert
  rfl

def gammaZetaFactorSealToEventFlow :
    GammaZetaFactorSealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | GammaZetaFactorSealUp.mk gammaDomain reflectedInput factorSlot
      zetaApplication transport replay provenance nameCert =>
      [[BMark.b0],
        gammaZetaFactorSealEncodeBHist gammaDomain,
        [BMark.b1, BMark.b0],
        gammaZetaFactorSealEncodeBHist reflectedInput,
        [BMark.b1, BMark.b1, BMark.b0],
        gammaZetaFactorSealEncodeBHist factorSlot,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        gammaZetaFactorSealEncodeBHist zetaApplication,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        gammaZetaFactorSealEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        gammaZetaFactorSealEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        gammaZetaFactorSealEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        gammaZetaFactorSealEncodeBHist nameCert]

def gammaZetaFactorSealFromEventFlow :
    EventFlow → Option GammaZetaFactorSealUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | gammaDomain :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | reflectedInput :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | factorSlot :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | zetaApplication :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | transport :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | replay :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | provenance :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | nameCert :: rest15 =>
                                                                  match rest15 with
                                                                  | [] =>
                                                                      some
                                                                        (GammaZetaFactorSealUp.mk
                                                                          (gammaZetaFactorSealDecodeBHist gammaDomain)
                                                                          (gammaZetaFactorSealDecodeBHist reflectedInput)
                                                                          (gammaZetaFactorSealDecodeBHist factorSlot)
                                                                          (gammaZetaFactorSealDecodeBHist zetaApplication)
                                                                          (gammaZetaFactorSealDecodeBHist transport)
                                                                          (gammaZetaFactorSealDecodeBHist replay)
                                                                          (gammaZetaFactorSealDecodeBHist provenance)
                                                                          (gammaZetaFactorSealDecodeBHist nameCert))
                                                                  | _ :: _ => none

private theorem GammaZetaFactorSealTasteGate_single_carrier_alignment_round_trip :
    ∀ x : GammaZetaFactorSealUp,
      gammaZetaFactorSealFromEventFlow
        (gammaZetaFactorSealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk gammaDomain reflectedInput factorSlot zetaApplication transport replay
      provenance nameCert =>
      change
        some
          (GammaZetaFactorSealUp.mk
            (gammaZetaFactorSealDecodeBHist
              (gammaZetaFactorSealEncodeBHist gammaDomain))
            (gammaZetaFactorSealDecodeBHist
              (gammaZetaFactorSealEncodeBHist reflectedInput))
            (gammaZetaFactorSealDecodeBHist
              (gammaZetaFactorSealEncodeBHist factorSlot))
            (gammaZetaFactorSealDecodeBHist
              (gammaZetaFactorSealEncodeBHist zetaApplication))
            (gammaZetaFactorSealDecodeBHist
              (gammaZetaFactorSealEncodeBHist transport))
            (gammaZetaFactorSealDecodeBHist
              (gammaZetaFactorSealEncodeBHist replay))
            (gammaZetaFactorSealDecodeBHist
              (gammaZetaFactorSealEncodeBHist provenance))
            (gammaZetaFactorSealDecodeBHist
              (gammaZetaFactorSealEncodeBHist nameCert))) =
          some
            (GammaZetaFactorSealUp.mk gammaDomain reflectedInput factorSlot
              zetaApplication transport replay provenance nameCert)
      exact
        congrArg some
          (GammaZetaFactorSealTasteGate_single_carrier_alignment_mk_congr
            (GammaZetaFactorSealTasteGate_single_carrier_alignment_decode gammaDomain)
            (GammaZetaFactorSealTasteGate_single_carrier_alignment_decode reflectedInput)
            (GammaZetaFactorSealTasteGate_single_carrier_alignment_decode factorSlot)
            (GammaZetaFactorSealTasteGate_single_carrier_alignment_decode zetaApplication)
            (GammaZetaFactorSealTasteGate_single_carrier_alignment_decode transport)
            (GammaZetaFactorSealTasteGate_single_carrier_alignment_decode replay)
            (GammaZetaFactorSealTasteGate_single_carrier_alignment_decode provenance)
            (GammaZetaFactorSealTasteGate_single_carrier_alignment_decode nameCert))

private theorem GammaZetaFactorSealTasteGate_single_carrier_alignment_injective
    {x y : GammaZetaFactorSealUp} :
    gammaZetaFactorSealToEventFlow x =
      gammaZetaFactorSealToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      gammaZetaFactorSealFromEventFlow
          (gammaZetaFactorSealToEventFlow x) =
        gammaZetaFactorSealFromEventFlow
          (gammaZetaFactorSealToEventFlow y) :=
    congrArg gammaZetaFactorSealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (GammaZetaFactorSealTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (GammaZetaFactorSealTasteGate_single_carrier_alignment_round_trip y)))

instance gammaZetaFactorSealBHistCarrier :
    BHistCarrier GammaZetaFactorSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := gammaZetaFactorSealToEventFlow
  fromEventFlow := gammaZetaFactorSealFromEventFlow

instance gammaZetaFactorSealChapterTasteGate :
    ChapterTasteGate GammaZetaFactorSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      gammaZetaFactorSealFromEventFlow
        (gammaZetaFactorSealToEventFlow x) = some x
    exact GammaZetaFactorSealTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (GammaZetaFactorSealTasteGate_single_carrier_alignment_injective heq)

def taste_gate : ChapterTasteGate GammaZetaFactorSealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  gammaZetaFactorSealChapterTasteGate

instance gammaZetaFactorSealFieldFaithful :
    FieldFaithful GammaZetaFactorSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | GammaZetaFactorSealUp.mk gammaDomain reflectedInput factorSlot
        zetaApplication transport replay provenance nameCert =>
        [gammaDomain, reflectedInput, factorSlot, zetaApplication, transport, replay,
          provenance, nameCert]
  field_faithful := by
    intro x y hfields
    cases x with
    | mk gammaDomain reflectedInput factorSlot zetaApplication transport replay
        provenance nameCert =>
        cases y with
        | mk gammaDomain' reflectedInput' factorSlot' zetaApplication' transport'
            replay' provenance' nameCert' =>
            cases hfields
            rfl

instance gammaZetaFactorSealNontrivial :
    Nontrivial GammaZetaFactorSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨GammaZetaFactorSealUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      GammaZetaFactorSealUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem GammaZetaFactorSealTasteGate_single_carrier_alignment :
    (∀ h : BHist, gammaZetaFactorSealDecodeBHist (gammaZetaFactorSealEncodeBHist h) = h) ∧
      gammaZetaFactorSealEncodeBHist BHist.Empty = ([] : List BMark) ∧
        (∀ x : GammaZetaFactorSealUp,
          gammaZetaFactorSealFromEventFlow (gammaZetaFactorSealToEventFlow x) = some x) ∧
          (∀ x y : GammaZetaFactorSealUp,
            gammaZetaFactorSealToEventFlow x = gammaZetaFactorSealToEventFlow y → x = y) ∧
            Nonempty (ChapterTasteGate GammaZetaFactorSealUp) ∧
              Nonempty (FieldFaithful GammaZetaFactorSealUp) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact GammaZetaFactorSealTasteGate_single_carrier_alignment_decode
  · constructor
    · rfl
    · constructor
      · exact GammaZetaFactorSealTasteGate_single_carrier_alignment_round_trip
      · constructor
        · intro x y heq
          exact GammaZetaFactorSealTasteGate_single_carrier_alignment_injective heq
        · constructor
          · exact ⟨gammaZetaFactorSealChapterTasteGate⟩
          · exact ⟨gammaZetaFactorSealFieldFaithful⟩

end BEDC.Derived.GammaZetaFactorSealUp
