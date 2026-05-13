import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ClosurePreservationAuditSealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ClosurePreservationAuditSealUp : Type where
  | mk :
      (audit shift varSubst subst beta betaStar gap transport routes provenance name :
        BHist) →
      ClosurePreservationAuditSealUp
  deriving DecidableEq

def closurePreservationAuditSealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: closurePreservationAuditSealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: closurePreservationAuditSealEncodeBHist h

def closurePreservationAuditSealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (closurePreservationAuditSealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (closurePreservationAuditSealDecodeBHist tail)

private theorem closurePreservationAuditSeal_decode_encode_bhist :
    ∀ h : BHist,
      closurePreservationAuditSealDecodeBHist
        (closurePreservationAuditSealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def closurePreservationAuditSealToEventFlow :
    ClosurePreservationAuditSealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ClosurePreservationAuditSealUp.mk audit shift varSubst subst beta betaStar gap
      transport routes provenance name =>
      [[BMark.b0],
        closurePreservationAuditSealEncodeBHist audit,
        [BMark.b1, BMark.b0],
        closurePreservationAuditSealEncodeBHist shift,
        [BMark.b1, BMark.b1, BMark.b0],
        closurePreservationAuditSealEncodeBHist varSubst,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closurePreservationAuditSealEncodeBHist subst,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closurePreservationAuditSealEncodeBHist beta,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closurePreservationAuditSealEncodeBHist betaStar,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closurePreservationAuditSealEncodeBHist gap,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        closurePreservationAuditSealEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        closurePreservationAuditSealEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        closurePreservationAuditSealEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closurePreservationAuditSealEncodeBHist name]

def closurePreservationAuditSealFromEventFlow :
    EventFlow → Option ClosurePreservationAuditSealUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | audit :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | shift :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | varSubst :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | subst :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | beta :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | betaStar :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | gap :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | transport ::
                                                                  rest15 =>
                                                                  match rest15
                                                                    with
                                                                  | [] => none
                                                                  | _tag8 ::
                                                                      rest16 =>
                                                                      match rest16
                                                                        with
                                                                      | [] =>
                                                                          none
                                                                      | routes ::
                                                                          rest17 =>
                                                                          match rest17
                                                                            with
                                                                          | [] =>
                                                                              none
                                                                          | _tag9 ::
                                                                              rest18 =>
                                                                              match rest18
                                                                                with
                                                                              | [] =>
                                                                                  none
                                                                              | provenance ::
                                                                                  rest19 =>
                                                                                  match rest19
                                                                                    with
                                                                                  | [] =>
                                                                                      none
                                                                                  | _tag10 ::
                                                                                      rest20 =>
                                                                                      match rest20
                                                                                        with
                                                                                      | [] =>
                                                                                          none
                                                                                      | name ::
                                                                                          rest21 =>
                                                                                          match rest21
                                                                                            with
                                                                                          | [] =>
                                                                                              some
                                                                                                (ClosurePreservationAuditSealUp.mk
                                                                                                  (closurePreservationAuditSealDecodeBHist
                                                                                                    audit)
                                                                                                  (closurePreservationAuditSealDecodeBHist
                                                                                                    shift)
                                                                                                  (closurePreservationAuditSealDecodeBHist
                                                                                                    varSubst)
                                                                                                  (closurePreservationAuditSealDecodeBHist
                                                                                                    subst)
                                                                                                  (closurePreservationAuditSealDecodeBHist
                                                                                                    beta)
                                                                                                  (closurePreservationAuditSealDecodeBHist
                                                                                                    betaStar)
                                                                                                  (closurePreservationAuditSealDecodeBHist
                                                                                                    gap)
                                                                                                  (closurePreservationAuditSealDecodeBHist
                                                                                                    transport)
                                                                                                  (closurePreservationAuditSealDecodeBHist
                                                                                                    routes)
                                                                                                  (closurePreservationAuditSealDecodeBHist
                                                                                                    provenance)
                                                                                                  (closurePreservationAuditSealDecodeBHist
                                                                                                    name))
                                                                                          | _ :: _ =>
                                                                                              none

private theorem closurePreservationAuditSeal_round_trip :
    ∀ x : ClosurePreservationAuditSealUp,
      closurePreservationAuditSealFromEventFlow
        (closurePreservationAuditSealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk audit shift varSubst subst beta betaStar gap transport routes provenance name =>
      change
        some
          (ClosurePreservationAuditSealUp.mk
            (closurePreservationAuditSealDecodeBHist
              (closurePreservationAuditSealEncodeBHist audit))
            (closurePreservationAuditSealDecodeBHist
              (closurePreservationAuditSealEncodeBHist shift))
            (closurePreservationAuditSealDecodeBHist
              (closurePreservationAuditSealEncodeBHist varSubst))
            (closurePreservationAuditSealDecodeBHist
              (closurePreservationAuditSealEncodeBHist subst))
            (closurePreservationAuditSealDecodeBHist
              (closurePreservationAuditSealEncodeBHist beta))
            (closurePreservationAuditSealDecodeBHist
              (closurePreservationAuditSealEncodeBHist betaStar))
            (closurePreservationAuditSealDecodeBHist
              (closurePreservationAuditSealEncodeBHist gap))
            (closurePreservationAuditSealDecodeBHist
              (closurePreservationAuditSealEncodeBHist transport))
            (closurePreservationAuditSealDecodeBHist
              (closurePreservationAuditSealEncodeBHist routes))
            (closurePreservationAuditSealDecodeBHist
              (closurePreservationAuditSealEncodeBHist provenance))
            (closurePreservationAuditSealDecodeBHist
              (closurePreservationAuditSealEncodeBHist name))) =
          some
            (ClosurePreservationAuditSealUp.mk audit shift varSubst subst beta
              betaStar gap transport routes provenance name)
      rw [closurePreservationAuditSeal_decode_encode_bhist audit,
        closurePreservationAuditSeal_decode_encode_bhist shift,
        closurePreservationAuditSeal_decode_encode_bhist varSubst,
        closurePreservationAuditSeal_decode_encode_bhist subst,
        closurePreservationAuditSeal_decode_encode_bhist beta,
        closurePreservationAuditSeal_decode_encode_bhist betaStar,
        closurePreservationAuditSeal_decode_encode_bhist gap,
        closurePreservationAuditSeal_decode_encode_bhist transport,
        closurePreservationAuditSeal_decode_encode_bhist routes,
        closurePreservationAuditSeal_decode_encode_bhist provenance,
        closurePreservationAuditSeal_decode_encode_bhist name]

private theorem closurePreservationAuditSealToEventFlow_injective
    {x y : ClosurePreservationAuditSealUp} :
    closurePreservationAuditSealToEventFlow x =
      closurePreservationAuditSealToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      closurePreservationAuditSealFromEventFlow
          (closurePreservationAuditSealToEventFlow x) =
        closurePreservationAuditSealFromEventFlow
          (closurePreservationAuditSealToEventFlow y) :=
    congrArg closurePreservationAuditSealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (closurePreservationAuditSeal_round_trip x).symm
      (Eq.trans hread (closurePreservationAuditSeal_round_trip y)))

instance closurePreservationAuditSealBHistCarrier :
    BHistCarrier ClosurePreservationAuditSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := closurePreservationAuditSealToEventFlow
  fromEventFlow := closurePreservationAuditSealFromEventFlow

instance closurePreservationAuditSealChapterTasteGate :
    ChapterTasteGate ClosurePreservationAuditSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      closurePreservationAuditSealFromEventFlow
        (closurePreservationAuditSealToEventFlow x) = some x
    exact closurePreservationAuditSeal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (closurePreservationAuditSealToEventFlow_injective heq)

instance closurePreservationAuditSealFieldFaithful :
    FieldFaithful ClosurePreservationAuditSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | ClosurePreservationAuditSealUp.mk audit shift varSubst subst beta betaStar gap
        transport routes provenance name =>
        [audit, shift, varSubst, subst, beta, betaStar, gap, transport, routes,
          provenance, name]
  field_faithful := by
    intro x y h
    cases x with
    | mk audit1 shift1 varSubst1 subst1 beta1 betaStar1 gap1 transport1 routes1
        provenance1 name1 =>
        cases y with
        | mk audit2 shift2 varSubst2 subst2 beta2 betaStar2 gap2 transport2 routes2
            provenance2 name2 =>
            injection h with hAudit t1
            injection t1 with hShift t2
            injection t2 with hVarSubst t3
            injection t3 with hSubst t4
            injection t4 with hBeta t5
            injection t5 with hBetaStar t6
            injection t6 with hGap t7
            injection t7 with hTransport t8
            injection t8 with hRoutes t9
            injection t9 with hProvenance t10
            injection t10 with hName _
            cases hAudit
            cases hShift
            cases hVarSubst
            cases hSubst
            cases hBeta
            cases hBetaStar
            cases hGap
            cases hTransport
            cases hRoutes
            cases hProvenance
            cases hName
            rfl

theorem ClosurePreservationAuditSealTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      closurePreservationAuditSealDecodeBHist
        (closurePreservationAuditSealEncodeBHist h) = h) ∧
      (∀ x : ClosurePreservationAuditSealUp,
        closurePreservationAuditSealFromEventFlow
          (closurePreservationAuditSealToEventFlow x) = some x) ∧
        (∀ x y : ClosurePreservationAuditSealUp,
          closurePreservationAuditSealToEventFlow x =
            closurePreservationAuditSealToEventFlow y → x = y) ∧
          closurePreservationAuditSealEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact closurePreservationAuditSeal_decode_encode_bhist
  · constructor
    · exact closurePreservationAuditSeal_round_trip
    · constructor
      · intro x y heq
        exact closurePreservationAuditSealToEventFlow_injective heq
      · rfl

end BEDC.Derived.ClosurePreservationAuditSealUp
