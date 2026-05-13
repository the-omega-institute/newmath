import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetaCICDischargeObligationLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetaCICDischargeObligationLedgerUp : Type where
  | mk :
      (beta app lam pi subject obstruction transport route provenance name : BHist) →
      MetaCICDischargeObligationLedgerUp
  deriving DecidableEq

private def metacicDischargeObligationLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metacicDischargeObligationLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metacicDischargeObligationLedgerEncodeBHist h

private def metacicDischargeObligationLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metacicDischargeObligationLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metacicDischargeObligationLedgerDecodeBHist tail)

private theorem metacicDischargeObligationLedgerDecode_encode_bhist :
    ∀ h : BHist,
      metacicDischargeObligationLedgerDecodeBHist
          (metacicDischargeObligationLedgerEncodeBHist h) =
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

private theorem metacicDischargeObligationLedger_mk_congr
    {beta beta' app app' lam lam' pi pi' subject subject' obstruction obstruction'
      transport transport' route route' provenance provenance' name name' : BHist}
    (hBeta : beta' = beta)
    (hApp : app' = app)
    (hLam : lam' = lam)
    (hPi : pi' = pi)
    (hSubject : subject' = subject)
    (hObstruction : obstruction' = obstruction)
    (hTransport : transport' = transport)
    (hRoute : route' = route)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    MetaCICDischargeObligationLedgerUp.mk beta' app' lam' pi' subject' obstruction'
        transport' route' provenance' name' =
      MetaCICDischargeObligationLedgerUp.mk beta app lam pi subject obstruction transport
        route provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hBeta
  cases hApp
  cases hLam
  cases hPi
  cases hSubject
  cases hObstruction
  cases hTransport
  cases hRoute
  cases hProvenance
  cases hName
  rfl

private def metacicDischargeObligationLedgerToEventFlow :
    MetaCICDischargeObligationLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MetaCICDischargeObligationLedgerUp.mk beta app lam pi subject obstruction transport route
      provenance name =>
      [[BMark.b0],
        metacicDischargeObligationLedgerEncodeBHist beta,
        [BMark.b1, BMark.b0],
        metacicDischargeObligationLedgerEncodeBHist app,
        [BMark.b1, BMark.b1, BMark.b0],
        metacicDischargeObligationLedgerEncodeBHist lam,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metacicDischargeObligationLedgerEncodeBHist pi,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metacicDischargeObligationLedgerEncodeBHist subject,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metacicDischargeObligationLedgerEncodeBHist obstruction,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metacicDischargeObligationLedgerEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        metacicDischargeObligationLedgerEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        metacicDischargeObligationLedgerEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        metacicDischargeObligationLedgerEncodeBHist name]

private def metacicDischargeObligationLedgerFromEventFlow :
    EventFlow → Option MetaCICDischargeObligationLedgerUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | beta :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | app :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | lam :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | pi :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | subject :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | obstruction :: rest11 =>
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
                                                              | route :: rest15 =>
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
                                                                              | name :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] =>
                                                                                      some
                                                                                        (MetaCICDischargeObligationLedgerUp.mk
                                                                                          (metacicDischargeObligationLedgerDecodeBHist beta)
                                                                                          (metacicDischargeObligationLedgerDecodeBHist app)
                                                                                          (metacicDischargeObligationLedgerDecodeBHist lam)
                                                                                          (metacicDischargeObligationLedgerDecodeBHist pi)
                                                                                          (metacicDischargeObligationLedgerDecodeBHist subject)
                                                                                          (metacicDischargeObligationLedgerDecodeBHist obstruction)
                                                                                          (metacicDischargeObligationLedgerDecodeBHist transport)
                                                                                          (metacicDischargeObligationLedgerDecodeBHist route)
                                                                                          (metacicDischargeObligationLedgerDecodeBHist provenance)
                                                                                          (metacicDischargeObligationLedgerDecodeBHist name))
                                                                                  | _ :: _ => none

private theorem metacicDischargeObligationLedger_round_trip :
    ∀ x : MetaCICDischargeObligationLedgerUp,
      metacicDischargeObligationLedgerFromEventFlow
          (metacicDischargeObligationLedgerToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk beta app lam pi subject obstruction transport route provenance name =>
      change
        some
          (MetaCICDischargeObligationLedgerUp.mk
            (metacicDischargeObligationLedgerDecodeBHist
              (metacicDischargeObligationLedgerEncodeBHist beta))
            (metacicDischargeObligationLedgerDecodeBHist
              (metacicDischargeObligationLedgerEncodeBHist app))
            (metacicDischargeObligationLedgerDecodeBHist
              (metacicDischargeObligationLedgerEncodeBHist lam))
            (metacicDischargeObligationLedgerDecodeBHist
              (metacicDischargeObligationLedgerEncodeBHist pi))
            (metacicDischargeObligationLedgerDecodeBHist
              (metacicDischargeObligationLedgerEncodeBHist subject))
            (metacicDischargeObligationLedgerDecodeBHist
              (metacicDischargeObligationLedgerEncodeBHist obstruction))
            (metacicDischargeObligationLedgerDecodeBHist
              (metacicDischargeObligationLedgerEncodeBHist transport))
            (metacicDischargeObligationLedgerDecodeBHist
              (metacicDischargeObligationLedgerEncodeBHist route))
            (metacicDischargeObligationLedgerDecodeBHist
              (metacicDischargeObligationLedgerEncodeBHist provenance))
            (metacicDischargeObligationLedgerDecodeBHist
              (metacicDischargeObligationLedgerEncodeBHist name))) =
          some
            (MetaCICDischargeObligationLedgerUp.mk beta app lam pi subject obstruction
              transport route provenance name)
      exact
        congrArg some
          (metacicDischargeObligationLedger_mk_congr
            (metacicDischargeObligationLedgerDecode_encode_bhist beta)
            (metacicDischargeObligationLedgerDecode_encode_bhist app)
            (metacicDischargeObligationLedgerDecode_encode_bhist lam)
            (metacicDischargeObligationLedgerDecode_encode_bhist pi)
            (metacicDischargeObligationLedgerDecode_encode_bhist subject)
            (metacicDischargeObligationLedgerDecode_encode_bhist obstruction)
            (metacicDischargeObligationLedgerDecode_encode_bhist transport)
            (metacicDischargeObligationLedgerDecode_encode_bhist route)
            (metacicDischargeObligationLedgerDecode_encode_bhist provenance)
            (metacicDischargeObligationLedgerDecode_encode_bhist name))

private theorem metacicDischargeObligationLedgerToEventFlow_injective
    {x y : MetaCICDischargeObligationLedgerUp} :
    metacicDischargeObligationLedgerToEventFlow x =
        metacicDischargeObligationLedgerToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metacicDischargeObligationLedgerFromEventFlow
          (metacicDischargeObligationLedgerToEventFlow x) =
        metacicDischargeObligationLedgerFromEventFlow
          (metacicDischargeObligationLedgerToEventFlow y) :=
    congrArg metacicDischargeObligationLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (metacicDischargeObligationLedger_round_trip x).symm
      (Eq.trans hread (metacicDischargeObligationLedger_round_trip y)))

instance metacicDischargeObligationLedgerBHistCarrier :
    BHistCarrier MetaCICDischargeObligationLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metacicDischargeObligationLedgerToEventFlow
  fromEventFlow := metacicDischargeObligationLedgerFromEventFlow

instance metacicDischargeObligationLedgerChapterTasteGate :
    ChapterTasteGate MetaCICDischargeObligationLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metacicDischargeObligationLedgerFromEventFlow
          (metacicDischargeObligationLedgerToEventFlow x) =
        some x
    exact metacicDischargeObligationLedger_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metacicDischargeObligationLedgerToEventFlow_injective heq)

theorem MetaCICDischargeObligationLedgerTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      metacicDischargeObligationLedgerDecodeBHist
          (metacicDischargeObligationLedgerEncodeBHist h) =
        h) ∧
      (∀ x : MetaCICDischargeObligationLedgerUp,
        metacicDischargeObligationLedgerFromEventFlow
            (metacicDischargeObligationLedgerToEventFlow x) =
          some x) ∧
        (∀ x y : MetaCICDischargeObligationLedgerUp,
          metacicDischargeObligationLedgerToEventFlow x =
              metacicDischargeObligationLedgerToEventFlow y →
            x = y) ∧
          metacicDischargeObligationLedgerEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact metacicDischargeObligationLedgerDecode_encode_bhist
  · constructor
    · exact metacicDischargeObligationLedger_round_trip
    · constructor
      · intro x y heq
        exact metacicDischargeObligationLedgerToEventFlow_injective heq
      · rfl

end BEDC.Derived.MetaCICDischargeObligationLedgerUp
