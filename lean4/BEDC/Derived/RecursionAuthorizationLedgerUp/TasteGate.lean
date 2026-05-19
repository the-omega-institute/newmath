import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Cont
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RecursionAuthorizationLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Cont
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RecursionAuthorizationLedgerUp : Type where
  | mk :
      (signature recursor motive branches descent output transport routes provenance name :
        BHist) →
        RecursionAuthorizationLedgerUp
  deriving DecidableEq

def recursionAuthorizationLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: recursionAuthorizationLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: recursionAuthorizationLedgerEncodeBHist h

def recursionAuthorizationLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (recursionAuthorizationLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (recursionAuthorizationLedgerDecodeBHist tail)

private theorem recursionAuthorizationLedgerDecode_encode_bhist :
    ∀ h : BHist,
      recursionAuthorizationLedgerDecodeBHist
        (recursionAuthorizationLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem recursionAuthorizationLedger_mk_congr
    {signature signature' recursor recursor' motive motive' branches branches'
      descent descent' output output' transport transport' routes routes'
      provenance provenance' name name' : BHist}
    (hSignature : signature' = signature)
    (hRecursor : recursor' = recursor)
    (hMotive : motive' = motive)
    (hBranches : branches' = branches)
    (hDescent : descent' = descent)
    (hOutput : output' = output)
    (hTransport : transport' = transport)
    (hRoutes : routes' = routes)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    RecursionAuthorizationLedgerUp.mk signature' recursor' motive' branches' descent'
        output' transport' routes' provenance' name' =
      RecursionAuthorizationLedgerUp.mk signature recursor motive branches descent output
        transport routes provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hSignature
  cases hRecursor
  cases hMotive
  cases hBranches
  cases hDescent
  cases hOutput
  cases hTransport
  cases hRoutes
  cases hProvenance
  cases hName
  rfl

def recursionAuthorizationLedgerToEventFlow :
    RecursionAuthorizationLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RecursionAuthorizationLedgerUp.mk signature recursor motive branches descent output
      transport routes provenance name =>
      [[BMark.b0],
        recursionAuthorizationLedgerEncodeBHist signature,
        [BMark.b1, BMark.b0],
        recursionAuthorizationLedgerEncodeBHist recursor,
        [BMark.b1, BMark.b1, BMark.b0],
        recursionAuthorizationLedgerEncodeBHist motive,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        recursionAuthorizationLedgerEncodeBHist branches,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        recursionAuthorizationLedgerEncodeBHist descent,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        recursionAuthorizationLedgerEncodeBHist output,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        recursionAuthorizationLedgerEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        recursionAuthorizationLedgerEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        recursionAuthorizationLedgerEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        recursionAuthorizationLedgerEncodeBHist name]

def recursionAuthorizationLedgerFromEventFlow :
    EventFlow → Option RecursionAuthorizationLedgerUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | signature :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | recursor :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | motive :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | branches :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | descent :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | output :: rest11 =>
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
                                                              | routes :: rest15 =>
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
                                                                                        (RecursionAuthorizationLedgerUp.mk
                                                                                          (recursionAuthorizationLedgerDecodeBHist signature)
                                                                                          (recursionAuthorizationLedgerDecodeBHist recursor)
                                                                                          (recursionAuthorizationLedgerDecodeBHist motive)
                                                                                          (recursionAuthorizationLedgerDecodeBHist branches)
                                                                                          (recursionAuthorizationLedgerDecodeBHist descent)
                                                                                          (recursionAuthorizationLedgerDecodeBHist output)
                                                                                          (recursionAuthorizationLedgerDecodeBHist transport)
                                                                                          (recursionAuthorizationLedgerDecodeBHist routes)
                                                                                          (recursionAuthorizationLedgerDecodeBHist provenance)
                                                                                          (recursionAuthorizationLedgerDecodeBHist name))
                                                                                  | _ :: _ => none

private theorem recursionAuthorizationLedger_round_trip :
    ∀ x : RecursionAuthorizationLedgerUp,
      recursionAuthorizationLedgerFromEventFlow
        (recursionAuthorizationLedgerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk signature recursor motive branches descent output transport routes provenance name =>
      change
        some
          (RecursionAuthorizationLedgerUp.mk
            (recursionAuthorizationLedgerDecodeBHist
              (recursionAuthorizationLedgerEncodeBHist signature))
            (recursionAuthorizationLedgerDecodeBHist
              (recursionAuthorizationLedgerEncodeBHist recursor))
            (recursionAuthorizationLedgerDecodeBHist
              (recursionAuthorizationLedgerEncodeBHist motive))
            (recursionAuthorizationLedgerDecodeBHist
              (recursionAuthorizationLedgerEncodeBHist branches))
            (recursionAuthorizationLedgerDecodeBHist
              (recursionAuthorizationLedgerEncodeBHist descent))
            (recursionAuthorizationLedgerDecodeBHist
              (recursionAuthorizationLedgerEncodeBHist output))
            (recursionAuthorizationLedgerDecodeBHist
              (recursionAuthorizationLedgerEncodeBHist transport))
            (recursionAuthorizationLedgerDecodeBHist
              (recursionAuthorizationLedgerEncodeBHist routes))
            (recursionAuthorizationLedgerDecodeBHist
              (recursionAuthorizationLedgerEncodeBHist provenance))
            (recursionAuthorizationLedgerDecodeBHist
              (recursionAuthorizationLedgerEncodeBHist name))) =
          some
            (RecursionAuthorizationLedgerUp.mk signature recursor motive branches descent
              output transport routes provenance name)
      exact
        congrArg some
          (recursionAuthorizationLedger_mk_congr
            (recursionAuthorizationLedgerDecode_encode_bhist signature)
            (recursionAuthorizationLedgerDecode_encode_bhist recursor)
            (recursionAuthorizationLedgerDecode_encode_bhist motive)
            (recursionAuthorizationLedgerDecode_encode_bhist branches)
            (recursionAuthorizationLedgerDecode_encode_bhist descent)
            (recursionAuthorizationLedgerDecode_encode_bhist output)
            (recursionAuthorizationLedgerDecode_encode_bhist transport)
            (recursionAuthorizationLedgerDecode_encode_bhist routes)
            (recursionAuthorizationLedgerDecode_encode_bhist provenance)
            (recursionAuthorizationLedgerDecode_encode_bhist name))

private theorem recursionAuthorizationLedgerToEventFlow_injective
    {x y : RecursionAuthorizationLedgerUp} :
    recursionAuthorizationLedgerToEventFlow x =
      recursionAuthorizationLedgerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      recursionAuthorizationLedgerFromEventFlow
          (recursionAuthorizationLedgerToEventFlow x) =
        recursionAuthorizationLedgerFromEventFlow
          (recursionAuthorizationLedgerToEventFlow y) :=
    congrArg recursionAuthorizationLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (recursionAuthorizationLedger_round_trip x).symm
      (Eq.trans hread (recursionAuthorizationLedger_round_trip y)))

instance recursionAuthorizationLedgerBHistCarrier :
    BHistCarrier RecursionAuthorizationLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := recursionAuthorizationLedgerToEventFlow
  fromEventFlow := recursionAuthorizationLedgerFromEventFlow

instance recursionAuthorizationLedgerChapterTasteGate :
    ChapterTasteGate RecursionAuthorizationLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      recursionAuthorizationLedgerFromEventFlow
        (recursionAuthorizationLedgerToEventFlow x) = some x
    exact recursionAuthorizationLedger_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (recursionAuthorizationLedgerToEventFlow_injective heq)

theorem RecursionAuthorizationLedgerTasteGate_single_carrier_alignment :
    recursionAuthorizationLedgerEncodeBHist BHist.Empty = [] /\
      recursionAuthorizationLedgerEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] /\
      (forall h : BHist,
        recursionAuthorizationLedgerDecodeBHist
          (recursionAuthorizationLedgerEncodeBHist h) = h) /\
      (forall x : RecursionAuthorizationLedgerUp,
        recursionAuthorizationLedgerFromEventFlow
          (recursionAuthorizationLedgerToEventFlow x) = some x) /\
      (forall x y : RecursionAuthorizationLedgerUp,
        recursionAuthorizationLedgerToEventFlow x =
          recursionAuthorizationLedgerToEventFlow y -> x = y) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · rfl
  · constructor
    · rfl
    · constructor
      · exact recursionAuthorizationLedgerDecode_encode_bhist
      · constructor
        · exact recursionAuthorizationLedger_round_trip
        · intro x y heq
          exact recursionAuthorizationLedgerToEventFlow_injective heq

theorem RecursionAuthorizationLedger_signature_acceptance
    {signature signature' recursor recursor' motive motive' branches branches'
      descent descent' output output' transport transport' routes routes'
      provenance provenance' name name' route : BHist} :
    RecursionAuthorizationLedgerUp.mk signature' recursor' motive' branches' descent'
        output' transport' routes' provenance' name' =
      RecursionAuthorizationLedgerUp.mk signature recursor motive branches descent output
        transport routes provenance name →
      Cont signature recursor route →
        Cont signature' recursor' route := by
  -- BEDC touchpoint anchor: BHist Cont
  intro sameCarrier signatureRoute
  cases sameCarrier
  exact signatureRoute

end BEDC.Derived.RecursionAuthorizationLedgerUp
