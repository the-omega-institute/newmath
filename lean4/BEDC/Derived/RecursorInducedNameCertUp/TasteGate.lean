import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RecursorInducedNameCertUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RecursorInducedNameCertUp : Type where
  | mk :
      (signature motive branch output audit transport continuation provenance name : BHist) ->
        RecursorInducedNameCertUp
  deriving DecidableEq

def recursorInducedNameCertEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: recursorInducedNameCertEncodeBHist h
  | BHist.e1 h => BMark.b1 :: recursorInducedNameCertEncodeBHist h

def recursorInducedNameCertDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (recursorInducedNameCertDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (recursorInducedNameCertDecodeBHist tail)

private theorem recursorInducedNameCertDecode_encode_bhist :
    forall h : BHist,
      recursorInducedNameCertDecodeBHist (recursorInducedNameCertEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def recursorInducedNameCertToEventFlow : RecursorInducedNameCertUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RecursorInducedNameCertUp.mk signature motive branch output audit transport continuation
      provenance name =>
      [[BMark.b0],
        recursorInducedNameCertEncodeBHist signature,
        [BMark.b1, BMark.b0],
        recursorInducedNameCertEncodeBHist motive,
        [BMark.b1, BMark.b1, BMark.b0],
        recursorInducedNameCertEncodeBHist branch,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        recursorInducedNameCertEncodeBHist output,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        recursorInducedNameCertEncodeBHist audit,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        recursorInducedNameCertEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        recursorInducedNameCertEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        recursorInducedNameCertEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        recursorInducedNameCertEncodeBHist name]

def recursorInducedNameCertFields : RecursorInducedNameCertUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RecursorInducedNameCertUp.mk signature motive branch output audit transport continuation
      provenance name =>
      [signature, motive, branch, output, audit, transport, continuation, provenance, name]

def recursorInducedNameCertFromEventFlow : EventFlow -> Option RecursorInducedNameCertUp
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
              | motive :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | branch :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | output :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | audit :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | transport :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | continuation :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | provenance :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | name :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (RecursorInducedNameCertUp.mk
                                                                                  (recursorInducedNameCertDecodeBHist
                                                                                    signature)
                                                                                  (recursorInducedNameCertDecodeBHist
                                                                                    motive)
                                                                                  (recursorInducedNameCertDecodeBHist
                                                                                    branch)
                                                                                  (recursorInducedNameCertDecodeBHist
                                                                                    output)
                                                                                  (recursorInducedNameCertDecodeBHist
                                                                                    audit)
                                                                                  (recursorInducedNameCertDecodeBHist
                                                                                    transport)
                                                                                  (recursorInducedNameCertDecodeBHist
                                                                                    continuation)
                                                                                  (recursorInducedNameCertDecodeBHist
                                                                                    provenance)
                                                                                  (recursorInducedNameCertDecodeBHist
                                                                                    name))
                                                                          | _ :: _ => none

private theorem recursorInducedNameCert_round_trip :
    forall x : RecursorInducedNameCertUp,
      recursorInducedNameCertFromEventFlow (recursorInducedNameCertToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk signature motive branch output audit transport continuation provenance name =>
      change
        some
          (RecursorInducedNameCertUp.mk
            (recursorInducedNameCertDecodeBHist
              (recursorInducedNameCertEncodeBHist signature))
            (recursorInducedNameCertDecodeBHist (recursorInducedNameCertEncodeBHist motive))
            (recursorInducedNameCertDecodeBHist (recursorInducedNameCertEncodeBHist branch))
            (recursorInducedNameCertDecodeBHist (recursorInducedNameCertEncodeBHist output))
            (recursorInducedNameCertDecodeBHist (recursorInducedNameCertEncodeBHist audit))
            (recursorInducedNameCertDecodeBHist
              (recursorInducedNameCertEncodeBHist transport))
            (recursorInducedNameCertDecodeBHist
              (recursorInducedNameCertEncodeBHist continuation))
            (recursorInducedNameCertDecodeBHist
              (recursorInducedNameCertEncodeBHist provenance))
            (recursorInducedNameCertDecodeBHist (recursorInducedNameCertEncodeBHist name))) =
          some
            (RecursorInducedNameCertUp.mk signature motive branch output audit transport
              continuation provenance name)
      rw [recursorInducedNameCertDecode_encode_bhist signature,
        recursorInducedNameCertDecode_encode_bhist motive,
        recursorInducedNameCertDecode_encode_bhist branch,
        recursorInducedNameCertDecode_encode_bhist output,
        recursorInducedNameCertDecode_encode_bhist audit,
        recursorInducedNameCertDecode_encode_bhist transport,
        recursorInducedNameCertDecode_encode_bhist continuation,
        recursorInducedNameCertDecode_encode_bhist provenance,
        recursorInducedNameCertDecode_encode_bhist name]

private theorem recursorInducedNameCertToEventFlow_injective {x y : RecursorInducedNameCertUp} :
    recursorInducedNameCertToEventFlow x = recursorInducedNameCertToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      recursorInducedNameCertFromEventFlow (recursorInducedNameCertToEventFlow x) =
        recursorInducedNameCertFromEventFlow (recursorInducedNameCertToEventFlow y) :=
    congrArg recursorInducedNameCertFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (recursorInducedNameCert_round_trip x).symm
      (Eq.trans hread (recursorInducedNameCert_round_trip y)))

private theorem recursorInducedNameCert_field_faithful :
    forall x y : RecursorInducedNameCertUp,
      recursorInducedNameCertFields x = recursorInducedNameCertFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk signature motive branch output audit transport continuation provenance name =>
      cases y with
      | mk signature' motive' branch' output' audit' transport' continuation' provenance'
          name' =>
          cases hfields
          rfl

instance recursorInducedNameCertBHistCarrier : BHistCarrier RecursorInducedNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := recursorInducedNameCertToEventFlow
  fromEventFlow := recursorInducedNameCertFromEventFlow

instance recursorInducedNameCertChapterTasteGate :
    ChapterTasteGate RecursorInducedNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change recursorInducedNameCertFromEventFlow (recursorInducedNameCertToEventFlow x) = some x
    exact recursorInducedNameCert_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (recursorInducedNameCertToEventFlow_injective heq)

instance recursorInducedNameCertFieldFaithful :
    FieldFaithful RecursorInducedNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := recursorInducedNameCertFields
  field_faithful := recursorInducedNameCert_field_faithful

instance recursorInducedNameCertNontrivial :
    Nontrivial RecursorInducedNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RecursorInducedNameCertUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RecursorInducedNameCertUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem RecursorInducedNameCertTasteGate_single_carrier_alignment :
    (forall h : BHist, recursorInducedNameCertDecodeBHist
      (recursorInducedNameCertEncodeBHist h) = h) /\
      (forall x : RecursorInducedNameCertUp,
        recursorInducedNameCertFromEventFlow
          (recursorInducedNameCertToEventFlow x) = some x) /\
        (forall x y : RecursorInducedNameCertUp,
          recursorInducedNameCertToEventFlow x =
            recursorInducedNameCertToEventFlow y -> x = y) /\
          recursorInducedNameCertEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  have hdecode :
      forall h : BHist,
        recursorInducedNameCertDecodeBHist (recursorInducedNameCertEncodeBHist h) = h := by
    intro h
    induction h with
    | Empty =>
        rfl
    | e0 h ih =>
        exact congrArg BHist.e0 ih
    | e1 h ih =>
        exact congrArg BHist.e1 ih
  have hround :
      forall x : RecursorInducedNameCertUp,
        recursorInducedNameCertFromEventFlow (recursorInducedNameCertToEventFlow x) = some x := by
    intro x
    cases x with
    | mk signature motive branch output audit transport continuation provenance name =>
        change
          some
            (RecursorInducedNameCertUp.mk
              (recursorInducedNameCertDecodeBHist
                (recursorInducedNameCertEncodeBHist signature))
              (recursorInducedNameCertDecodeBHist
                (recursorInducedNameCertEncodeBHist motive))
              (recursorInducedNameCertDecodeBHist
                (recursorInducedNameCertEncodeBHist branch))
              (recursorInducedNameCertDecodeBHist
                (recursorInducedNameCertEncodeBHist output))
              (recursorInducedNameCertDecodeBHist
                (recursorInducedNameCertEncodeBHist audit))
              (recursorInducedNameCertDecodeBHist
                (recursorInducedNameCertEncodeBHist transport))
              (recursorInducedNameCertDecodeBHist
                (recursorInducedNameCertEncodeBHist continuation))
              (recursorInducedNameCertDecodeBHist
                (recursorInducedNameCertEncodeBHist provenance))
              (recursorInducedNameCertDecodeBHist
                (recursorInducedNameCertEncodeBHist name))) =
            some
              (RecursorInducedNameCertUp.mk signature motive branch output audit transport
                continuation provenance name)
        rw [hdecode signature, hdecode motive, hdecode branch, hdecode output, hdecode audit,
          hdecode transport, hdecode continuation, hdecode provenance, hdecode name]
  have hinj :
      forall x y : RecursorInducedNameCertUp,
        recursorInducedNameCertToEventFlow x =
          recursorInducedNameCertToEventFlow y -> x = y := by
    intro x y heq
    have hread :
        recursorInducedNameCertFromEventFlow (recursorInducedNameCertToEventFlow x) =
          recursorInducedNameCertFromEventFlow (recursorInducedNameCertToEventFlow y) :=
      congrArg recursorInducedNameCertFromEventFlow heq
    exact Option.some.inj (Eq.trans (hround x).symm (Eq.trans hread (hround y)))
  exact And.intro hdecode (And.intro hround (And.intro hinj rfl))

theorem RecursorInducedNameCertAuditBoundary_replay_route
    {signature motive branch output audit transport continuation provenance name
      signatureMotive branchRead outputRead auditRead : BHist} :
    UnaryHistory signature →
      UnaryHistory motive →
        UnaryHistory branch →
          UnaryHistory output →
            UnaryHistory audit →
              Cont signature motive signatureMotive →
                Cont signatureMotive branch branchRead →
                  Cont branchRead output outputRead →
                    Cont outputRead audit auditRead →
                      recursorInducedNameCertFromEventFlow
                          (recursorInducedNameCertToEventFlow
                            (RecursorInducedNameCertUp.mk signature motive branch output audit
                              transport continuation provenance name)) =
                        some
                          (RecursorInducedNameCertUp.mk signature motive branch output audit
                            transport continuation provenance name) →
                        UnaryHistory signatureMotive ∧
                          UnaryHistory branchRead ∧
                            UnaryHistory outputRead ∧
                              UnaryHistory auditRead ∧
                                hsame
                                  (recursorInducedNameCertDecodeBHist
                                    (recursorInducedNameCertEncodeBHist audit))
                                  audit := by
  -- BEDC touchpoint anchor: BHist hsame Cont ChapterTasteGate
  intro signatureUnary motiveUnary branchUnary outputUnary auditUnary signatureRoute branchRoute
    outputRoute auditRoute _readback
  have signatureMotiveUnary : UnaryHistory signatureMotive :=
    unary_cont_closed signatureUnary motiveUnary signatureRoute
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed signatureMotiveUnary branchUnary branchRoute
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed branchReadUnary outputUnary outputRoute
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed outputReadUnary auditUnary auditRoute
  exact
    ⟨signatureMotiveUnary,
      branchReadUnary,
      outputReadUnary,
      auditReadUnary,
      recursorInducedNameCertDecode_encode_bhist audit⟩

theorem RecursorInducedNameCertNameCertObligationSurface [AskSetup] [PackageSetup]
    {signature motive branch output audit transport continuation provenance name signatureMotive
      branchRead outputRead auditRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory signature -> UnaryHistory motive -> UnaryHistory branch ->
      UnaryHistory output -> UnaryHistory audit -> UnaryHistory name ->
        Cont signature motive signatureMotive ->
          Cont signatureMotive branch branchRead ->
            Cont branchRead output outputRead ->
              Cont outputRead audit auditRead ->
                Cont auditRead name namedRead ->
                  PkgSig bundle provenance pkg ->
                    SemanticNameCert
                        (fun row : BHist => hsame row namedRead /\ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row signature \/ hsame row motive \/ hsame row branch \/
                            hsame row output \/ hsame row audit \/ hsame row transport \/
                              hsame row continuation \/ hsame row provenance \/
                                hsame row name \/ hsame row namedRead)
                        (fun row : BHist =>
                          UnaryHistory row /\ Cont signature motive signatureMotive /\
                            Cont signatureMotive branch branchRead /\
                              Cont branchRead output outputRead /\
                                Cont outputRead audit auditRead /\
                                  Cont auditRead name namedRead /\
                                    PkgSig bundle provenance pkg)
                        hsame /\ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory FieldFaithful
  intro signatureUnary motiveUnary branchUnary outputUnary auditUnary nameUnary signatureRoute
    branchRoute outputRoute auditRoute namedRoute pkgProvenance
  have signatureMotiveUnary : UnaryHistory signatureMotive :=
    unary_cont_closed signatureUnary motiveUnary signatureRoute
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed signatureMotiveUnary branchUnary branchRoute
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed branchReadUnary outputUnary outputRoute
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed outputReadUnary auditUnary auditRoute
  have namedReadUnary : UnaryHistory namedRead :=
    unary_cont_closed auditReadUnary nameUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead /\ UnaryHistory row)
          (fun row : BHist =>
            hsame row signature \/ hsame row motive \/ hsame row branch \/
              hsame row output \/ hsame row audit \/ hsame row transport \/
                hsame row continuation \/ hsame row provenance \/ hsame row name \/
                  hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row /\ Cont signature motive signatureMotive /\
              Cont signatureMotive branch branchRead /\ Cont branchRead output outputRead /\
                Cont outputRead audit auditRead /\ Cont auditRead name namedRead /\
                  PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedReadUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, signatureRoute, branchRoute, outputRoute, auditRoute, namedRoute,
          pkgProvenance⟩
  }
  exact ⟨cert, namedReadUnary⟩

theorem RecursorInducedNameCert_non_escape_boundary [AskSetup] [PackageSetup]
    {signature motive branch output audit transport continuation provenance name signatureMotive
      branchRead outputRead auditRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory signature -> UnaryHistory motive -> UnaryHistory branch ->
      UnaryHistory output -> UnaryHistory audit -> UnaryHistory name ->
        Cont signature motive signatureMotive ->
          Cont signatureMotive branch branchRead ->
            Cont branchRead output outputRead ->
              Cont outputRead audit auditRead ->
                Cont auditRead name namedRead ->
                  PkgSig bundle provenance pkg ->
                    SemanticNameCert
                      (fun row : BHist => hsame row namedRead /\ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row signature \/ hsame row motive \/ hsame row branch \/
                          hsame row output \/ hsame row audit \/ hsame row transport \/
                            hsame row continuation \/ hsame row provenance \/
                              hsame row name \/ hsame row namedRead)
                      (fun row : BHist =>
                        hsame row namedRead /\ Cont auditRead name namedRead /\
                          PkgSig bundle provenance pkg)
                      hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro signatureUnary motiveUnary branchUnary outputUnary auditUnary nameUnary signatureRoute
    branchRoute outputRoute auditRoute namedRoute pkgProvenance
  have signatureMotiveUnary : UnaryHistory signatureMotive :=
    unary_cont_closed signatureUnary motiveUnary signatureRoute
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed signatureMotiveUnary branchUnary branchRoute
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed branchReadUnary outputUnary outputRoute
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed outputReadUnary auditUnary auditRoute
  have namedReadUnary : UnaryHistory namedRead :=
    unary_cont_closed auditReadUnary nameUnary namedRoute
  exact {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedReadUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, namedRoute, pkgProvenance⟩
  }

end BEDC.Derived.RecursorInducedNameCertUp
