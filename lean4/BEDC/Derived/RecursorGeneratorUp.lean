import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Sig
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RecursorGeneratorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow

inductive RecursorGeneratorUp : Type where
  | mk :
      (signature eliminator branches audit metacic transport cont provenance name : BHist) →
      RecursorGeneratorUp
  deriving DecidableEq

def recursorGeneratorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: recursorGeneratorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: recursorGeneratorEncodeBHist h

def recursorGeneratorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (recursorGeneratorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (recursorGeneratorDecodeBHist tail)

private theorem recursorGeneratorDecode_encode_bhist :
    ∀ h : BHist, recursorGeneratorDecodeBHist (recursorGeneratorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem RecursorGeneratorTasteGate_single_carrier_alignment_mk_congr
    {signature signature' eliminator eliminator' branches branches' audit audit'
      metacic metacic' transport transport' cont cont' provenance provenance'
      name name' : BHist}
    (hSignature : signature' = signature)
    (hEliminator : eliminator' = eliminator)
    (hBranches : branches' = branches)
    (hAudit : audit' = audit)
    (hMetaCIC : metacic' = metacic)
    (hTransport : transport' = transport)
    (hCont : cont' = cont)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    RecursorGeneratorUp.mk signature' eliminator' branches' audit' metacic' transport'
        cont' provenance' name' =
      RecursorGeneratorUp.mk signature eliminator branches audit metacic transport cont
        provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hSignature
  cases hEliminator
  cases hBranches
  cases hAudit
  cases hMetaCIC
  cases hTransport
  cases hCont
  cases hProvenance
  cases hName
  rfl

def recursorGeneratorToEventFlow : RecursorGeneratorUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RecursorGeneratorUp.mk signature eliminator branches audit metacic transport cont
      provenance name =>
      [[BMark.b0],
        recursorGeneratorEncodeBHist signature,
        [BMark.b1, BMark.b0],
        recursorGeneratorEncodeBHist eliminator,
        [BMark.b1, BMark.b1, BMark.b0],
        recursorGeneratorEncodeBHist branches,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        recursorGeneratorEncodeBHist audit,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        recursorGeneratorEncodeBHist metacic,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        recursorGeneratorEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        recursorGeneratorEncodeBHist cont,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        recursorGeneratorEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        recursorGeneratorEncodeBHist name]

def recursorGeneratorFromEventFlow : EventFlow → Option RecursorGeneratorUp
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
              | eliminator :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | branches :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | audit :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | metacic :: rest9 =>
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
                                                      | cont :: rest13 =>
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
                                                                                (RecursorGeneratorUp.mk
                                                                                  (recursorGeneratorDecodeBHist
                                                                                    signature)
                                                                                  (recursorGeneratorDecodeBHist
                                                                                    eliminator)
                                                                                  (recursorGeneratorDecodeBHist
                                                                                    branches)
                                                                                  (recursorGeneratorDecodeBHist
                                                                                    audit)
                                                                                  (recursorGeneratorDecodeBHist
                                                                                    metacic)
                                                                                  (recursorGeneratorDecodeBHist
                                                                                    transport)
                                                                                  (recursorGeneratorDecodeBHist
                                                                                    cont)
                                                                                  (recursorGeneratorDecodeBHist
                                                                                    provenance)
                                                                                  (recursorGeneratorDecodeBHist
                                                                                    name))
                                                                          | _ :: _ => none

private theorem recursorGenerator_round_trip :
    ∀ x : RecursorGeneratorUp,
      recursorGeneratorFromEventFlow (recursorGeneratorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk signature eliminator branches audit metacic transport cont provenance name =>
      change
        some
          (RecursorGeneratorUp.mk
            (recursorGeneratorDecodeBHist (recursorGeneratorEncodeBHist signature))
            (recursorGeneratorDecodeBHist (recursorGeneratorEncodeBHist eliminator))
            (recursorGeneratorDecodeBHist (recursorGeneratorEncodeBHist branches))
            (recursorGeneratorDecodeBHist (recursorGeneratorEncodeBHist audit))
            (recursorGeneratorDecodeBHist (recursorGeneratorEncodeBHist metacic))
            (recursorGeneratorDecodeBHist (recursorGeneratorEncodeBHist transport))
            (recursorGeneratorDecodeBHist (recursorGeneratorEncodeBHist cont))
            (recursorGeneratorDecodeBHist (recursorGeneratorEncodeBHist provenance))
            (recursorGeneratorDecodeBHist (recursorGeneratorEncodeBHist name))) =
          some
            (RecursorGeneratorUp.mk signature eliminator branches audit metacic transport cont
              provenance name)
      exact
        congrArg some
          (RecursorGeneratorTasteGate_single_carrier_alignment_mk_congr
            (recursorGeneratorDecode_encode_bhist signature)
            (recursorGeneratorDecode_encode_bhist eliminator)
            (recursorGeneratorDecode_encode_bhist branches)
            (recursorGeneratorDecode_encode_bhist audit)
            (recursorGeneratorDecode_encode_bhist metacic)
            (recursorGeneratorDecode_encode_bhist transport)
            (recursorGeneratorDecode_encode_bhist cont)
            (recursorGeneratorDecode_encode_bhist provenance)
            (recursorGeneratorDecode_encode_bhist name))

private theorem recursorGeneratorToEventFlow_injective {x y : RecursorGeneratorUp} :
    recursorGeneratorToEventFlow x = recursorGeneratorToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      recursorGeneratorFromEventFlow (recursorGeneratorToEventFlow x) =
        recursorGeneratorFromEventFlow (recursorGeneratorToEventFlow y) :=
    congrArg recursorGeneratorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (recursorGenerator_round_trip x).symm
      (Eq.trans hread (recursorGenerator_round_trip y)))

theorem RecursorGeneratorTasteGate_single_carrier_alignment :
    (forall h : BHist, recursorGeneratorDecodeBHist (recursorGeneratorEncodeBHist h) = h) /\
      (forall x : RecursorGeneratorUp,
        recursorGeneratorFromEventFlow (recursorGeneratorToEventFlow x) = some x) /\
        (forall x y : RecursorGeneratorUp,
          recursorGeneratorToEventFlow x = recursorGeneratorToEventFlow y -> x = y) /\
          recursorGeneratorEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact recursorGeneratorDecode_encode_bhist
  · constructor
    · exact recursorGenerator_round_trip
    · constructor
      · intro x y heq
        exact recursorGeneratorToEventFlow_injective heq
      · rfl

theorem RecursorGenerator_audit_non_escape
    [AskSetup] [PackageSetup]
    {I A C P N auditRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory I ->
      UnaryHistory A ->
        UnaryHistory C ->
          UnaryHistory N ->
            Cont I A auditRead ->
              Cont auditRead C publicRead ->
                PkgSig bundle P pkg ->
                  SemanticNameCert
                    (fun row : BHist => hsame row N ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row N ∧ Cont I A auditRead ∧ Cont auditRead C publicRead)
                    (fun row : BHist => hsame row N ∧ PkgSig bundle P pkg)
                    hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro _unaryI _unaryA _unaryC unaryN auditRoute publicRoute pkgSig
  have sourceN : (fun row : BHist => hsame row N ∧ UnaryHistory row) N := by
    exact ⟨hsame_refl N, unaryN⟩
  exact {
    core := {
      carrier_inhabited := Exists.intro N sourceN
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same source
        exact ⟨hsame_trans (hsame_symm same) source.left, unary_transport source.right same⟩
    }
    pattern_sound := by
      intro _row source
      exact ⟨source.left, auditRoute, publicRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, pkgSig⟩
  }

theorem RecursorGeneratorAuthorizedOutputFactorization
    {signature eliminator branches audit metacic transport cont provenance name outputRead :
      BHist} :
    recursorGeneratorFromEventFlow
        (recursorGeneratorToEventFlow
          (RecursorGeneratorUp.mk signature eliminator branches audit metacic transport cont
            provenance name)) =
      some
        (RecursorGeneratorUp.mk signature eliminator branches audit metacic transport cont
          provenance name) ->
      Cont eliminator branches outputRead ->
        UnaryHistory eliminator ->
          UnaryHistory branches ->
            UnaryHistory outputRead ∧ Cont eliminator branches outputRead ∧
              recursorGeneratorEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark Cont UnaryHistory
  intro _carrierRoundTrip eliminatorBranchesOutputRead eliminatorUnary branchesUnary
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed eliminatorUnary branchesUnary eliminatorBranchesOutputRead
  exact ⟨outputReadUnary, eliminatorBranchesOutputRead, rfl⟩

theorem RecursorGeneratorCarrier_closed_term_handoff
    {signature eliminator branches audit metacic transport cont provenance name outputRead
      closedRead : BHist} :
    recursorGeneratorFromEventFlow
        (recursorGeneratorToEventFlow
          (RecursorGeneratorUp.mk signature eliminator branches audit metacic transport cont
            provenance name)) =
        some
          (RecursorGeneratorUp.mk signature eliminator branches audit metacic transport cont
            provenance name) →
      Cont eliminator branches outputRead →
        Cont outputRead metacic closedRead →
          UnaryHistory eliminator →
            UnaryHistory branches →
              UnaryHistory metacic →
                UnaryHistory outputRead ∧ UnaryHistory closedRead ∧
                  Cont eliminator branches outputRead ∧ Cont outputRead metacic closedRead ∧
                    recursorGeneratorEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark Cont UnaryHistory
  intro _roundTrip eliminatorBranchesOutput outputMetaCICClosed eliminatorUnary branchesUnary
    metacicUnary
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed eliminatorUnary branchesUnary eliminatorBranchesOutput
  have closedReadUnary : UnaryHistory closedRead :=
    unary_cont_closed outputReadUnary metacicUnary outputMetaCICClosed
  exact
    ⟨outputReadUnary, closedReadUnary, eliminatorBranchesOutput, outputMetaCICClosed, rfl⟩

theorem RecursorGeneratorBranchDescentExhaustion
    {signature eliminator branches audit metacic transport cont provenance name branchRead
      descentRead : BHist} :
    recursorGeneratorFromEventFlow
        (recursorGeneratorToEventFlow
          (RecursorGeneratorUp.mk signature eliminator branches audit metacic transport cont
            provenance name)) =
        some
          (RecursorGeneratorUp.mk signature eliminator branches audit metacic transport cont
            provenance name) →
      Cont eliminator branches branchRead →
        Cont branchRead metacic descentRead →
          UnaryHistory eliminator →
            UnaryHistory branches →
              UnaryHistory metacic →
                UnaryHistory branchRead ∧ UnaryHistory descentRead ∧
                  Cont eliminator branches branchRead ∧ Cont branchRead metacic descentRead ∧
                    recursorGeneratorEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark Cont UnaryHistory
  intro _roundTrip eliminatorBranchesBranch branchMetaCICDescent eliminatorUnary branchesUnary
    metacicUnary
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed eliminatorUnary branchesUnary eliminatorBranchesBranch
  have descentReadUnary : UnaryHistory descentRead :=
    unary_cont_closed branchReadUnary metacicUnary branchMetaCICDescent
  exact
    ⟨branchReadUnary, descentReadUnary, eliminatorBranchesBranch, branchMetaCICDescent, rfl⟩

theorem RecursorGeneratorDownstreamScopePackage [AskSetup] [PackageSetup]
    {I E B A M _H _C P N generatedRead closedRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory I →
      UnaryHistory E →
        UnaryHistory B →
          UnaryHistory A →
            UnaryHistory M →
              UnaryHistory N →
                Cont E B generatedRead →
                  Cont generatedRead M closedRead →
                    Cont closedRead N publicRead →
                      PkgSig bundle P pkg →
                        PkgSig bundle publicRead pkg →
                          UnaryHistory generatedRead ∧ UnaryHistory closedRead ∧
                            UnaryHistory publicRead ∧ Cont E B generatedRead ∧
                              Cont generatedRead M closedRead ∧
                                Cont closedRead N publicRead ∧ PkgSig bundle P pkg ∧
                                  PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro _unaryI unaryE unaryB _unaryA unaryM unaryN generatedRoute closedRoute publicRoute
    provenancePkg publicPkg
  have generatedUnary : UnaryHistory generatedRead :=
    unary_cont_closed unaryE unaryB generatedRoute
  have closedUnary : UnaryHistory closedRead :=
    unary_cont_closed generatedUnary unaryM closedRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed closedUnary unaryN publicRoute
  exact
    ⟨generatedUnary, closedUnary, publicUnary, generatedRoute, closedRoute, publicRoute,
      provenancePkg, publicPkg⟩

end BEDC.Derived.RecursorGeneratorUp
