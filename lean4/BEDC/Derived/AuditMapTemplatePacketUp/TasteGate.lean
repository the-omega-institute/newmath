import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AuditMapTemplatePacketUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AuditMapTemplatePacketUp : Type where
  | mk : (U P C O F S H R K N : BHist) → AuditMapTemplatePacketUp
  deriving DecidableEq

def auditMapTemplatePacketEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: auditMapTemplatePacketEncodeBHist h
  | BHist.e1 h => BMark.b1 :: auditMapTemplatePacketEncodeBHist h

def auditMapTemplatePacketDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (auditMapTemplatePacketDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (auditMapTemplatePacketDecodeBHist tail)

private theorem auditMapTemplatePacketDecode_encode_bhist :
    ∀ h : BHist, auditMapTemplatePacketDecodeBHist
      (auditMapTemplatePacketEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def auditMapTemplatePacketToEventFlow : AuditMapTemplatePacketUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | AuditMapTemplatePacketUp.mk U P C O F S H R K N =>
      [[BMark.b0],
        auditMapTemplatePacketEncodeBHist U,
        [BMark.b1, BMark.b0],
        auditMapTemplatePacketEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b0],
        auditMapTemplatePacketEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditMapTemplatePacketEncodeBHist O,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditMapTemplatePacketEncodeBHist F,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditMapTemplatePacketEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditMapTemplatePacketEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        auditMapTemplatePacketEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        auditMapTemplatePacketEncodeBHist K,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        auditMapTemplatePacketEncodeBHist N]

def auditMapTemplatePacketFromEventFlow : EventFlow → Option AuditMapTemplatePacketUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | U :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | P :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | C :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | O :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | F :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | S :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | H :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | R :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | K :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | N :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] =>
                                                                                      some
                                                                                        (AuditMapTemplatePacketUp.mk
                                                                                          (auditMapTemplatePacketDecodeBHist U)
                                                                                          (auditMapTemplatePacketDecodeBHist P)
                                                                                          (auditMapTemplatePacketDecodeBHist C)
                                                                                          (auditMapTemplatePacketDecodeBHist O)
                                                                                          (auditMapTemplatePacketDecodeBHist F)
                                                                                          (auditMapTemplatePacketDecodeBHist S)
                                                                                          (auditMapTemplatePacketDecodeBHist H)
                                                                                          (auditMapTemplatePacketDecodeBHist R)
                                                                                          (auditMapTemplatePacketDecodeBHist K)
                                                                                          (auditMapTemplatePacketDecodeBHist N))
                                                                                  | _ :: _ => none

private theorem auditMapTemplatePacket_round_trip :
    ∀ x : AuditMapTemplatePacketUp,
      auditMapTemplatePacketFromEventFlow (auditMapTemplatePacketToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk U P C O F S H R K N =>
      change
        some
          (AuditMapTemplatePacketUp.mk
            (auditMapTemplatePacketDecodeBHist (auditMapTemplatePacketEncodeBHist U))
            (auditMapTemplatePacketDecodeBHist (auditMapTemplatePacketEncodeBHist P))
            (auditMapTemplatePacketDecodeBHist (auditMapTemplatePacketEncodeBHist C))
            (auditMapTemplatePacketDecodeBHist (auditMapTemplatePacketEncodeBHist O))
            (auditMapTemplatePacketDecodeBHist (auditMapTemplatePacketEncodeBHist F))
            (auditMapTemplatePacketDecodeBHist (auditMapTemplatePacketEncodeBHist S))
            (auditMapTemplatePacketDecodeBHist (auditMapTemplatePacketEncodeBHist H))
            (auditMapTemplatePacketDecodeBHist (auditMapTemplatePacketEncodeBHist R))
            (auditMapTemplatePacketDecodeBHist (auditMapTemplatePacketEncodeBHist K))
            (auditMapTemplatePacketDecodeBHist (auditMapTemplatePacketEncodeBHist N))) =
          some (AuditMapTemplatePacketUp.mk U P C O F S H R K N)
      rw [auditMapTemplatePacketDecode_encode_bhist U,
        auditMapTemplatePacketDecode_encode_bhist P,
        auditMapTemplatePacketDecode_encode_bhist C,
        auditMapTemplatePacketDecode_encode_bhist O,
        auditMapTemplatePacketDecode_encode_bhist F,
        auditMapTemplatePacketDecode_encode_bhist S,
        auditMapTemplatePacketDecode_encode_bhist H,
        auditMapTemplatePacketDecode_encode_bhist R,
        auditMapTemplatePacketDecode_encode_bhist K,
        auditMapTemplatePacketDecode_encode_bhist N]

private theorem auditMapTemplatePacketToEventFlow_injective {x y : AuditMapTemplatePacketUp} :
    auditMapTemplatePacketToEventFlow x = auditMapTemplatePacketToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      auditMapTemplatePacketFromEventFlow (auditMapTemplatePacketToEventFlow x) =
        auditMapTemplatePacketFromEventFlow (auditMapTemplatePacketToEventFlow y) :=
    congrArg auditMapTemplatePacketFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (auditMapTemplatePacket_round_trip x).symm
      (Eq.trans hread (auditMapTemplatePacket_round_trip y)))

instance auditMapTemplatePacketBHistCarrier : BHistCarrier AuditMapTemplatePacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := auditMapTemplatePacketToEventFlow
  fromEventFlow := auditMapTemplatePacketFromEventFlow

instance auditMapTemplatePacketChapterTasteGate : ChapterTasteGate AuditMapTemplatePacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change auditMapTemplatePacketFromEventFlow (auditMapTemplatePacketToEventFlow x) = some x
    exact auditMapTemplatePacket_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (auditMapTemplatePacketToEventFlow_injective heq)

instance auditMapTemplatePacketFieldFaithful : FieldFaithful AuditMapTemplatePacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | AuditMapTemplatePacketUp.mk U P C O F S H R K N =>
        [U, P, C, O, F, S, H, R, K, N]
  field_faithful := by
    intro x y h
    cases x with
    | mk U1 P1 C1 O1 F1 S1 H1 R1 K1 N1 =>
        cases y with
        | mk U2 P2 C2 O2 F2 S2 H2 R2 K2 N2 =>
            cases h
            rfl

instance auditMapTemplatePacketNontrivial : Nontrivial AuditMapTemplatePacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨AuditMapTemplatePacketUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      AuditMapTemplatePacketUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate AuditMapTemplatePacketUp :=
  -- BEDC touchpoint anchor: BHist BMark
  auditMapTemplatePacketChapterTasteGate

theorem AuditMapTemplatePacketTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate AuditMapTemplatePacketUp) ∧
      (∀ x : AuditMapTemplatePacketUp,
        auditMapTemplatePacketFromEventFlow (auditMapTemplatePacketToEventFlow x) = some x) ∧
      (∀ x y : AuditMapTemplatePacketUp,
        auditMapTemplatePacketToEventFlow x = auditMapTemplatePacketToEventFlow y → x = y) ∧
      auditMapTemplatePacketEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨auditMapTemplatePacketChapterTasteGate⟩
  · constructor
    · intro x
      change auditMapTemplatePacketFromEventFlow (auditMapTemplatePacketToEventFlow x) = some x
      exact auditMapTemplatePacket_round_trip x
    · constructor
      · intro x y heq
        exact auditMapTemplatePacketToEventFlow_injective heq
      · rfl

def AuditMapTemplatePacketCarrier [AskSetup] [PackageSetup]
    (U P C O F S H R K N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory PkgSig Cont
  UnaryHistory U ∧ UnaryHistory P ∧ UnaryHistory C ∧ UnaryHistory O ∧ UnaryHistory F ∧
    UnaryHistory S ∧ UnaryHistory H ∧ UnaryHistory R ∧ UnaryHistory K ∧
      UnaryHistory N ∧ Cont C O F ∧ PkgSig bundle K pkg ∧ PkgSig bundle N pkg

theorem AuditMapTemplatePacketCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {U P C O F S H R K N useRead posRead condRead obsRead frontRead siblingRead
      nameRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuditMapTemplatePacketCarrier U P C O F S H R K N bundle pkg ->
      Cont U P useRead -> Cont P C posRead -> Cont C O condRead ->
        Cont O F obsRead -> Cont F S frontRead -> Cont S H siblingRead ->
          Cont R K nameRead -> PkgSig bundle N pkg ->
            SemanticNameCert
              (fun row : BHist => hsame row N ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row U ∨ hsame row P ∨ hsame row C ∨ hsame row O ∨
                  hsame row F ∨ hsame row S ∨ hsame row H ∨ hsame row R ∨
                    hsame row K ∨ hsame row N)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle N pkg ∧ Cont R K nameRead)
              hsame ∧
              UnaryHistory useRead ∧ UnaryHistory posRead ∧ UnaryHistory condRead ∧
                UnaryHistory obsRead ∧ UnaryHistory frontRead ∧
                  UnaryHistory siblingRead ∧ UnaryHistory nameRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame SemanticNameCert
  intro carrier useRoute posRoute condRoute obsRoute frontRoute siblingRoute nameRoute namePkg
  obtain ⟨unaryU, unaryP, unaryC, unaryO, unaryF, unaryS, unaryH, unaryR, unaryK,
    unaryN, _conditionalObstructionFrontier, _provenancePkg, _carrierNamePkg⟩ := carrier
  have useUnary : UnaryHistory useRead := unary_cont_closed unaryU unaryP useRoute
  have posUnary : UnaryHistory posRead := unary_cont_closed unaryP unaryC posRoute
  have condUnary : UnaryHistory condRead := unary_cont_closed unaryC unaryO condRoute
  have obsUnary : UnaryHistory obsRead := unary_cont_closed unaryO unaryF obsRoute
  have frontUnary : UnaryHistory frontRead := unary_cont_closed unaryF unaryS frontRoute
  have siblingUnary : UnaryHistory siblingRead :=
    unary_cont_closed unaryS unaryH siblingRoute
  have nameUnary : UnaryHistory nameRead := unary_cont_closed unaryR unaryK nameRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row N ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row U ∨ hsame row P ∨ hsame row C ∨ hsame row O ∨ hsame row F ∨
            hsame row S ∨ hsame row H ∨ hsame row R ∨ hsame row K ∨ hsame row N)
        (fun row : BHist =>
          UnaryHistory row ∧ PkgSig bundle N pkg ∧ Cont R K nameRead)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro N ⟨hsame_refl N, unaryN⟩
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
      exact ⟨source.right, namePkg, nameRoute⟩
  }
  exact
    ⟨cert, useUnary, posUnary, condUnary, obsUnary, frontUnary, siblingUnary, nameUnary⟩

theorem AuditMapTemplatePacketCarrier_conditional_row_non_discharge [AskSetup] [PackageSetup]
    {use positive conditional obstruction frontier sibling transport replay provenance
      localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuditMapTemplatePacketCarrier use positive conditional obstruction frontier sibling
        transport replay provenance localName bundle pkg ->
      UnaryHistory conditional ∧ UnaryHistory obstruction ∧ UnaryHistory frontier ∧
        Cont conditional obstruction frontier ∧ PkgSig bundle provenance pkg ∧
          PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory PkgSig
  intro carrier
  obtain ⟨_useUnary, _positiveUnary, conditionalUnary, obstructionUnary, frontierUnary,
    _siblingUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    conditionalObstructionFrontier, provenancePkg, localNamePkg⟩ := carrier
  exact
    ⟨conditionalUnary, obstructionUnary, frontierUnary, conditionalObstructionFrontier,
      provenancePkg, localNamePkg⟩

end BEDC.Derived.AuditMapTemplatePacketUp
