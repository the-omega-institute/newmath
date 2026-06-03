import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AuditSystemUp

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

inductive AuditSystemUp : Type where
  | mk : (C P F R E L H K Q N : BHist) → AuditSystemUp
  deriving DecidableEq

def auditSystemEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: auditSystemEncodeBHist h
  | BHist.e1 h => BMark.b1 :: auditSystemEncodeBHist h

def auditSystemDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (auditSystemDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (auditSystemDecodeBHist tail)

private theorem auditSystemDecode_encode_bhist :
    ∀ h : BHist, auditSystemDecodeBHist (auditSystemEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def auditSystemToEventFlow : AuditSystemUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | AuditSystemUp.mk C P F R E L H K Q N =>
      [auditSystemEncodeBHist C, auditSystemEncodeBHist P, auditSystemEncodeBHist F,
        auditSystemEncodeBHist R, auditSystemEncodeBHist E, auditSystemEncodeBHist L,
        auditSystemEncodeBHist H, auditSystemEncodeBHist K, auditSystemEncodeBHist Q,
        auditSystemEncodeBHist N]

def auditSystemFromEventFlow : EventFlow → Option AuditSystemUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | C :: rest0 =>
      match rest0 with
      | [] => none
      | P :: rest1 =>
          match rest1 with
          | [] => none
          | F :: rest2 =>
              match rest2 with
              | [] => none
              | R :: rest3 =>
                  match rest3 with
                  | [] => none
                  | E :: rest4 =>
                      match rest4 with
                      | [] => none
                      | L :: rest5 =>
                          match rest5 with
                          | [] => none
                          | H :: rest6 =>
                              match rest6 with
                              | [] => none
                              | K :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | Q :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | N :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (AuditSystemUp.mk
                                                  (auditSystemDecodeBHist C)
                                                  (auditSystemDecodeBHist P)
                                                  (auditSystemDecodeBHist F)
                                                  (auditSystemDecodeBHist R)
                                                  (auditSystemDecodeBHist E)
                                                  (auditSystemDecodeBHist L)
                                                  (auditSystemDecodeBHist H)
                                                  (auditSystemDecodeBHist K)
                                                  (auditSystemDecodeBHist Q)
                                                  (auditSystemDecodeBHist N))
                                          | _ :: _ => none

private theorem auditSystem_round_trip :
    ∀ x : AuditSystemUp, auditSystemFromEventFlow (auditSystemToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk C P F R E L H K Q N =>
      change
        some
            (AuditSystemUp.mk
              (auditSystemDecodeBHist (auditSystemEncodeBHist C))
              (auditSystemDecodeBHist (auditSystemEncodeBHist P))
              (auditSystemDecodeBHist (auditSystemEncodeBHist F))
              (auditSystemDecodeBHist (auditSystemEncodeBHist R))
              (auditSystemDecodeBHist (auditSystemEncodeBHist E))
              (auditSystemDecodeBHist (auditSystemEncodeBHist L))
              (auditSystemDecodeBHist (auditSystemEncodeBHist H))
              (auditSystemDecodeBHist (auditSystemEncodeBHist K))
              (auditSystemDecodeBHist (auditSystemEncodeBHist Q))
              (auditSystemDecodeBHist (auditSystemEncodeBHist N))) =
          some (AuditSystemUp.mk C P F R E L H K Q N)
      rw [auditSystemDecode_encode_bhist C, auditSystemDecode_encode_bhist P,
        auditSystemDecode_encode_bhist F, auditSystemDecode_encode_bhist R,
        auditSystemDecode_encode_bhist E, auditSystemDecode_encode_bhist L,
        auditSystemDecode_encode_bhist H, auditSystemDecode_encode_bhist K,
        auditSystemDecode_encode_bhist Q, auditSystemDecode_encode_bhist N]

private theorem auditSystemToEventFlow_injective {x y : AuditSystemUp} :
    auditSystemToEventFlow x = auditSystemToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      auditSystemFromEventFlow (auditSystemToEventFlow x) =
        auditSystemFromEventFlow (auditSystemToEventFlow y) :=
    congrArg auditSystemFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (auditSystem_round_trip x).symm
      (Eq.trans hread (auditSystem_round_trip y)))

instance auditSystemBHistCarrier : BHistCarrier AuditSystemUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := auditSystemToEventFlow
  fromEventFlow := auditSystemFromEventFlow

instance auditSystemChapterTasteGate : ChapterTasteGate AuditSystemUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change auditSystemFromEventFlow (auditSystemToEventFlow x) = some x
    exact auditSystem_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (auditSystemToEventFlow_injective heq)

instance auditSystemFieldFaithful : FieldFaithful AuditSystemUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | AuditSystemUp.mk C P F R E L H K Q N => [C, P, F, R, E, L, H, K, Q, N]
  field_faithful := by
    intro x y h
    cases x with
    | mk C1 P1 F1 R1 E1 L1 H1 K1 Q1 N1 =>
        cases y with
        | mk C2 P2 F2 R2 E2 L2 H2 K2 Q2 N2 =>
            cases h
            rfl

instance auditSystemNontrivial : Nontrivial AuditSystemUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨AuditSystemUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      AuditSystemUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate AuditSystemUp :=
  -- BEDC touchpoint anchor: BHist BMark
  auditSystemChapterTasteGate

theorem AuditSystemTasteGate_single_carrier_alignment :
    (∀ h : BHist, auditSystemDecodeBHist (auditSystemEncodeBHist h) = h) ∧
      (∀ x : AuditSystemUp, auditSystemFromEventFlow (auditSystemToEventFlow x) = some x) ∧
        (∀ x y : AuditSystemUp,
          auditSystemToEventFlow x = auditSystemToEventFlow y → x = y) ∧
          auditSystemEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact auditSystemDecode_encode_bhist
  · constructor
    · intro x
      change auditSystemFromEventFlow (auditSystemToEventFlow x) = some x
      exact auditSystem_round_trip x
    · constructor
      · intro x y heq
        exact auditSystemToEventFlow_injective heq
      · rfl

def AuditSystemCarrier [AskSetup] [PackageSetup]
    (C P F R E L H K Q N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory PkgSig
  UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory F ∧ UnaryHistory R ∧
    UnaryHistory E ∧ UnaryHistory L ∧ UnaryHistory H ∧ UnaryHistory K ∧
      UnaryHistory Q ∧ UnaryHistory N ∧ Cont F R K ∧ Cont C P E ∧
        Cont E L H ∧ PkgSig bundle Q pkg

theorem AuditSystemCarrier_export_refusal_conflict [AskSetup] [PackageSetup]
    {C P F R E L H K Q N conflict : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuditSystemCarrier C P F R E L H K Q N bundle pkg →
      Cont F R conflict →
        PkgSig bundle conflict pkg →
          UnaryHistory F ∧ UnaryHistory R ∧ UnaryHistory E ∧ UnaryHistory conflict ∧
            Cont F R conflict ∧ PkgSig bundle Q pkg ∧ PkgSig bundle conflict pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory PkgSig
  intro carrier refusalRoute conflictPkg
  obtain ⟨_cUnary, _pUnary, fUnary, rUnary, eUnary, _lUnary, _hUnary, _kUnary,
    _qUnary, _nUnary, _failureRefusal, _claimPositive, _exportLedger, qPkg⟩ := carrier
  have conflictUnary : UnaryHistory conflict :=
    unary_cont_closed fUnary rUnary refusalRoute
  exact ⟨fUnary, rUnary, eUnary, conflictUnary, refusalRoute, qPkg, conflictPkg⟩

theorem AuditSystemLedgerClosure [AskSetup] [PackageSetup]
    {C P F R E L H K Q N claimRead ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont C E claimRead →
      Cont claimRead L ledgerRead →
        PkgSig bundle Q pkg →
          PkgSig bundle N pkg →
            UnaryHistory C →
              UnaryHistory E →
                UnaryHistory L →
                  SemanticNameCert
                      (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row C ∨ hsame row P ∨ hsame row F ∨ hsame row R ∨
                          hsame row E ∨ hsame row L ∨ hsame row H ∨ hsame row K ∨
                            hsame row Q ∨ hsame row N ∨ hsame row claimRead ∨
                              hsame row ledgerRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont C E claimRead ∧
                          Cont claimRead L ledgerRead ∧ PkgSig bundle Q pkg ∧
                            PkgSig bundle N pkg)
                      hsame ∧
                    UnaryHistory claimRead ∧ UnaryHistory ledgerRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory SemanticNameCert hsame
  intro claimRoute ledgerRoute qPkg nPkg cUnary eUnary lUnary
  have claimUnary : UnaryHistory claimRead :=
    unary_cont_closed cUnary eUnary claimRoute
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed claimUnary lUnary ledgerRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row C ∨ hsame row P ∨ hsame row F ∨ hsame row R ∨
              hsame row E ∨ hsame row L ∨ hsame row H ∨ hsame row K ∨
                hsame row Q ∨ hsame row N ∨ hsame row claimRead ∨
                  hsame row ledgerRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont C E claimRead ∧ Cont claimRead L ledgerRead ∧
              PkgSig bundle Q pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro ledgerRead ⟨hsame_refl ledgerRead, ledgerUnary⟩
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
        exact
          ⟨hsame_trans (hsame_symm same) source.left,
            unary_transport source.right same⟩
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
                        (Or.inr
                          (Or.inr
                            (Or.inr source.left))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, claimRoute, ledgerRoute, qPkg, nPkg⟩
  }
  exact ⟨cert, claimUnary, ledgerUnary⟩

theorem AuditSystemCarrier_namecert_surface [AskSetup] [PackageSetup]
    {C P F R E L H K Q N exportRead closureRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuditSystemCarrier C P F R E L H K Q N bundle pkg ->
      Cont C P exportRead ->
        Cont exportRead L closureRead ->
          PkgSig bundle Q pkg ->
            SemanticNameCert
              (fun row : BHist => hsame row closureRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row C ∨ hsame row P ∨ hsame row F ∨ hsame row R ∨
                  hsame row E ∨ hsame row L ∨ hsame row H ∨ hsame row K ∨
                    hsame row Q ∨ hsame row N ∨ hsame row exportRead ∨
                      hsame row closureRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont C P exportRead ∧ Cont exportRead L closureRead ∧
                  PkgSig bundle Q pkg)
              hsame ∧ UnaryHistory exportRead ∧ UnaryHistory closureRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame
  intro carrier exportRoute closureRoute qPkg
  obtain ⟨cUnary, pUnary, _fUnary, _rUnary, _eUnary, lUnary, _hUnary, _kUnary,
    _qUnary, _nUnary, _failureRoute, _claimRoute, _ledgerRoute, _carrierPkg⟩ := carrier
  have exportUnary : UnaryHistory exportRead :=
    unary_cont_closed cUnary pUnary exportRoute
  have closureUnary : UnaryHistory closureRead :=
    unary_cont_closed exportUnary lUnary closureRoute
  have sourceClosure :
      (fun row : BHist => hsame row closureRead ∧ UnaryHistory row) closureRead :=
    ⟨hsame_refl closureRead, closureUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row closureRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row C ∨ hsame row P ∨ hsame row F ∨ hsame row R ∨
            hsame row E ∨ hsame row L ∨ hsame row H ∨ hsame row K ∨
              hsame row Q ∨ hsame row N ∨ hsame row exportRead ∨ hsame row closureRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont C P exportRead ∧ Cont exportRead L closureRead ∧
            PkgSig bundle Q pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro closureRead sourceClosure
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
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr source.left))))))))))
      ledger_sound := by
        intro _row source
        exact ⟨source.right, exportRoute, closureRoute, qPkg⟩
    }
  exact ⟨cert, exportUnary, closureUnary⟩

theorem AuditSystemCarrier_certificate_conflict_determinacy [AskSetup] [PackageSetup]
    {C P F R E L H K Q N blockedRead exportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuditSystemCarrier C P F R E L H K Q N bundle pkg →
      Cont F R blockedRead →
        Cont E L exportRead →
          PkgSig bundle exportRead pkg →
            SemanticNameCert
                (fun row : BHist =>
                  (hsame row blockedRead ∨ hsame row exportRead) ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row F ∨ hsame row R ∨ hsame row blockedRead ∨ hsame row E ∨
                    hsame row L ∨ hsame row exportRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle exportRead pkg ∧ PkgSig bundle Q pkg)
                hsame ∧
              UnaryHistory blockedRead ∧ UnaryHistory exportRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame
  intro carrier blockedRoute exportRoute exportPkg
  obtain ⟨_cUnary, _pUnary, fUnary, rUnary, eUnary, lUnary, _hUnary, _kUnary,
    _qUnary, _nUnary, _failureRoute, _claimRoute, _ledgerRoute, qPkg⟩ := carrier
  have blockedUnary : UnaryHistory blockedRead :=
    unary_cont_closed fUnary rUnary blockedRoute
  have exportUnary : UnaryHistory exportRead :=
    unary_cont_closed eUnary lUnary exportRoute
  have sourceExport :
      (fun row : BHist =>
        (hsame row blockedRead ∨ hsame row exportRead) ∧ UnaryHistory row) exportRead := by
    exact ⟨Or.inr (hsame_refl exportRead), exportUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row blockedRead ∨ hsame row exportRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row F ∨ hsame row R ∨ hsame row blockedRead ∨ hsame row E ∨
              hsame row L ∨ hsame row exportRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle exportRead pkg ∧ PkgSig bundle Q pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro exportRead sourceExport
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
        constructor
        · cases source.left with
          | inl sameBlocked =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameBlocked)
          | inr sameExport =>
              exact Or.inr (hsame_trans (hsame_symm sameRows) sameExport)
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameBlocked =>
          exact Or.inr (Or.inr (Or.inl sameBlocked))
      | inr sameExport =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sameExport))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, exportPkg, qPkg⟩
  }
  exact ⟨cert, blockedUnary, exportUnary⟩

theorem AuditSystemIndependenceWitness [AskSetup] [PackageSetup]
    {claim positive failure refusal «export» audit ledger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory claim ->
      UnaryHistory positive ->
        UnaryHistory failure ->
          UnaryHistory refusal ->
            UnaryHistory «export» ->
              Cont claim positive audit ->
                Cont failure refusal «export» ->
                  Cont audit «export» ledger ->
                    PkgSig bundle ledger pkg ->
                      SemanticNameCert
                          (fun row : BHist => hsame row ledger ∧ UnaryHistory row)
                          (fun row : BHist =>
                              hsame row claim ∨ hsame row positive ∨ hsame row failure ∨
                                hsame row refusal ∨ hsame row «export» ∨ hsame row audit ∨
                                hsame row ledger)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont claim positive audit ∧
                              Cont failure refusal «export» ∧ Cont audit «export» ledger ∧
                                PkgSig bundle ledger pkg)
                          hsame ∧
                        UnaryHistory audit ∧ UnaryHistory «export» ∧ UnaryHistory ledger := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig SemanticNameCert UnaryHistory hsame
  intro claimUnary positiveUnary failureUnary refusalUnary exportUnary auditRoute exportRoute
    ledgerRoute ledgerPkg
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed claimUnary positiveUnary auditRoute
  have exportUnaryFromRoute : UnaryHistory «export» :=
    unary_cont_closed failureUnary refusalUnary exportRoute
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed auditUnary exportUnaryFromRoute ledgerRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row ledger ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row claim ∨ hsame row positive ∨ hsame row failure ∨
              hsame row refusal ∨ hsame row «export» ∨ hsame row audit ∨ hsame row ledger)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont claim positive audit ∧ Cont failure refusal «export» ∧
              Cont audit «export» ledger ∧ PkgSig bundle ledger pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro ledger ⟨hsame_refl ledger, ledgerUnary⟩
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
                  (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, auditRoute, exportRoute, ledgerRoute, ledgerPkg⟩
  }
  exact ⟨cert, auditUnary, exportUnaryFromRoute, ledgerUnary⟩

end BEDC.Derived.AuditSystemUp
