import BEDC.Derived.AxiomRefusalLedgerUp.NameCertObligations

namespace BEDC.Derived.AxiomRefusalLedgerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AxiomRefusalLedger_namecert_audit_surface_consumer [AskSetup] [PackageSetup]
    {A S Q F R G H C P N nameRead alternativeRead auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory A →
      UnaryHistory S →
        UnaryHistory Q →
          UnaryHistory F →
            UnaryHistory R →
              UnaryHistory G →
                UnaryHistory C →
                  UnaryHistory N →
                    Cont A S nameRead →
                      Cont Q F alternativeRead →
                        Cont R G auditRead →
                          hsame H BHist.Empty →
                            PkgSig bundle P pkg →
                              (∃ row : BHist,
                                  (hsame row N ∧ Cont A S nameRead ∧
                                    Cont Q F alternativeRead ∧ Cont R G auditRead ∧
                                      hsame H BHist.Empty) ∧
                                    (hsame row N ∧ PkgSig bundle P pkg)) ∧
                                UnaryHistory nameRead ∧ UnaryHistory alternativeRead ∧
                                  UnaryHistory auditRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro unaryA unaryS unaryQ unaryF unaryR unaryG _unaryC unaryN nameRoute
    alternativeRoute auditRoute transportEmpty provenancePkg
  have obligations :=
    AxiomRefusalLedger_namecert_obligations (A := A) (S := S) (Q := Q) (F := F)
      (R := R) (G := G) (H := H) (C := C) (P := P) (N := N)
      (nameRead := nameRead) (alternativeRead := alternativeRead) (auditRead := auditRead)
      (bundle := bundle) (pkg := pkg) unaryA unaryS unaryQ unaryF unaryR unaryG
      _unaryC unaryN nameRoute alternativeRoute auditRoute transportEmpty provenancePkg
  have surfaceWitness :=
    semanticNameCert_pattern_ledger_witness obligations.left
  exact
    ⟨surfaceWitness, obligations.right.left, obligations.right.right.left,
      obligations.right.right.right⟩

theorem AxiomRefusalLedger_accepted_readback_consumer [AskSetup] [PackageSetup]
    {A S Q F R G H C P N nameRead alternativeRead auditRead acceptedRead consumer
      consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory A →
      UnaryHistory S →
        UnaryHistory Q →
          UnaryHistory F →
            UnaryHistory R →
              UnaryHistory G →
                UnaryHistory C →
                  UnaryHistory N →
                    Cont A S nameRead →
                      Cont Q F alternativeRead →
                        Cont R G auditRead →
                          Cont auditRead C acceptedRead →
                            UnaryHistory consumer →
                              Cont acceptedRead consumer consumerRead →
                                hsame H BHist.Empty →
                                  PkgSig bundle P pkg →
                                    PkgSig bundle consumerRead pkg →
                                      SemanticNameCert
                                          (fun row : BHist =>
                                            hsame row consumerRead ∧ UnaryHistory row)
                                          (fun row : BHist =>
                                            hsame row acceptedRead ∨ hsame row consumerRead)
                                          (fun row : BHist =>
                                            UnaryHistory row ∧
                                              Cont auditRead C acceptedRead ∧
                                                Cont acceptedRead consumer consumerRead ∧
                                                  PkgSig bundle P pkg ∧
                                                    PkgSig bundle consumerRead pkg)
                                          hsame ∧
                                        UnaryHistory consumerRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro unaryA unaryS unaryQ unaryF unaryR unaryG unaryC unaryN nameRoute
    alternativeRoute auditRoute acceptedRoute consumerUnary consumerRoute transportEmpty
    provenancePkg consumerPkg
  have noninternalized :=
    AxiomRefusalLedger_noninternalization (A := A) (S := S) (Q := Q) (F := F)
      (R := R) (G := G) (H := H) (C := C) (P := P) (N := N)
      (nameRead := nameRead) (alternativeRead := alternativeRead) (auditRead := auditRead)
      (acceptedRead := acceptedRead) (bundle := bundle) (pkg := pkg) unaryA unaryS unaryQ
      unaryF unaryR unaryG unaryC unaryN nameRoute alternativeRoute auditRoute acceptedRoute
      transportEmpty provenancePkg
  have acceptedReadUnary : UnaryHistory acceptedRead := noninternalized.right
  have acceptedSource :
      (fun row : BHist => hsame row acceptedRead ∧ UnaryHistory row) acceptedRead := by
    exact ⟨hsame_refl acceptedRead, acceptedReadUnary⟩
  have acceptedLedger :=
    noninternalized.left.ledger_sound acceptedSource
  have consumerReadUnary : UnaryHistory consumerRead :=
    unary_cont_closed acceptedReadUnary consumerUnary consumerRoute
  have consumerSource :
      (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row) consumerRead := by
    exact ⟨hsame_refl consumerRead, consumerReadUnary⟩
  have downstreamCert :
      SemanticNameCert
          (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row acceptedRead ∨ hsame row consumerRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont auditRead C acceptedRead ∧
              Cont acceptedRead consumer consumerRead ∧ PkgSig bundle P pkg ∧
                PkgSig bundle consumerRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro consumerRead consumerSource
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
      exact Or.inr source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, acceptedLedger.right.right.right.right.left, consumerRoute,
          acceptedLedger.right.right.right.right.right, consumerPkg⟩
  }
  exact ⟨downstreamCert, consumerReadUnary⟩

end BEDC.Derived.AxiomRefusalLedgerUp
