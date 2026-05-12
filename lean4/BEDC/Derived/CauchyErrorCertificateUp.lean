import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyErrorCertificateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyErrorCertificatePacket [AskSetup] [PackageSetup]
    (readback modulus tail budget provenance nameCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory readback ∧ UnaryHistory modulus ∧ UnaryHistory tail ∧ UnaryHistory budget ∧
    UnaryHistory provenance ∧ UnaryHistory nameCert ∧ Cont modulus tail budget ∧
      Cont readback budget provenance ∧ PkgSig bundle readback pkg ∧
        PkgSig bundle provenance pkg

theorem CauchyErrorCertificatePacket_namecert_obligations [AskSetup] [PackageSetup]
    {readback modulus tail budget provenance nameCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyErrorCertificatePacket readback modulus tail budget provenance nameCert bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          hsame row readback ∧
            CauchyErrorCertificatePacket readback modulus tail budget provenance nameCert
              bundle pkg)
        (fun row : BHist => hsame row readback)
        (fun row : BHist => hsame row readback ∧ PkgSig bundle readback pkg)
        hsame ∧ UnaryHistory readback ∧ UnaryHistory modulus ∧ UnaryHistory tail ∧
          UnaryHistory budget ∧ PkgSig bundle readback pkg := by
  intro packet
  have packetWitness := packet
  obtain ⟨readbackUnary, modulusUnary, tailUnary, budgetUnary, _provenanceUnary,
    _nameCertUnary, _modulusTailBudget, _readbackBudgetProvenance, readbackPkg,
    _provenancePkg⟩ := packet
  have sourceWitness :
      (fun row : BHist =>
        hsame row readback ∧
          CauchyErrorCertificatePacket readback modulus tail budget provenance nameCert
            bundle pkg) readback := by
    exact And.intro (hsame_refl readback) packetWitness
  have core :
      NameCert
        (fun row : BHist =>
          hsame row readback ∧
            CauchyErrorCertificatePacket readback modulus tail budget provenance nameCert
              bundle pkg)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro readback sourceWitness
      equiv_refl := by
        intro h _source
        exact hsame_refl h
      equiv_symm := by
        intro h k same
        exact hsame_symm same
      equiv_trans := by
        intro h k r sameHK sameKR
        exact hsame_trans sameHK sameKR
      carrier_respects_equiv := by
        intro h k sameHK sourceH
        have sameHReadback : hsame h readback := sourceH.left
        have sameKReadback : hsame k readback :=
          hsame_trans (hsame_symm sameHK) sameHReadback
        exact And.intro sameKReadback sourceH.right
    }
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          hsame row readback ∧
            CauchyErrorCertificatePacket readback modulus tail budget provenance nameCert
              bundle pkg)
        (fun row : BHist => hsame row readback)
        (fun row : BHist => hsame row readback ∧ PkgSig bundle readback pkg)
        hsame := by
    exact {
      core := core
      pattern_sound := by
        intro h source
        exact source.left
      ledger_sound := by
        intro h source
        exact And.intro source.left readbackPkg
    }
  exact
    And.intro cert
      (And.intro readbackUnary
        (And.intro modulusUnary (And.intro tailUnary (And.intro budgetUnary readbackPkg))))

theorem CauchyErrorCertificatePacket_budget_handoff_closure [AskSetup] [PackageSetup]
    {readback modulus tail budget budget' provenance nameCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyErrorCertificatePacket readback modulus tail budget provenance nameCert bundle pkg ->
      hsame budget budget' ->
        Cont modulus tail budget' ->
          Cont readback budget' provenance ->
            CauchyErrorCertificatePacket readback modulus tail budget' provenance nameCert
              bundle pkg := by
  intro packet sameBudget modulusTailBudget' readbackBudgetProvenance'
  obtain ⟨readbackUnary, modulusUnary, tailUnary, budgetUnary, provenanceUnary, nameCertUnary,
    _modulusTailBudget, _readbackBudgetProvenance, readbackPkg, provenancePkg⟩ := packet
  have budgetUnary' : UnaryHistory budget' :=
    unary_transport budgetUnary sameBudget
  exact
    ⟨readbackUnary, modulusUnary, tailUnary, budgetUnary', provenanceUnary, nameCertUnary,
      modulusTailBudget', readbackBudgetProvenance', readbackPkg, provenancePkg⟩

theorem CauchyErrorCertificatePacket_downstream_handoff [AskSetup] [PackageSetup]
    {readback modulus tail budget provenance nameCert consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyErrorCertificatePacket readback modulus tail budget provenance nameCert bundle pkg ->
      Cont budget readback consumer ->
        PkgSig bundle consumer pkg ->
          UnaryHistory readback ∧ UnaryHistory modulus ∧ UnaryHistory tail ∧
            UnaryHistory budget ∧ UnaryHistory provenance ∧ UnaryHistory consumer ∧
              Cont modulus tail budget ∧ Cont readback budget provenance ∧
                Cont budget readback consumer ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle consumer pkg := by
  intro packet budgetReadbackConsumer consumerPkg
  obtain ⟨readbackUnary, modulusUnary, tailUnary, budgetUnary, provenanceUnary,
    _nameCertUnary, modulusTailBudget, readbackBudgetProvenance, _readbackPkg,
    provenancePkg⟩ := packet
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed budgetUnary readbackUnary budgetReadbackConsumer
  exact
    ⟨readbackUnary, modulusUnary, tailUnary, budgetUnary, provenanceUnary, consumerUnary,
      modulusTailBudget, readbackBudgetProvenance, budgetReadbackConsumer, provenancePkg,
      consumerPkg⟩

theorem CauchyErrorCertificatePacket_modulus_soundness [AskSetup] [PackageSetup]
    {readback modulus tail budget provenance nameCert tail' budget' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyErrorCertificatePacket readback modulus tail budget provenance nameCert bundle pkg ->
      hsame tail tail' ->
        Cont modulus tail' budget' ->
          Cont readback budget' provenance ->
            UnaryHistory modulus ∧ UnaryHistory tail' ∧ UnaryHistory budget' ∧
              hsame budget budget' ∧ PkgSig bundle readback pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro packet sameTail modulusTailBudget' _readbackBudgetProvenance'
  obtain ⟨_readbackUnary, modulusUnary, tailUnary, _budgetUnary, _provenanceUnary,
    _nameCertUnary, modulusTailBudget, _readbackBudgetProvenance, readbackPkg,
    _provenancePkg⟩ := packet
  have tailUnary' : UnaryHistory tail' :=
    unary_transport tailUnary sameTail
  have budgetUnary' : UnaryHistory budget' :=
    unary_cont_closed modulusUnary tailUnary' modulusTailBudget'
  have sameBudget : hsame budget budget' :=
    cont_respects_hsame (hsame_refl modulus) sameTail modulusTailBudget
      modulusTailBudget'
  exact ⟨modulusUnary, tailUnary', budgetUnary', sameBudget, readbackPkg⟩

theorem CauchyErrorCertificatePacket_readback_route_uniqueness [AskSetup] [PackageSetup]
    {readback modulus tail budget provenance nameCert readback' provenance' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyErrorCertificatePacket readback modulus tail budget provenance nameCert bundle pkg ->
      CauchyErrorCertificatePacket readback' modulus tail budget provenance' nameCert
          bundle pkg ->
        hsame provenance provenance' ->
          hsame readback readback' ∧ Cont modulus tail budget ∧
            Cont readback budget provenance ∧ Cont readback' budget provenance' ∧
              PkgSig bundle readback pkg ∧ PkgSig bundle readback' pkg := by
  intro packet packet' sameProvenance
  obtain ⟨_readbackUnary, _modulusUnary, _tailUnary, _budgetUnary, _provenanceUnary,
    _nameCertUnary, modulusTailBudget, readbackBudgetProvenance, readbackPkg,
    _provenancePkg⟩ := packet
  obtain ⟨_readbackUnary', _modulusUnary', _tailUnary', _budgetUnary', _provenanceUnary',
    _nameCertUnary', _modulusTailBudget', readbackBudgetProvenance', readbackPkg',
    _provenancePkg'⟩ := packet'
  have sameReadback : hsame readback readback' :=
    cont_common_suffix_cancellation readbackBudgetProvenance readbackBudgetProvenance'
      sameProvenance
  exact
    ⟨sameReadback, modulusTailBudget, readbackBudgetProvenance, readbackBudgetProvenance',
      readbackPkg, readbackPkg'⟩

end BEDC.Derived.CauchyErrorCertificateUp
