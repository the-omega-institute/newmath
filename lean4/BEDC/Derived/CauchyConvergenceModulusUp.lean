import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyConvergenceModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyConvergenceModulusCarrier [AskSetup] [PackageSetup]
    (source tolerance schedule windows readback limit transport route provenance nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory tolerance ∧ UnaryHistory schedule ∧
    UnaryHistory windows ∧ UnaryHistory readback ∧ UnaryHistory limit ∧
      UnaryHistory transport ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
        UnaryHistory nameRow ∧ Cont source tolerance schedule ∧
          Cont schedule windows readback ∧ Cont readback limit route ∧
            Cont route transport provenance ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle nameRow pkg

theorem CauchyConvergenceModulusNamecertObligations [AskSetup] [PackageSetup]
    {source tolerance schedule windows readback limit transport route provenance nameRow
      auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyConvergenceModulusCarrier source tolerance schedule windows readback limit transport
        route provenance nameRow bundle pkg →
      Cont route nameRow auditRead →
        PkgSig bundle auditRead pkg →
          SemanticNameCert
              (fun row : BHist =>
                CauchyConvergenceModulusCarrier source tolerance schedule windows readback
                    limit transport route provenance nameRow bundle pkg ∧
                  hsame row nameRow)
              (fun row : BHist =>
                hsame row source ∨ hsame row tolerance ∨ hsame row schedule ∨
                  hsame row windows ∨ hsame row readback ∨ hsame row limit ∨
                    hsame row nameRow)
              (fun row : BHist =>
                PkgSig bundle provenance pkg ∧ PkgSig bundle auditRead pkg ∧
                  hsame row nameRow ∧ Cont route nameRow auditRead)
              hsame ∧
            UnaryHistory source ∧ UnaryHistory tolerance ∧ UnaryHistory schedule ∧
              UnaryHistory windows ∧ UnaryHistory readback ∧ UnaryHistory limit ∧
                UnaryHistory auditRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier routeNameAudit auditPkg
  have carrierPacket :
      CauchyConvergenceModulusCarrier source tolerance schedule windows readback limit
        transport route provenance nameRow bundle pkg :=
    carrier
  obtain ⟨sourceUnary, toleranceUnary, scheduleUnary, windowsUnary, readbackUnary,
    limitUnary, _transportUnary, routeUnary, _provenanceUnary, nameRowUnary,
    _sourceToleranceSchedule, _scheduleWindowsReadback, _readbackLimitRoute,
    _routeTransportProvenance, provenancePkg, _namePkg⟩ := carrier
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed routeUnary nameRowUnary routeNameAudit
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            CauchyConvergenceModulusCarrier source tolerance schedule windows readback
                limit transport route provenance nameRow bundle pkg ∧
              hsame row nameRow)
          (fun row : BHist =>
            hsame row source ∨ hsame row tolerance ∨ hsame row schedule ∨
              hsame row windows ∨ hsame row readback ∨ hsame row limit ∨
                hsame row nameRow)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle auditRead pkg ∧
              hsame row nameRow ∧ Cont route nameRow auditRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro nameRow
        (And.intro carrierPacket (hsame_refl nameRow))
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
        intro _row _other same sourceRow
        exact And.intro sourceRow.left (hsame_trans (hsame_symm same) sourceRow.right)
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.right)))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨provenancePkg, auditPkg, sourceRow.right, routeNameAudit⟩
  }
  exact
    ⟨cert, sourceUnary, toleranceUnary, scheduleUnary, windowsUnary, readbackUnary,
      limitUnary, auditUnary⟩

end BEDC.Derived.CauchyConvergenceModulusUp
