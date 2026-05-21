import BEDC.Derived.BoundedUniversalTraceUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.BoundedUniversalTraceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BoundedUniversalTraceCarrier [AskSetup] [PackageSetup]
    (fuel substrate source trace readback transport route provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory fuel ∧ UnaryHistory substrate ∧ UnaryHistory source ∧
    UnaryHistory trace ∧ UnaryHistory readback ∧ UnaryHistory transport ∧
      UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
        PkgSig bundle name pkg

theorem BoundedUniversalTraceCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {fuel substrate source trace readback transport route provenance name audit : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedUniversalTraceCarrier fuel substrate source trace readback transport route provenance
        name bundle pkg ->
      Cont trace readback audit ->
        PkgSig bundle audit pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row audit ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row fuel ∨ hsame row substrate ∨ hsame row source ∨ hsame row trace ∨
                  hsame row readback ∨ hsame row audit)
              (fun row : BHist => hsame row audit ∧ PkgSig bundle audit pkg)
              hsame ∧
            UnaryHistory fuel ∧ UnaryHistory substrate ∧ UnaryHistory source ∧
              UnaryHistory trace ∧ UnaryHistory readback ∧ UnaryHistory audit := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier traceReadbackAudit auditPkg
  obtain ⟨fuelUnary, substrateUnary, sourceUnary, traceUnary, readbackUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _nameUnary, _namePkg⟩ := carrier
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed traceUnary readbackUnary traceReadbackAudit
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row audit ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row fuel ∨ hsame row substrate ∨ hsame row source ∨ hsame row trace ∨
              hsame row readback ∨ hsame row audit)
          (fun row : BHist => hsame row audit ∧ PkgSig bundle audit pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro audit
        ⟨hsame_refl audit, auditUnary⟩
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
        intro row row' sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, auditPkg⟩
  }
  exact
    ⟨cert, fuelUnary, substrateUnary, sourceUnary, traceUnary, readbackUnary, auditUnary⟩

end BEDC.Derived.BoundedUniversalTraceUp
