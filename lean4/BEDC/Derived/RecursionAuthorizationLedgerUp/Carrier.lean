import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RecursionAuthorizationLedgerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RecursionAuthorizationLedgerCarrier [AskSetup] [PackageSetup]
    (signature eliminator motive branch descent output transport route provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory signature ∧ UnaryHistory eliminator ∧ UnaryHistory motive ∧
    UnaryHistory branch ∧ UnaryHistory descent ∧ UnaryHistory output ∧
      UnaryHistory transport ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
        UnaryHistory name ∧ Cont signature eliminator motive ∧
          Cont branch descent output ∧ Cont output transport route ∧
            PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg

theorem RecursionAuthorizationLedgerCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {signature eliminator motive branch descent output transport route provenance name audit : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RecursionAuthorizationLedgerCarrier signature eliminator motive branch descent output
        transport route provenance name bundle pkg ->
      Cont signature eliminator motive ->
        Cont branch descent output ->
          Cont output route audit ->
            PkgSig bundle audit pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row audit ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row signature ∨ hsame row eliminator ∨ hsame row motive ∨
                      hsame row branch ∨ hsame row descent ∨ hsame row output ∨
                        hsame row audit)
                  (fun row : BHist => hsame row audit ∧ PkgSig bundle audit pkg)
                  hsame ∧
                UnaryHistory signature ∧ UnaryHistory eliminator ∧ UnaryHistory motive ∧
                  UnaryHistory branch ∧ UnaryHistory descent ∧ UnaryHistory output ∧
                    UnaryHistory audit ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle audit pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier signatureEliminatorMotive branchDescentOutput outputRouteAudit auditPkg
  obtain ⟨signatureUnary, eliminatorUnary, motiveUnary, branchUnary, descentUnary,
    outputUnary, _transportUnary, routeUnary, provenanceUnary, nameUnary,
    _carrierSignatureEliminatorMotive, _carrierBranchDescentOutput,
    _outputTransportRoute, provenancePkg, _namePkg⟩ := carrier
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed outputUnary routeUnary outputRouteAudit
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row audit ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row signature ∨ hsame row eliminator ∨ hsame row motive ∨
              hsame row branch ∨ hsame row descent ∨ hsame row output ∨ hsame row audit)
          (fun row : BHist => hsame row audit ∧ PkgSig bundle audit pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro audit ⟨hsame_refl audit, auditUnary⟩
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
        exact ⟨hsame_trans (hsame_symm same) source.left,
          unary_transport source.right same⟩
    }
    pattern_sound := by
      intro row source
      exact Or.inr
        (Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, auditPkg⟩
  }
  exact
    ⟨cert, signatureUnary, eliminatorUnary, motiveUnary, branchUnary, descentUnary,
      outputUnary, auditUnary, provenancePkg, auditPkg⟩

end BEDC.Derived.RecursionAuthorizationLedgerUp
