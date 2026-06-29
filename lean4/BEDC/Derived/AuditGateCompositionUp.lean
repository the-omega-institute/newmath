import BEDC.Derived.AuditGateCompositionUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.AuditGateCompositionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def AuditGateCompositionCarrier [AskSetup] [PackageSetup]
    (G0 G1 B0 B1 R0 R1 Q H K P N : BHist) (bundle : ProbeBundle ProbeName)
    (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg PkgSig UnaryHistory
  UnaryHistory G0 ∧ UnaryHistory G1 ∧ UnaryHistory B0 ∧ UnaryHistory B1 ∧
    UnaryHistory R0 ∧ UnaryHistory R1 ∧ UnaryHistory Q ∧ UnaryHistory H ∧
      UnaryHistory K ∧ UnaryHistory P ∧ UnaryHistory N ∧ PkgSig bundle P pkg ∧
        PkgSig bundle N pkg

theorem AuditGateCompositionCarrier_membrane_obligation [AskSetup] [PackageSetup]
    {G0 G1 B0 B1 R0 R1 Q H K P N membraneRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuditGateCompositionCarrier G0 G1 B0 B1 R0 R1 Q H K P N bundle pkg →
      Cont P H membraneRead →
        PkgSig bundle membraneRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row membraneRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row P ∨ hsame row H ∨ hsame row K ∨ hsame row N ∨
                  hsame row membraneRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont P H membraneRead ∧ PkgSig bundle P pkg ∧
                  PkgSig bundle membraneRead pkg)
              hsame ∧ UnaryHistory membraneRead := by
  -- BEDC touchpoint anchor: AuditGateCompositionCarrier BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier membraneRoute membranePkg
  obtain ⟨_g0Unary, _g1Unary, _b0Unary, _b1Unary, _r0Unary, _r1Unary, _qUnary,
    hUnary, _kUnary, pUnary, _nUnary, pPkg, _nPkg⟩ := carrier
  have membraneUnary : UnaryHistory membraneRead :=
    unary_cont_closed pUnary hUnary membraneRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row membraneRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row P ∨ hsame row H ∨ hsame row K ∨ hsame row N ∨
              hsame row membraneRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont P H membraneRead ∧ PkgSig bundle P pkg ∧
              PkgSig bundle membraneRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro membraneRead ⟨hsame_refl membraneRead, membraneUnary⟩
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
      repeat (first | exact source.left | apply Or.inr)
    ledger_sound := by
      intro _row source
      exact ⟨source.right, membraneRoute, pPkg, membranePkg⟩
  }
  exact ⟨cert, membraneUnary⟩

end BEDC.Derived.AuditGateCompositionUp
