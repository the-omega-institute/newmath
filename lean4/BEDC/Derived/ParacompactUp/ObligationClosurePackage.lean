import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Derived.ParacompactUp.TasteGate

namespace BEDC.Derived.ParacompactUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ParacompactCarrier_obligation_closure_package [AskSetup] [PackageSetup]
    {topology window cover refinement localFinite coverage normal urysohn metric transport replay
      provenance localName metricRead normalRead refinementExport : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SemanticNameCert
        (fun row : BHist => hsame row localName ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row topology ∨ hsame row cover ∨ hsame row refinement ∨
            hsame row localFinite ∨ hsame row coverage ∨ hsame row normal ∨
              hsame row urysohn ∨ hsame row metric ∨ Cont cover refinement coverage ∨
                Cont window refinement localFinite)
        (fun row : BHist =>
          PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg ∧ hsame row localName)
        hsame →
      UnaryHistory metricRead →
        UnaryHistory normalRead →
          UnaryHistory refinementExport →
            Cont metric transport metricRead →
              Cont normal urysohn normalRead →
                Cont metricRead normalRead refinementExport →
                  PkgSig bundle provenance pkg →
                    PkgSig bundle refinementExport pkg →
                      PkgSig bundle localName pkg →
                        SemanticNameCert
                            (fun row : BHist => hsame row refinementExport ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row metricRead ∨ hsame row normalRead ∨
                                hsame row refinementExport ∨
                                  Cont metricRead normalRead refinementExport)
                            (fun row : BHist =>
                              PkgSig bundle provenance pkg ∧
                                PkgSig bundle refinementExport pkg ∧
                                  hsame row refinementExport)
                            hsame ∧
                          PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro _localCert metricReadUnary _normalReadUnary refinementExportUnary _metricRoute
    _normalRoute refinementRoute provenancePkg refinementPkg localNamePkg
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro refinementExport ⟨hsame_refl refinementExport, refinementExportUnary⟩
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
        intro row source
        exact Or.inr (Or.inr (Or.inl source.left))
      ledger_sound := by
        intro row source
        exact ⟨provenancePkg, refinementPkg, source.left⟩
    }
  · exact localNamePkg

end BEDC.Derived.ParacompactUp
