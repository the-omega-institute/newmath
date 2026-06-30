import BEDC.Derived.CauchyProductMetricUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyProductMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductMetricProjectionStability [AskSetup] [PackageSetup]
    {L R WL WR QL QR D Delta E H C P N leftRead rightRead metricRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory WL →
      UnaryHistory WR →
        UnaryHistory QL →
          UnaryHistory QR →
            Cont WL QL leftRead →
              Cont WR QR rightRead →
                Cont leftRead rightRead metricRead →
                  PkgSig bundle metricRead pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row metricRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row L ∨ hsame row R ∨ hsame row WL ∨ hsame row WR ∨
                            hsame row QL ∨ hsame row QR ∨ hsame row Delta ∨
                              hsame row metricRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont WL QL leftRead ∧
                            Cont WR QR rightRead ∧ Cont leftRead rightRead metricRead ∧
                              PkgSig bundle metricRead pkg)
                        hsame ∧
                      UnaryHistory leftRead ∧ UnaryHistory rightRead ∧
                        UnaryHistory metricRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro wlUnary wrUnary qlUnary qrUnary leftRoute rightRoute metricRoute metricPkg
  have leftUnary : UnaryHistory leftRead :=
    unary_cont_closed wlUnary qlUnary leftRoute
  have rightUnary : UnaryHistory rightRead :=
    unary_cont_closed wrUnary qrUnary rightRoute
  have metricUnary : UnaryHistory metricRead :=
    unary_cont_closed leftUnary rightUnary metricRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row metricRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row L ∨ hsame row R ∨ hsame row WL ∨ hsame row WR ∨
              hsame row QL ∨ hsame row QR ∨ hsame row Delta ∨ hsame row metricRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont WL QL leftRead ∧ Cont WR QR rightRead ∧
              Cont leftRead rightRead metricRead ∧ PkgSig bundle metricRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro metricRead ⟨hsame_refl metricRead, metricUnary⟩
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
                    (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, leftRoute, rightRoute, metricRoute, metricPkg⟩
  }
  exact ⟨cert, leftUnary, rightUnary, metricUnary⟩

end BEDC.Derived.CauchyProductMetricUp
