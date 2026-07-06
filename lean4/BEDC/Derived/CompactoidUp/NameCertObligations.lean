import BEDC.Derived.CompactoidUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CompactoidUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CompactoidCarrier [AskSetup] [PackageSetup]
    (U L T M K E B H R P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  UnaryHistory U ∧ UnaryHistory L ∧ UnaryHistory T ∧ UnaryHistory M ∧
    UnaryHistory K ∧ UnaryHistory E ∧ UnaryHistory B ∧ UnaryHistory H ∧
      UnaryHistory R ∧ UnaryHistory P ∧ UnaryHistory N ∧
        PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem CompactoidCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {U L T M K E B H R P N netRead metricRead completionRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactoidCarrier U L T M K E B H R P N bundle pkg ->
      Cont L T netRead ->
        Cont netRead M metricRead ->
          Cont metricRead E completionRead ->
            Cont completionRead B realRead ->
              PkgSig bundle P pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row N ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row U ∨ hsame row L ∨ hsame row T ∨ hsame row M ∨
                        hsame row K ∨ hsame row E ∨ hsame row B ∨ hsame row H ∨
                          hsame row R ∨ hsame row P ∨ hsame row N)
                    (fun row : BHist => UnaryHistory row ∧ PkgSig bundle P pkg)
                    hsame ∧
                  UnaryHistory netRead ∧
                    UnaryHistory metricRead ∧
                      UnaryHistory completionRead ∧ UnaryHistory realRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro carrier netRoute metricRoute completionRoute realRoute pkgRow
  obtain ⟨_uUnary, lUnary, tUnary, mUnary, _kUnary, eUnary, bUnary, _hUnary, _rUnary,
    _pUnary, nUnary, _carrierPkg, _namePkg⟩ := carrier
  have netUnary : UnaryHistory netRead :=
    unary_cont_closed lUnary tUnary netRoute
  have metricUnary : UnaryHistory metricRead :=
    unary_cont_closed netUnary mUnary metricRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed metricUnary eUnary completionRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed completionUnary bUnary realRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row N ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row U ∨ hsame row L ∨ hsame row T ∨ hsame row M ∨
              hsame row K ∨ hsame row E ∨ hsame row B ∨ hsame row H ∨
                hsame row R ∨ hsame row P ∨ hsame row N)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro N ⟨hsame_refl N, nUnary⟩
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
        cases sameRows
        exact source
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
                          (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, pkgRow⟩
  }
  exact ⟨cert, netUnary, metricUnary, completionUnary, realUnary⟩

end BEDC.Derived.CompactoidUp
