import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DirichletKernelUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DirichletKernelCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {W A S Z F R H C P N phaseCoeff circleSum fourierRoute seriesRoute
      localRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory W ->
      UnaryHistory A ->
        UnaryHistory S ->
          UnaryHistory Z ->
            UnaryHistory F ->
              UnaryHistory R ->
                UnaryHistory H ->
                  UnaryHistory C ->
                    UnaryHistory P ->
                      UnaryHistory N ->
                        Cont W A phaseCoeff ->
                          Cont S Z circleSum ->
                            Cont phaseCoeff circleSum fourierRoute ->
                              Cont fourierRoute R seriesRoute ->
                                Cont seriesRoute N localRead ->
                                  PkgSig bundle P pkg ->
                                    PkgSig bundle localRead pkg ->
                                      SemanticNameCert
                                          (fun row : BHist =>
                                            hsame row localRead ∧ UnaryHistory row)
                                          (fun row : BHist =>
                                            hsame row W ∨ hsame row A ∨ hsame row S ∨
                                              hsame row Z ∨ hsame row F ∨ hsame row R ∨
                                                hsame row localRead)
                                          (fun row : BHist =>
                                            hsame row localRead ∧ PkgSig bundle P pkg ∧
                                              PkgSig bundle localRead pkg)
                                          hsame ∧
                                        UnaryHistory phaseCoeff ∧ UnaryHistory circleSum ∧
                                          UnaryHistory fourierRoute ∧
                                            UnaryHistory seriesRoute ∧
                                              UnaryHistory localRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro wUnary aUnary sUnary zUnary _fUnary rUnary _hUnary _cUnary _pUnary nUnary
    phaseRoute circleRoute fourierRouteCont seriesRouteCont localRoute provenancePkg
    localPkg
  have phaseUnary : UnaryHistory phaseCoeff :=
    unary_cont_closed wUnary aUnary phaseRoute
  have circleUnary : UnaryHistory circleSum :=
    unary_cont_closed sUnary zUnary circleRoute
  have fourierUnary : UnaryHistory fourierRoute :=
    unary_cont_closed phaseUnary circleUnary fourierRouteCont
  have seriesUnary : UnaryHistory seriesRoute :=
    unary_cont_closed fourierUnary rUnary seriesRouteCont
  have localUnary : UnaryHistory localRead :=
    unary_cont_closed seriesUnary nUnary localRoute
  have sourceLocal :
      (fun row : BHist => hsame row localRead ∧ UnaryHistory row) localRead := by
    exact ⟨hsame_refl localRead, localUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row localRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row W ∨ hsame row A ∨ hsame row S ∨ hsame row Z ∨ hsame row F ∨
              hsame row R ∨ hsame row localRead)
          (fun row : BHist =>
            hsame row localRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle localRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro localRead sourceLocal
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, provenancePkg, localPkg⟩
  }
  exact ⟨cert, phaseUnary, circleUnary, fourierUnary, seriesUnary, localUnary⟩

end BEDC.Derived.DirichletKernelUp
