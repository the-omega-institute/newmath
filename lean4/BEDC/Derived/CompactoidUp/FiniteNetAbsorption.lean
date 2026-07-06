import BEDC.Derived.CompactoidUp.NameCertObligations

namespace BEDC.Derived.CompactoidUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompactoidCarrier_finite_net_absorption [AskSetup] [PackageSetup]
    {U L T M K E B H R P N netRead metricRead compactRead completionRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactoidCarrier U L T M K E B H R P N bundle pkg ->
      Cont L T netRead ->
        Cont netRead M metricRead ->
          Cont metricRead K compactRead ->
            Cont compactRead E completionRead ->
              Cont completionRead B realRead ->
                PkgSig bundle P pkg ->
                  PkgSig bundle N pkg ->
                    SemanticNameCert
                        (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row L ∨ hsame row T ∨ hsame row M ∨ hsame row K ∨
                            hsame row E ∨ hsame row B ∨ hsame row netRead ∨
                              hsame row metricRead ∨ hsame row compactRead ∨
                                hsame row completionRead ∨ hsame row realRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont L T netRead ∧
                            Cont netRead M metricRead ∧ Cont metricRead K compactRead ∧
                              Cont compactRead E completionRead ∧
                                Cont completionRead B realRead ∧ PkgSig bundle P pkg ∧
                                  PkgSig bundle N pkg)
                        hsame ∧
                      UnaryHistory netRead ∧ UnaryHistory metricRead ∧
                        UnaryHistory compactRead ∧ UnaryHistory completionRead ∧
                          UnaryHistory realRead := by
  -- BEDC touchpoint anchor: BHist CompactoidCarrier Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier netRoute metricRoute compactRoute completionRoute realRoute pkgRow nameRow
  obtain ⟨_uUnary, lUnary, tUnary, mUnary, kUnary, eUnary, bUnary, _hUnary, _rUnary,
    _pUnary, _nUnary, _carrierPkg, _namePkg⟩ := carrier
  have netUnary : UnaryHistory netRead :=
    unary_cont_closed lUnary tUnary netRoute
  have metricUnary : UnaryHistory metricRead :=
    unary_cont_closed netUnary mUnary metricRoute
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed metricUnary kUnary compactRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed compactUnary eUnary completionRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed completionUnary bUnary realRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row L ∨ hsame row T ∨ hsame row M ∨ hsame row K ∨
              hsame row E ∨ hsame row B ∨ hsame row netRead ∨
                hsame row metricRead ∨ hsame row compactRead ∨
                  hsame row completionRead ∨ hsame row realRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont L T netRead ∧
              Cont netRead M metricRead ∧ Cont metricRead K compactRead ∧
                Cont compactRead E completionRead ∧ Cont completionRead B realRead ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro realRead ⟨hsame_refl realRead, realUnary⟩
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
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, netRoute, metricRoute, compactRoute, completionRoute, realRoute,
          pkgRow, nameRow⟩
  }
  exact
    ⟨cert, netUnary, metricUnary, compactUnary, completionUnary, realUnary⟩

end BEDC.Derived.CompactoidUp
