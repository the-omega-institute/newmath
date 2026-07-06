import BEDC.Derived.BolzanoWeierstrassUp.FiniteSubsequenceObligations
import BEDC.FKernel.NameCert

namespace BEDC.Derived.BolzanoWeierstrassUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BolzanoWeierstrassCarrier_cluster_seal_nonescape [AskSetup] [PackageSetup]
    {S K R Q E H C P N sourceAdmission sourceSupport retainedWindow readbackWindow
      clusterSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BolzanoWeierstrassCarrier S K R Q E H C P N bundle pkg ->
      Cont S K sourceAdmission ->
        Cont sourceAdmission H sourceSupport ->
          Cont K R retainedWindow ->
            Cont retainedWindow Q readbackWindow ->
              Cont readbackWindow E clusterSeal ->
                PkgSig bundle sourceSupport pkg ->
                  PkgSig bundle clusterSeal pkg ->
                    SemanticNameCert
                        (fun row : BHist => hsame row clusterSeal ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row S ∨ hsame row K ∨ hsame row R ∨ hsame row Q ∨
                            hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                              hsame row N ∨ hsame row sourceAdmission ∨
                                hsame row sourceSupport ∨ hsame row retainedWindow ∨
                                  hsame row readbackWindow ∨ hsame row clusterSeal)
                        (fun row : BHist =>
                          UnaryHistory row ∧ PkgSig bundle sourceSupport pkg ∧
                            PkgSig bundle clusterSeal pkg)
                        hsame ∧
                      UnaryHistory sourceAdmission ∧ UnaryHistory sourceSupport ∧
                        UnaryHistory retainedWindow ∧ UnaryHistory readbackWindow ∧
                          UnaryHistory clusterSeal := by
  -- BEDC touchpoint anchor: BolzanoWeierstrassCarrier BHist Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier sourceAdmissionRoute sourceSupportRoute retainedRoute readbackRoute
    clusterRoute sourceSupportPkg clusterPkg
  obtain ⟨SUnary, KUnary, RUnary, QUnary, EUnary, HUnary, _CUnary, _PUnary,
    _NUnary, _sourceIntervalRoute, _readbackSealRoute, _transportReplayRoute,
    _carrierPkg⟩ := carrier
  have sourceAdmissionUnary : UnaryHistory sourceAdmission :=
    unary_cont_closed SUnary KUnary sourceAdmissionRoute
  have sourceSupportUnary : UnaryHistory sourceSupport :=
    unary_cont_closed sourceAdmissionUnary HUnary sourceSupportRoute
  have retainedUnary : UnaryHistory retainedWindow :=
    unary_cont_closed KUnary RUnary retainedRoute
  have readbackUnary : UnaryHistory readbackWindow :=
    unary_cont_closed retainedUnary QUnary readbackRoute
  have clusterUnary : UnaryHistory clusterSeal :=
    unary_cont_closed readbackUnary EUnary clusterRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row clusterSeal ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row K ∨ hsame row R ∨ hsame row Q ∨
              hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row N ∨ hsame row sourceAdmission ∨
                  hsame row sourceSupport ∨ hsame row retainedWindow ∨
                    hsame row readbackWindow ∨ hsame row clusterSeal)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle sourceSupport pkg ∧
              PkgSig bundle clusterSeal pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro clusterSeal ⟨hsame_refl clusterSeal, clusterUnary⟩
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
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr source.left))))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, sourceSupportPkg, clusterPkg⟩
  }
  exact
    ⟨cert, sourceAdmissionUnary, sourceSupportUnary, retainedUnary, readbackUnary,
      clusterUnary⟩

end BEDC.Derived.BolzanoWeierstrassUp
