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

theorem BolzanoWeierstrassCarrier_regular_cluster_seal [AskSetup] [PackageSetup]
    {S K R Q E H C P N sourceAdmission sourceSupport retainedWindow readbackWindow
      clusterSeal regularSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BolzanoWeierstrassCarrier S K R Q E H C P N bundle pkg ->
      Cont S K sourceAdmission ->
        Cont sourceAdmission H sourceSupport ->
          Cont K R retainedWindow ->
            Cont retainedWindow Q readbackWindow ->
              Cont readbackWindow E clusterSeal ->
                Cont clusterSeal H regularSeal ->
                  PkgSig bundle sourceSupport pkg ->
                    PkgSig bundle regularSeal pkg ->
                      SemanticNameCert
                          (fun row : BHist => hsame row regularSeal ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row S ∨ hsame row K ∨ hsame row R ∨ hsame row Q ∨
                              hsame row E ∨ hsame row sourceSupport ∨ hsame row regularSeal)
                          (fun row : BHist =>
                            UnaryHistory row ∧ PkgSig bundle P pkg ∧
                              PkgSig bundle regularSeal pkg)
                          hsame ∧
                        UnaryHistory sourceAdmission ∧ UnaryHistory sourceSupport ∧
                          UnaryHistory retainedWindow ∧ UnaryHistory readbackWindow ∧
                            UnaryHistory clusterSeal ∧ UnaryHistory regularSeal := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier sourceAdmissionRoute sourceSupportRoute retainedRoute readbackRoute
    clusterRoute regularRoute _sourceSupportPkg regularPkg
  obtain ⟨sUnary, kUnary, rUnary, qUnary, eUnary, hUnary, _cUnary, _pUnary,
    _nUnary, _sourceIntervalRoute, _readbackSealRoute, _transportReplayRoute,
    carrierPkg⟩ := carrier
  have sourceAdmissionUnary : UnaryHistory sourceAdmission :=
    unary_cont_closed sUnary kUnary sourceAdmissionRoute
  have sourceSupportUnary : UnaryHistory sourceSupport :=
    unary_cont_closed sourceAdmissionUnary hUnary sourceSupportRoute
  have retainedUnary : UnaryHistory retainedWindow :=
    unary_cont_closed kUnary rUnary retainedRoute
  have readbackUnary : UnaryHistory readbackWindow :=
    unary_cont_closed retainedUnary qUnary readbackRoute
  have clusterUnary : UnaryHistory clusterSeal :=
    unary_cont_closed readbackUnary eUnary clusterRoute
  have regularUnary : UnaryHistory regularSeal :=
    unary_cont_closed clusterUnary hUnary regularRoute
  have sourceRegular :
      (fun row : BHist => hsame row regularSeal ∧ UnaryHistory row) regularSeal := by
    exact ⟨hsame_refl regularSeal, regularUnary⟩
  constructor
  · exact {
      core := {
        carrier_inhabited := Exists.intro regularSeal sourceRegular
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
        exact ⟨source.right, carrierPkg, regularPkg⟩
    }
  · exact
      ⟨sourceAdmissionUnary, sourceSupportUnary, retainedUnary, readbackUnary,
        clusterUnary, regularUnary⟩

end BEDC.Derived.BolzanoWeierstrassUp
