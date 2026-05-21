import BEDC.Derived.RealityConstrainedTruthCertUp

namespace BEDC.Derived.RealityConstrainedTruthCertUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealityConstrainedTruthCertRootReadinessPacket [AskSetup] [PackageSetup]
    {S Sigma K T U D I L F N routeOne routeTwo rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealityConstrainedTruthCertCarrier S Sigma K T U D I L F N →
      Cont S L routeOne →
        Cont routeOne F routeTwo →
          Cont routeTwo N rootRead →
            PkgSig bundle rootRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row rootRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row S ∨ hsame row L ∨ hsame row F ∨ hsame row N ∨
                      hsame row rootRead)
                  (fun row : BHist => hsame row rootRead ∧ PkgSig bundle rootRead pkg)
                  hsame ∧
                UnaryHistory routeOne ∧ UnaryHistory routeTwo ∧ UnaryHistory rootRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier sourceLedgerRoute routeOneFailureRoute routeTwoNameRoute rootPkg
  obtain ⟨unarySource, _unarySignature, _unaryTower, _unaryStability, unaryInvariant,
    unaryLedger, _sourceSignatureClassifier, _towerStabilityDescent, invariantLedgerFailure,
    ledgerFailureName⟩ := carrier
  have unaryFailure : UnaryHistory F :=
    unary_cont_closed unaryInvariant unaryLedger invariantLedgerFailure
  have unaryName : UnaryHistory N :=
    unary_cont_closed unaryLedger unaryFailure ledgerFailureName
  have unaryRouteOne : UnaryHistory routeOne :=
    unary_cont_closed unarySource unaryLedger sourceLedgerRoute
  have unaryRouteTwo : UnaryHistory routeTwo :=
    unary_cont_closed unaryRouteOne unaryFailure routeOneFailureRoute
  have unaryRootRead : UnaryHistory rootRead :=
    unary_cont_closed unaryRouteTwo unaryName routeTwoNameRoute
  have sourceRoot : (fun row : BHist => hsame row rootRead ∧ UnaryHistory row) rootRead :=
    ⟨hsame_refl rootRead, unaryRootRead⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row rootRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row S ∨ hsame row L ∨ hsame row F ∨ hsame row N ∨ hsame row rootRead)
        (fun row : BHist => hsame row rootRead ∧ PkgSig bundle rootRead pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro rootRead sourceRoot
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
          exact
            ⟨hsame_trans (hsame_symm same) source.left,
              unary_transport source.right same⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
      ledger_sound := by
        intro _row source
        exact ⟨source.left, rootPkg⟩
    }
  exact ⟨cert, unaryRouteOne, unaryRouteTwo, unaryRootRead⟩

end BEDC.Derived.RealityConstrainedTruthCertUp
