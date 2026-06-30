import BEDC.Derived.PaperLeanDriftWitnessUp

namespace BEDC.Derived.PaperLeanDriftWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PaperLeanDriftWitness_obligation_closure_package [AskSetup] [PackageSetup]
    {M A L I R H C P N exactRead duplicateRead unresolvedRead statusRead packageRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PaperLeanDriftWitnessCarrier M A L I R H C P N bundle pkg ->
      Cont L I exactRead ->
        Cont M L duplicateRead ->
          Cont I R unresolvedRead ->
            Cont exactRead duplicateRead statusRead ->
              Cont statusRead C packageRead ->
                PkgSig bundle packageRead pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row packageRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row M ∨ hsame row A ∨ hsame row L ∨ hsame row I ∨
                          hsame row R ∨ hsame row exactRead ∨ hsame row duplicateRead ∨
                            hsame row unresolvedRead ∨ hsame row packageRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont L I exactRead ∧
                          Cont M L duplicateRead ∧ Cont I R unresolvedRead ∧
                            PkgSig bundle packageRead pkg)
                      hsame ∧
                    UnaryHistory exactRead ∧ UnaryHistory duplicateRead ∧
                      UnaryHistory unresolvedRead ∧ UnaryHistory statusRead ∧
                        UnaryHistory packageRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier exactRoute duplicateRoute unresolvedRoute statusRoute packageRoute packagePkg
  obtain ⟨mUnary, _aUnary, lUnary, iUnary, rUnary, _hUnary, cUnary, _pUnary,
    _nUnary, _markerNameLedger, _ledgerInventoryVerdict, _verdictTransportConsumer,
    _namePkg⟩ := carrier
  have exactUnary : UnaryHistory exactRead :=
    unary_cont_closed lUnary iUnary exactRoute
  have duplicateUnary : UnaryHistory duplicateRead :=
    unary_cont_closed mUnary lUnary duplicateRoute
  have unresolvedUnary : UnaryHistory unresolvedRead :=
    unary_cont_closed iUnary rUnary unresolvedRoute
  have statusUnary : UnaryHistory statusRead :=
    unary_cont_closed exactUnary duplicateUnary statusRoute
  have packageUnary : UnaryHistory packageRead :=
    unary_cont_closed statusUnary cUnary packageRoute
  have sourcePackage :
      (fun row : BHist => hsame row packageRead ∧ UnaryHistory row) packageRead := by
    exact ⟨hsame_refl packageRead, packageUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row packageRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row A ∨ hsame row L ∨ hsame row I ∨
              hsame row R ∨ hsame row exactRead ∨ hsame row duplicateRead ∨
                hsame row unresolvedRead ∨ hsame row packageRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont L I exactRead ∧ Cont M L duplicateRead ∧
              Cont I R unresolvedRead ∧ PkgSig bundle packageRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro packageRead sourcePackage
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
        exact Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr source.left)))))))
      ledger_sound := by
        intro _row source
        exact ⟨source.right, exactRoute, duplicateRoute, unresolvedRoute, packagePkg⟩
    }
  exact
    ⟨cert, exactUnary, duplicateUnary, unresolvedUnary, statusUnary, packageUnary⟩

end BEDC.Derived.PaperLeanDriftWitnessUp
