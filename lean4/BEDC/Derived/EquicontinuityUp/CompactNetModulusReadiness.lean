import BEDC.Derived.EquicontinuityUp

namespace BEDC.Derived.EquicontinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem EquicontinuityCompactNetModulusReadiness [AskSetup] [PackageSetup]
    {K F eps rho M T R P N radiusRead handoffRead modulusRead finiteNetRead
      readinessRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EquicontinuityCarrier K F eps rho M T R P N radiusRead handoffRead bundle pkg ->
      UnaryHistory M ->
        UnaryHistory T ->
          Cont handoffRead M modulusRead ->
            Cont modulusRead T finiteNetRead ->
              Cont finiteNetRead N readinessRead ->
                PkgSig bundle readinessRead pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row readinessRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row K ∨ hsame row F ∨ hsame row eps ∨ hsame row rho ∨
                          hsame row M ∨ hsame row T ∨ hsame row N ∨
                            hsame row modulusRead ∨ hsame row finiteNetRead ∨
                              hsame row readinessRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont K F radiusRead ∧
                          Cont radiusRead rho handoffRead ∧
                            Cont handoffRead M modulusRead ∧
                              Cont modulusRead T finiteNetRead ∧
                                Cont finiteNetRead N readinessRead ∧
                                  PkgSig bundle readinessRead pkg)
                      hsame ∧
                    UnaryHistory modulusRead ∧ UnaryHistory finiteNetRead ∧
                      UnaryHistory readinessRead := by
  -- BEDC touchpoint anchor: EquicontinuityCarrier BHist ProbeBundle PkgSig Cont hsame SemanticNameCert UnaryHistory
  intro carrier unaryM unaryT modulusRoute finiteNetRoute readinessRoute readinessPkg
  have sharedStability :=
    EquicontinuityCarrier_shared_radius_stability carrier
  obtain ⟨_unaryK, _unaryF, _unaryRho, _unaryR, unaryN, _compactFamily,
    _radiusHandoff, _carrierPkgP, _carrierPkgN⟩ := carrier
  obtain ⟨_radiusUnary, handoffUnary, radiusRoute, handoffRoute, _pkgP, _pkgN⟩ :=
    sharedStability
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed handoffUnary unaryM modulusRoute
  have finiteNetUnary : UnaryHistory finiteNetRead :=
    unary_cont_closed modulusUnary unaryT finiteNetRoute
  have readinessUnary : UnaryHistory readinessRead :=
    unary_cont_closed finiteNetUnary unaryN readinessRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row readinessRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row K ∨ hsame row F ∨ hsame row eps ∨ hsame row rho ∨ hsame row M ∨
              hsame row T ∨ hsame row N ∨ hsame row modulusRead ∨
                hsame row finiteNetRead ∨ hsame row readinessRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont K F radiusRead ∧ Cont radiusRead rho handoffRead ∧
              Cont handoffRead M modulusRead ∧ Cont modulusRead T finiteNetRead ∧
                Cont finiteNetRead N readinessRead ∧ PkgSig bundle readinessRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro readinessRead ⟨hsame_refl readinessRead, readinessUnary⟩
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
                        (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, radiusRoute, handoffRoute, modulusRoute, finiteNetRoute,
          readinessRoute, readinessPkg⟩
  }
  exact ⟨cert, modulusUnary, finiteNetUnary, readinessUnary⟩

end BEDC.Derived.EquicontinuityUp
