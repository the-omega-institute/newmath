import BEDC.Derived.EquicontinuityUp

namespace BEDC.Derived.EquicontinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem EquicontinuityRootObligationCarrier [AskSetup] [PackageSetup]
    {K F eps rho M T R P N radiusRead handoffRead compactNetRead modulusRead rootRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EquicontinuityCarrier K F eps rho M T R P N radiusRead handoffRead bundle pkg ->
      UnaryHistory M ->
        UnaryHistory T ->
          Cont handoffRead M compactNetRead ->
            Cont compactNetRead T modulusRead ->
              Cont modulusRead R rootRead ->
                PkgSig bundle rootRead pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row rootRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row K ∨ hsame row F ∨ hsame row rho ∨ hsame row M ∨
                          hsame row T ∨ hsame row R ∨ hsame row radiusRead ∨
                            hsame row handoffRead ∨ hsame row compactNetRead ∨
                              hsame row modulusRead ∨ hsame row rootRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont K F radiusRead ∧
                          Cont radiusRead rho handoffRead ∧
                            Cont handoffRead M compactNetRead ∧
                              Cont compactNetRead T modulusRead ∧
                                Cont modulusRead R rootRead ∧
                                  PkgSig bundle rootRead pkg)
                      hsame ∧ UnaryHistory radiusRead ∧ UnaryHistory handoffRead ∧
                    UnaryHistory compactNetRead ∧ UnaryHistory modulusRead ∧
                      UnaryHistory rootRead := by
  -- BEDC touchpoint anchor: EquicontinuityCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier unaryM unaryT compactNetRoute modulusRoute rootRoute rootPkg
  obtain ⟨radiusUnary, handoffUnary, radiusRoute, handoffRoute, _pkgP, _pkgN⟩ :=
    EquicontinuityCarrier_shared_radius_stability carrier
  obtain ⟨_unaryK, _unaryF, _unaryRho, unaryR, _unaryN, _carrierRadius,
    _carrierHandoff, _carrierPkgP, _carrierPkgN⟩ := carrier
  have compactNetUnary : UnaryHistory compactNetRead :=
    unary_cont_closed handoffUnary unaryM compactNetRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed compactNetUnary unaryT modulusRoute
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed modulusUnary unaryR rootRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row rootRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row K ∨ hsame row F ∨ hsame row rho ∨ hsame row M ∨ hsame row T ∨
              hsame row R ∨ hsame row radiusRead ∨ hsame row handoffRead ∨
                hsame row compactNetRead ∨ hsame row modulusRead ∨ hsame row rootRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont K F radiusRead ∧ Cont radiusRead rho handoffRead ∧
              Cont handoffRead M compactNetRead ∧ Cont compactNetRead T modulusRead ∧
                Cont modulusRead R rootRead ∧ PkgSig bundle rootRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro rootRead ⟨hsame_refl rootRead, rootUnary⟩
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
        ⟨source.right, radiusRoute, handoffRoute, compactNetRoute, modulusRoute,
          rootRoute, rootPkg⟩
  }
  exact
    ⟨cert, radiusUnary, handoffUnary, compactNetUnary, modulusUnary, rootUnary⟩

end BEDC.Derived.EquicontinuityUp
