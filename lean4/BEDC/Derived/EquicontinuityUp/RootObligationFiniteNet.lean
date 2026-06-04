import BEDC.Derived.EquicontinuityUp

namespace BEDC.Derived.EquicontinuityUp.RootObligationFiniteNet

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem EquicontinuityRootObligationFiniteNet [AskSetup] [PackageSetup]
    {K F eps rho M T R P N radiusRead handoffRead finiteNetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EquicontinuityCarrier K F eps rho M T R P N radiusRead handoffRead bundle pkg ->
      UnaryHistory M ->
        Cont handoffRead M finiteNetRead ->
          PkgSig bundle finiteNetRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row finiteNetRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row K ∨ hsame row F ∨ hsame row eps ∨ hsame row rho ∨
                    hsame row M ∨ hsame row finiteNetRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont K F radiusRead ∧
                    Cont radiusRead rho handoffRead ∧ Cont handoffRead M finiteNetRead ∧
                      PkgSig bundle finiteNetRead pkg)
                hsame ∧
              UnaryHistory radiusRead ∧ UnaryHistory handoffRead ∧
                UnaryHistory finiteNetRead := by
  -- BEDC touchpoint anchor: EquicontinuityCarrier BHist ProbeBundle PkgSig Cont hsame SemanticNameCert UnaryHistory
  intro carrier unaryM finiteNetRoute finiteNetPkg
  obtain ⟨unaryK, unaryF, unaryRho, _unaryR, _unaryN, radiusRoute, handoffRoute,
    _pkgP, _pkgN⟩ := carrier
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed unaryK unaryF radiusRoute
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed radiusUnary unaryRho handoffRoute
  have finiteNetUnary : UnaryHistory finiteNetRead :=
    unary_cont_closed handoffUnary unaryM finiteNetRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row finiteNetRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row K ∨ hsame row F ∨ hsame row eps ∨ hsame row rho ∨
              hsame row M ∨ hsame row finiteNetRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont K F radiusRead ∧
              Cont radiusRead rho handoffRead ∧ Cont handoffRead M finiteNetRead ∧
                PkgSig bundle finiteNetRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro finiteNetRead ⟨hsame_refl finiteNetRead, finiteNetUnary⟩
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
                (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, radiusRoute, handoffRoute, finiteNetRoute, finiteNetPkg⟩
  }
  exact ⟨cert, radiusUnary, handoffUnary, finiteNetUnary⟩

end BEDC.Derived.EquicontinuityUp.RootObligationFiniteNet
