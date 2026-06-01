import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.EquicontinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def EquicontinuityCarrier [AskSetup] [PackageSetup]
    (K F eps rho M T R P N radiusRead handoffRead : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory K ∧ UnaryHistory F ∧ UnaryHistory rho ∧
    Cont K F radiusRead ∧ Cont radiusRead rho handoffRead ∧
      PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem EquicontinuityCarrier_shared_radius_stability [AskSetup] [PackageSetup]
    {K F eps rho M T R P N radiusRead handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EquicontinuityCarrier K F eps rho M T R P N radiusRead handoffRead bundle pkg ->
      UnaryHistory radiusRead ∧ UnaryHistory handoffRead ∧
        Cont K F radiusRead ∧ Cont radiusRead rho handoffRead ∧
          PkgSig bundle P pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier
  obtain ⟨unaryK, unaryF, unaryRho, compactFamily, radiusHandoff, pkgP, pkgN⟩ := carrier
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed unaryK unaryF compactFamily
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed radiusUnary unaryRho radiusHandoff
  exact ⟨radiusUnary, handoffUnary, compactFamily, radiusHandoff, pkgP, pkgN⟩

theorem EquicontinuityCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {K F eps rho M T R P N radiusRead handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont K F radiusRead ->
      Cont radiusRead rho handoffRead ->
        PkgSig bundle P pkg ->
          UnaryHistory K ->
            UnaryHistory F ->
              UnaryHistory rho ->
                SemanticNameCert
                    (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row K ∨ hsame row F ∨ hsame row eps ∨ hsame row rho ∨
                        hsame row M ∨ hsame row T ∨ hsame row R ∨ hsame row P ∨
                          hsame row N ∨ hsame row radiusRead ∨ hsame row handoffRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont K F radiusRead ∧
                        Cont radiusRead rho handoffRead ∧ PkgSig bundle P pkg)
                    hsame ∧
                  UnaryHistory radiusRead ∧ UnaryHistory handoffRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro compactFamily radiusHandoff pkgP unaryK unaryF unaryRho
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed unaryK unaryF compactFamily
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed radiusUnary unaryRho radiusHandoff
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row K ∨ hsame row F ∨ hsame row eps ∨ hsame row rho ∨ hsame row M ∨
              hsame row T ∨ hsame row R ∨ hsame row P ∨ hsame row N ∨
                hsame row radiusRead ∨ hsame row handoffRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont K F radiusRead ∧ Cont radiusRead rho handoffRead ∧
              PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro handoffRead ⟨hsame_refl handoffRead, handoffUnary⟩
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
                        (Or.inr (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, compactFamily, radiusHandoff, pkgP⟩
  }
  exact ⟨cert, radiusUnary, handoffUnary⟩

end BEDC.Derived.EquicontinuityUp
