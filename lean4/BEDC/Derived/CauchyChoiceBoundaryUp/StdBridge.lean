import BEDC.Derived.CauchyChoiceBoundaryUp.NameCertObligationSurface

namespace BEDC.Derived.CauchyChoiceBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyChoiceBoundaryUp_StdBridge [AskSetup] [PackageSetup]
    {M E I T S R H C P N selectedRead tailRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyChoiceBoundaryCarrier M E I T S R H C P N ->
      Cont M E I ->
        Cont I T selectedRead ->
          Cont selectedRead S tailRead ->
            Cont tailRead R sealRead ->
              PkgSig bundle N pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row sealRead ∧ Cont selectedRead S tailRead ∧
                        Cont tailRead R sealRead)
                    (fun row : BHist => hsame row sealRead ∧ PkgSig bundle N pkg)
                    hsame ∧
                  UnaryHistory I ∧ UnaryHistory selectedRead ∧ UnaryHistory tailRead ∧
                    UnaryHistory sealRead ∧ hsame H (append M E) ∧ Cont C P N ∧
                      PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier routeI routeSelected routeTail routeSeal namePkg
  obtain ⟨unaryM, unaryE, _unaryI, unaryT, unaryS, unaryR, sameH, routeN⟩ := carrier
  have surface :=
    CauchyChoiceBoundaryNameCertObligationSurface
      (M := M) (E := E) (I := I) (T := T) (S := S) (R := R) (H := H) (C := C)
      (P := P) (N := N) (selectedRead := selectedRead) (tailRead := tailRead)
      (sealRead := sealRead) (bundle := bundle) (pkg := pkg) routeI routeSelected routeTail
      routeSeal unaryM unaryE unaryT unaryS unaryR namePkg
  exact
    ⟨surface.left, surface.right.left, surface.right.right.left,
      surface.right.right.right.left, surface.right.right.right.right, sameH, routeN, namePkg⟩

end BEDC.Derived.CauchyChoiceBoundaryUp
