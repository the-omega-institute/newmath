import BEDC.Derived.CauchyChoiceBoundaryUp.NoChoiceNonescape

namespace BEDC.Derived.CauchyChoiceBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyChoiceBoundaryNameCertObligationSurface [AskSetup] [PackageSetup]
    {M E I T S R H C P N selectedRead tailRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont M E I ->
      Cont I T selectedRead ->
        Cont selectedRead S tailRead ->
          Cont tailRead R sealRead ->
            UnaryHistory M ->
              UnaryHistory E ->
                UnaryHistory T ->
                  UnaryHistory S ->
                    UnaryHistory R ->
                      PkgSig bundle N pkg ->
                        SemanticNameCert
                            (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row sealRead ∧ Cont selectedRead S tailRead ∧
                                Cont tailRead R sealRead)
                            (fun row : BHist => hsame row sealRead ∧ PkgSig bundle N pkg)
                            hsame ∧
                          UnaryHistory I ∧ UnaryHistory selectedRead ∧ UnaryHistory tailRead ∧
                            UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro routeI routeSelected routeTail routeSeal unaryM unaryE unaryT unaryS unaryR namePkg
  have unaryI : UnaryHistory I :=
    unary_cont_closed unaryM unaryE routeI
  have base :=
    CauchyChoiceBoundary_no_choice_nonescape
      (M := M) (E := E) (I := I) (T := T) (S := S) (R := R) (_H := H) (_C := C)
      (_P := P) (N := N) (selectedRead := selectedRead) (tailRead := tailRead)
      (sealRead := sealRead) (bundle := bundle) (pkg := pkg) routeI routeSelected routeTail
      routeSeal unaryM unaryE unaryT unaryS unaryR namePkg
  exact ⟨base.left, unaryI, base.right.left, base.right.right.left, base.right.right.right⟩

end BEDC.Derived.CauchyChoiceBoundaryUp
