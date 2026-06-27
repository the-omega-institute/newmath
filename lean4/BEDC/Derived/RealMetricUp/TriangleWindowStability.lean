import BEDC.Derived.RealMetricUp

namespace BEDC.Derived.RealMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealMetricCarrier_triangle_window_stability [AskSetup] [PackageSetup]
    {X Y Z Axy Ayz Axz D S R H C P N xyWindow xyRead xyAbs yzWindow yzRead yzAbs
      xzWindow xzRead xzAbs triangleRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealMetricCarrier X Y Axy D S R H C P N bundle pkg ->
      RealMetricCarrier Y Z Ayz D S R H C P N bundle pkg ->
        RealMetricCarrier X Z Axz D S R H C P N bundle pkg ->
          Cont S R xyWindow ->
            Cont xyWindow D xyRead ->
              Cont xyRead Axy xyAbs ->
                Cont S R yzWindow ->
                  Cont yzWindow D yzRead ->
                    Cont yzRead Ayz yzAbs ->
                      Cont S R xzWindow ->
                        Cont xzWindow D xzRead ->
                          Cont xzRead Axz xzAbs ->
                            Cont xyAbs yzAbs triangleRead ->
                              PkgSig bundle triangleRead pkg ->
                                UnaryHistory xyWindow ∧ UnaryHistory xyRead ∧
                                  UnaryHistory xyAbs ∧ UnaryHistory yzWindow ∧
                                    UnaryHistory yzRead ∧ UnaryHistory yzAbs ∧
                                      UnaryHistory xzWindow ∧ UnaryHistory xzRead ∧
                                        UnaryHistory xzAbs ∧ UnaryHistory triangleRead ∧
                                          PkgSig bundle P pkg ∧
                                            PkgSig bundle triangleRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro xyCarrier _yzCarrier _xzCarrier xyWindowRoute xyReadRoute xyAbsRoute yzWindowRoute
    yzReadRoute yzAbsRoute xzWindowRoute xzReadRoute xzAbsRoute triangleRoute trianglePkg
  have dUnary : UnaryHistory D := xyCarrier.right.right.right.left
  have sUnary : UnaryHistory S := xyCarrier.right.right.right.right.left
  have rUnary : UnaryHistory R := xyCarrier.right.right.right.right.right.left
  have axyUnary : UnaryHistory Axy := xyCarrier.right.right.left
  have ayzUnary : UnaryHistory Ayz := _yzCarrier.right.right.left
  have axzUnary : UnaryHistory Axz := _xzCarrier.right.right.left
  have pPkg : PkgSig bundle P pkg :=
    xyCarrier.right.right.right.right.right.right.right.right.right.right.left
  have xyWindowUnary : UnaryHistory xyWindow :=
    unary_cont_closed sUnary rUnary xyWindowRoute
  have xyReadUnary : UnaryHistory xyRead :=
    unary_cont_closed xyWindowUnary dUnary xyReadRoute
  have xyAbsUnary : UnaryHistory xyAbs :=
    unary_cont_closed xyReadUnary axyUnary xyAbsRoute
  have yzWindowUnary : UnaryHistory yzWindow :=
    unary_cont_closed sUnary rUnary yzWindowRoute
  have yzReadUnary : UnaryHistory yzRead :=
    unary_cont_closed yzWindowUnary dUnary yzReadRoute
  have yzAbsUnary : UnaryHistory yzAbs :=
    unary_cont_closed yzReadUnary ayzUnary yzAbsRoute
  have xzWindowUnary : UnaryHistory xzWindow :=
    unary_cont_closed sUnary rUnary xzWindowRoute
  have xzReadUnary : UnaryHistory xzRead :=
    unary_cont_closed xzWindowUnary dUnary xzReadRoute
  have xzAbsUnary : UnaryHistory xzAbs :=
    unary_cont_closed xzReadUnary axzUnary xzAbsRoute
  have triangleUnary : UnaryHistory triangleRead :=
    unary_cont_closed xyAbsUnary yzAbsUnary triangleRoute
  exact
    ⟨xyWindowUnary, xyReadUnary, xyAbsUnary, yzWindowUnary, yzReadUnary, yzAbsUnary,
      xzWindowUnary, xzReadUnary, xzAbsUnary, triangleUnary, pPkg, trianglePkg⟩

end BEDC.Derived.RealMetricUp
