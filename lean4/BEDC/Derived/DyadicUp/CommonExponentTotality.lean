import BEDC.Derived.DyadicUp.CommonExponentNormalization

namespace BEDC.Derived.DyadicUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicCommonExponentTotality [AskSetup] [PackageSetup]
    {left right leftScale rightScale commonExponent leftRead rightRead joined : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
        UnaryHistory left →
          UnaryHistory right →
            UnaryHistory leftScale →
              UnaryHistory rightScale →
                UnaryHistory leftRead →
                  Cont left leftScale commonExponent →
                    Cont right rightScale commonExponent →
                      Cont commonExponent leftRead joined →
                        Cont commonExponent rightRead joined →
                          PkgSig bundle joined pkg →
                            UnaryHistory commonExponent ∧ UnaryHistory joined ∧
                              hsame joined joined ∧ PkgSig bundle joined pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame UnaryHistory
  intro leftUnary _rightUnary leftScaleUnary _rightScaleUnary leftReadUnary leftRoute _rightRoute
    leftReadRoute _rightReadRoute joinedPkg
  have commonUnary : UnaryHistory commonExponent :=
    unary_cont_closed leftUnary leftScaleUnary leftRoute
  have joinedUnary : UnaryHistory joined :=
    unary_cont_closed commonUnary leftReadUnary leftReadRoute
  exact ⟨commonUnary, joinedUnary, hsame_refl joined, joinedPkg⟩

end BEDC.Derived.DyadicUp
