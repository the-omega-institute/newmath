import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.GapClosureBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem GapClosureBoundarySourceRouteTotality [AskSetup] [PackageSetup]
    {G S R H C P N sourceRead structuralRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory G →
      UnaryHistory S →
        UnaryHistory H →
          Cont G S sourceRead →
            Cont sourceRead H structuralRead →
              PkgSig bundle sourceRead pkg →
                PkgSig bundle structuralRead pkg →
                  UnaryHistory sourceRead ∧ UnaryHistory structuralRead ∧
                    Cont G S sourceRead ∧ Cont sourceRead H structuralRead ∧
                      PkgSig bundle sourceRead pkg ∧ PkgSig bundle structuralRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro unaryG unaryS unaryH sourceRoute structuralRoute sourcePkg structuralPkg
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed unaryG unaryS sourceRoute
  have structuralUnary : UnaryHistory structuralRead :=
    unary_cont_closed sourceUnary unaryH structuralRoute
  exact
    ⟨sourceUnary, structuralUnary, sourceRoute, structuralRoute, sourcePkg,
      structuralPkg⟩

end BEDC.Derived.GapClosureBoundaryUp
