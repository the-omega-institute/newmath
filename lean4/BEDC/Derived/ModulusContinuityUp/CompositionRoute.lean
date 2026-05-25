import BEDC.Derived.ModulusContinuityUp.TasteGate

namespace BEDC.Derived.ModulusContinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ModulusContinuityCompositionRoute [AskSetup] [PackageSetup]
    {gf sf kf df qf rf hf cf pf nf gg sg kg dg qg rg hg cg pg ng outerTol outerWindow
      handoff innerWindow composedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory dg →
      UnaryHistory kg →
        UnaryHistory sg →
          UnaryHistory df →
            UnaryHistory kf →
              Cont dg kg outerWindow →
                Cont outerWindow sg handoff →
                  Cont handoff df innerWindow →
                    Cont innerWindow kf composedRead →
                      PkgSig bundle composedRead pkg →
                        UnaryHistory outerWindow ∧ UnaryHistory handoff ∧
                          UnaryHistory innerWindow ∧ UnaryHistory composedRead ∧
                            Cont dg kg outerWindow ∧ Cont outerWindow sg handoff ∧
                              Cont handoff df innerWindow ∧
                                Cont innerWindow kf composedRead ∧
                                  PkgSig bundle composedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro dgUnary kgUnary sgUnary dfUnary kfUnary dgKgOuter outerSgHandoff handoffDfInner
    innerKfComposed composedPkg
  have outerWindowUnary : UnaryHistory outerWindow :=
    unary_cont_closed dgUnary kgUnary dgKgOuter
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed outerWindowUnary sgUnary outerSgHandoff
  have innerWindowUnary : UnaryHistory innerWindow :=
    unary_cont_closed handoffUnary dfUnary handoffDfInner
  have composedReadUnary : UnaryHistory composedRead :=
    unary_cont_closed innerWindowUnary kfUnary innerKfComposed
  exact
    ⟨outerWindowUnary, handoffUnary, innerWindowUnary, composedReadUnary, dgKgOuter,
      outerSgHandoff, handoffDfInner, innerKfComposed, composedPkg⟩

end BEDC.Derived.ModulusContinuityUp
