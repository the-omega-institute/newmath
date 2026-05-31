import BEDC.Derived.ModulusContinuityUp.TasteGate

namespace BEDC.Derived.ModulusContinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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

theorem ModulusContinuityCompositionNonescape [AskSetup] [PackageSetup]
    {gf sf kf df qf rf hf cf pf nf gg sg kg dg qg rg hg cg pg ng outerWindow handoff
      innerWindow composedRead finalSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory dg →
      UnaryHistory kg →
        UnaryHistory sg →
          UnaryHistory df →
            UnaryHistory kf →
              UnaryHistory rf →
                Cont dg kg outerWindow →
                  Cont outerWindow sg handoff →
                    Cont handoff df innerWindow →
                      Cont innerWindow kf composedRead →
                        Cont composedRead rf finalSeal →
                          PkgSig bundle finalSeal pkg →
                            SemanticNameCert
                                (fun row : BHist => hsame row finalSeal ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row dg ∨ hsame row kg ∨ hsame row sg ∨
                                    hsame row df ∨ hsame row kf ∨ hsame row rf ∨
                                      hsame row finalSeal)
                                (fun row : BHist =>
                                  hsame row finalSeal ∧ PkgSig bundle finalSeal pkg)
                                hsame ∧
                              UnaryHistory finalSeal ∧ Cont composedRead rf finalSeal := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory SemanticNameCert hsame
  intro dgUnary kgUnary sgUnary dfUnary kfUnary rfUnary dgKgOuter outerSgHandoff
    handoffDfInner innerKfComposed composedRfFinal finalPkg
  have outerWindowUnary : UnaryHistory outerWindow :=
    unary_cont_closed dgUnary kgUnary dgKgOuter
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed outerWindowUnary sgUnary outerSgHandoff
  have innerWindowUnary : UnaryHistory innerWindow :=
    unary_cont_closed handoffUnary dfUnary handoffDfInner
  have composedReadUnary : UnaryHistory composedRead :=
    unary_cont_closed innerWindowUnary kfUnary innerKfComposed
  have finalSealUnary : UnaryHistory finalSeal :=
    unary_cont_closed composedReadUnary rfUnary composedRfFinal
  have sourceFinal :
      (fun row : BHist => hsame row finalSeal ∧ UnaryHistory row) finalSeal := by
    exact ⟨hsame_refl finalSeal, finalSealUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row finalSeal ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row dg ∨ hsame row kg ∨ hsame row sg ∨ hsame row df ∨
            hsame row kf ∨ hsame row rf ∨ hsame row finalSeal)
        (fun row : BHist => hsame row finalSeal ∧ PkgSig bundle finalSeal pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro finalSeal sourceFinal
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, finalPkg⟩
  }
  exact ⟨cert, finalSealUnary, composedRfFinal⟩

end BEDC.Derived.ModulusContinuityUp
