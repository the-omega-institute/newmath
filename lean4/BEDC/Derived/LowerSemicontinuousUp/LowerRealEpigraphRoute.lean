import BEDC.Derived.LowerSemicontinuousUp.RealHandoff

namespace BEDC.Derived.LowerSemicontinuousUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LowerSemicontinuousLowerRealEpigraphRoute [AskSetup] [PackageSetup]
    {X F E W R O H C P N sourceRead graphRead valueRead epigraphRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    lowerSemicontinuousRootFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, E, W, R, O, H, C, P, N] ->
      UnaryHistory X ->
        UnaryHistory F ->
          UnaryHistory W ->
            UnaryHistory R ->
              UnaryHistory E ->
                UnaryHistory O ->
                  Cont X F sourceRead ->
                    Cont sourceRead W graphRead ->
                      Cont graphRead R valueRead ->
                        Cont valueRead E epigraphRead ->
                          Cont epigraphRead O sealRead ->
                            PkgSig bundle P pkg ->
                              PkgSig bundle N pkg ->
                                SemanticNameCert
                                    (fun row : BHist =>
                                      hsame row sealRead ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row X ∨ hsame row F ∨ hsame row W ∨
                                        hsame row R ∨ hsame row E ∨ hsame row O ∨
                                          hsame row sealRead)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧ Cont X F sourceRead ∧
                                        Cont sourceRead W graphRead ∧
                                          Cont graphRead R valueRead ∧
                                            Cont valueRead E epigraphRead ∧
                                              Cont epigraphRead O sealRead ∧
                                                PkgSig bundle P pkg ∧
                                                  PkgSig bundle N pkg)
                                    hsame ∧
                                  UnaryHistory sourceRead ∧ UnaryHistory graphRead ∧
                                    UnaryHistory valueRead ∧ UnaryHistory epigraphRead ∧
                                      UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Cont PkgSig SemanticNameCert hsame UnaryHistory
  intro fields xUnary fUnary wUnary rUnary eUnary oUnary sourceRoute graphRoute valueRoute
    epigraphRoute sealRoute provenancePkg namePkg
  have _acceptedFields :
      lowerSemicontinuousRootFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, E, W, R, O, H, C, P, N] := fields
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed xUnary fUnary sourceRoute
  have graphUnary : UnaryHistory graphRead :=
    unary_cont_closed sourceUnary wUnary graphRoute
  have valueUnary : UnaryHistory valueRead :=
    unary_cont_closed graphUnary rUnary valueRoute
  have epigraphUnary : UnaryHistory epigraphRead :=
    unary_cont_closed valueUnary eUnary epigraphRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed epigraphUnary oUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row F ∨ hsame row W ∨ hsame row R ∨ hsame row E ∨
              hsame row O ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont X F sourceRead ∧ Cont sourceRead W graphRead ∧
              Cont graphRead R valueRead ∧ Cont valueRead E epigraphRead ∧
                Cont epigraphRead O sealRead ∧ PkgSig bundle P pkg ∧
                  PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
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
      exact
        ⟨source.right, sourceRoute, graphRoute, valueRoute, epigraphRoute, sealRoute,
          provenancePkg, namePkg⟩
  }
  exact ⟨cert, sourceUnary, graphUnary, valueUnary, epigraphUnary, sealUnary⟩

end BEDC.Derived.LowerSemicontinuousUp
