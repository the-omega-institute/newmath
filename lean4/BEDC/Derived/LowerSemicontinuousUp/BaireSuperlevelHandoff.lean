import BEDC.Derived.LowerSemicontinuousUp.RealHandoff

namespace BEDC.Derived.LowerSemicontinuousUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LowerSemicontinuousBaireOneSuperlevelHandoff [AskSetup] [PackageSetup]
    {X F E W R O H C P N baireRead lowerRead thresholdRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    lowerSemicontinuousRootFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, E, W, R, O, H, C, P, N] ->
      UnaryHistory W -> UnaryHistory R -> UnaryHistory E -> UnaryHistory O ->
        UnaryHistory N ->
          Cont W R baireRead -> Cont baireRead E lowerRead ->
            Cont lowerRead O thresholdRead -> Cont thresholdRead N sealRead ->
              PkgSig bundle P pkg -> PkgSig bundle N pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row O ∨
                        hsame row thresholdRead ∨ hsame row sealRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont W R baireRead ∧
                        Cont baireRead E lowerRead ∧ Cont lowerRead O thresholdRead ∧
                          Cont thresholdRead N sealRead ∧ PkgSig bundle P pkg ∧
                            PkgSig bundle N pkg)
                    hsame ∧ UnaryHistory baireRead ∧ UnaryHistory lowerRead ∧
                  UnaryHistory thresholdRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro fields unaryW unaryR unaryE unaryO unaryN baireRoute lowerRoute thresholdRoute
    sealRoute provenancePkg localNamePkg
  have _acceptedFields :
      lowerSemicontinuousRootFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, E, W, R, O, H, C, P, N] := fields
  have baireUnary : UnaryHistory baireRead :=
    unary_cont_closed unaryW unaryR baireRoute
  have lowerUnary : UnaryHistory lowerRead :=
    unary_cont_closed baireUnary unaryE lowerRoute
  have thresholdUnary : UnaryHistory thresholdRead :=
    unary_cont_closed lowerUnary unaryO thresholdRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed thresholdUnary unaryN sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row O ∨
              hsame row thresholdRead ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W R baireRead ∧ Cont baireRead E lowerRead ∧
              Cont lowerRead O thresholdRead ∧ Cont thresholdRead N sealRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, baireRoute, lowerRoute, thresholdRoute, sealRoute, provenancePkg,
          localNamePkg⟩
  }
  exact ⟨cert, baireUnary, lowerUnary, thresholdUnary, sealUnary⟩

end BEDC.Derived.LowerSemicontinuousUp
