import BEDC.Derived.LowerSemicontinuousUp.RealHandoff

namespace BEDC.Derived.LowerSemicontinuousUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LowerSemicontinuousRootEpigraphCarrierAdmission [AskSetup] [PackageSetup]
    {X F E W R O H C P N sourceRead graphRead carrierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    lowerSemicontinuousRootFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, E, W, R, O, H, C, P, N] ->
      UnaryHistory X ->
        UnaryHistory F ->
          UnaryHistory W ->
            UnaryHistory E ->
              Cont X F sourceRead ->
                Cont sourceRead W graphRead ->
                  Cont graphRead E carrierRead ->
                    PkgSig bundle P pkg ->
                      PkgSig bundle N pkg ->
                        SemanticNameCert
                          (fun row : BHist => hsame row carrierRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row X ∨ hsame row F ∨ hsame row E ∨ hsame row W ∨
                              hsame row R ∨ hsame row O ∨ hsame row H ∨ hsame row C ∨
                                hsame row P ∨ hsame row N ∨ hsame row carrierRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont X F sourceRead ∧
                              Cont sourceRead W graphRead ∧
                                Cont graphRead E carrierRead ∧
                                  PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                          hsame ∧ UnaryHistory sourceRead ∧ UnaryHistory graphRead ∧
                        UnaryHistory carrierRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro fields sourceUnary graphUnary scheduleUnary epigraphUnary sourceRoute graphRoute
    carrierRoute provenancePkg namePkg
  have _acceptedFields :
      lowerSemicontinuousRootFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, E, W, R, O, H, C, P, N] := fields
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed sourceUnary graphUnary sourceRoute
  have graphReadUnary : UnaryHistory graphRead :=
    unary_cont_closed sourceReadUnary scheduleUnary graphRoute
  have carrierReadUnary : UnaryHistory carrierRead :=
    unary_cont_closed graphReadUnary epigraphUnary carrierRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row carrierRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row X ∨ hsame row F ∨ hsame row E ∨ hsame row W ∨ hsame row R ∨
            hsame row O ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
              hsame row carrierRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont X F sourceRead ∧ Cont sourceRead W graphRead ∧
            Cont graphRead E carrierRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro carrierRead ⟨hsame_refl carrierRead, carrierReadUnary⟩
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
                        (Or.inr
                          (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, sourceRoute, graphRoute, carrierRoute, provenancePkg, namePkg⟩
  }
  exact ⟨cert, sourceReadUnary, graphReadUnary, carrierReadUnary⟩

end BEDC.Derived.LowerSemicontinuousUp
