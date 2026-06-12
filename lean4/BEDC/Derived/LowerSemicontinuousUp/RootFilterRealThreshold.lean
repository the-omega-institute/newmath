import BEDC.Derived.LowerSemicontinuousUp.RealHandoff

namespace BEDC.Derived.LowerSemicontinuousUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LowerSemicontinuousRootFilterRealThreshold [AskSetup] [PackageSetup]
    {X F E W R O H C P N filterRead thresholdRead locatedRead realSeal _namedRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    lowerSemicontinuousRootFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, E, W, R, O, H, C, P, N] ->
      UnaryHistory W ->
        UnaryHistory R ->
          UnaryHistory E ->
            UnaryHistory O ->
              UnaryHistory N ->
                Cont W R filterRead ->
                  Cont filterRead E thresholdRead ->
                    Cont thresholdRead O locatedRead ->
                      Cont locatedRead N realSeal ->
                        PkgSig bundle P pkg ->
                          PkgSig bundle N pkg ->
                            SemanticNameCert
                                (fun row : BHist => hsame row realSeal ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row W ∨ hsame row R ∨ hsame row E ∨
                                    hsame row O ∨ hsame row N ∨ hsame row filterRead ∨
                                      hsame row thresholdRead ∨ hsame row locatedRead ∨
                                        hsame row realSeal)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ Cont W R filterRead ∧
                                    Cont filterRead E thresholdRead ∧
                                      Cont thresholdRead O locatedRead ∧
                                        Cont locatedRead N realSeal ∧ PkgSig bundle P pkg ∧
                                          PkgSig bundle N pkg)
                                hsame ∧
                              UnaryHistory filterRead ∧ UnaryHistory thresholdRead ∧
                                UnaryHistory locatedRead ∧ UnaryHistory realSeal := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Cont PkgSig SemanticNameCert UnaryHistory
  intro fields wUnary rUnary eUnary oUnary nUnary filterRoute thresholdRoute locatedRoute
    realSealRoute provenancePkg namePkg
  have _acceptedFields :
      lowerSemicontinuousRootFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, E, W, R, O, H, C, P, N] := fields
  have filterUnary : UnaryHistory filterRead :=
    unary_cont_closed wUnary rUnary filterRoute
  have thresholdUnary : UnaryHistory thresholdRead :=
    unary_cont_closed filterUnary eUnary thresholdRoute
  have locatedUnary : UnaryHistory locatedRead :=
    unary_cont_closed thresholdUnary oUnary locatedRoute
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed locatedUnary nUnary realSealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realSeal ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row O ∨ hsame row N ∨
              hsame row filterRead ∨ hsame row thresholdRead ∨ hsame row locatedRead ∨
                hsame row realSeal)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W R filterRead ∧ Cont filterRead E thresholdRead ∧
              Cont thresholdRead O locatedRead ∧ Cont locatedRead N realSeal ∧
                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro realSeal ⟨hsame_refl realSeal, realSealUnary⟩
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
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, filterRoute, thresholdRoute, locatedRoute, realSealRoute,
          provenancePkg, namePkg⟩
  }
  exact ⟨cert, filterUnary, thresholdUnary, locatedUnary, realSealUnary⟩

end BEDC.Derived.LowerSemicontinuousUp
