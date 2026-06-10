import BEDC.Derived.LowerSemicontinuousUp.RootEpigraphFilterDirectedness

namespace BEDC.Derived.LowerSemicontinuousUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LowerSemicontinuousRootEpigraphFilterBasisClosure [AskSetup] [PackageSetup]
    {X F E W R O H C P N leftThreshold rightThreshold commonThreshold filterRead namedRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    lowerSemicontinuousRootEpigraphFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, W, R, E, O, H, C, P, N] ->
      UnaryHistory W -> UnaryHistory R -> UnaryHistory E -> UnaryHistory O -> UnaryHistory H ->
        UnaryHistory C -> UnaryHistory N ->
          Cont W R leftThreshold -> Cont W R rightThreshold ->
            Cont leftThreshold rightThreshold commonThreshold -> Cont commonThreshold E filterRead ->
              Cont filterRead N namedRead -> PkgSig bundle P pkg -> PkgSig bundle N pkg ->
                SemanticNameCert
                  (fun row : BHist => hsame row namedRead /\ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row W \/ hsame row R \/ hsame row E \/ hsame row O \/
                      hsame row commonThreshold \/ hsame row namedRead)
                  (fun row : BHist =>
                    UnaryHistory row /\ Cont leftThreshold rightThreshold commonThreshold /\
                      Cont commonThreshold E filterRead /\ Cont filterRead N namedRead /\
                        PkgSig bundle P pkg /\ PkgSig bundle N pkg)
                  hsame /\ UnaryHistory commonThreshold /\ UnaryHistory filterRead /\
                    UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro fields wUnary rUnary eUnary _oUnary _hUnary _cUnary nUnary leftRoute rightRoute
    commonRoute filterRoute namedRoute provenancePkg namePkg
  have _acceptedFields :
      lowerSemicontinuousRootEpigraphFields
          (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, W, R, E, O, H, C, P, N] := fields
  have leftUnary : UnaryHistory leftThreshold :=
    unary_cont_closed wUnary rUnary leftRoute
  have rightUnary : UnaryHistory rightThreshold :=
    unary_cont_closed wUnary rUnary rightRoute
  have commonUnary : UnaryHistory commonThreshold :=
    unary_cont_closed leftUnary rightUnary commonRoute
  have filterUnary : UnaryHistory filterRead :=
    unary_cont_closed commonUnary eUnary filterRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed filterUnary nUnary namedRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row namedRead /\ UnaryHistory row)
        (fun row : BHist =>
          hsame row W \/ hsame row R \/ hsame row E \/ hsame row O \/
            hsame row commonThreshold \/ hsame row namedRead)
        (fun row : BHist =>
          UnaryHistory row /\ Cont leftThreshold rightThreshold commonThreshold /\
            Cont commonThreshold E filterRead /\ Cont filterRead N namedRead /\
              PkgSig bundle P pkg /\ PkgSig bundle N pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
      exact ⟨source.right, commonRoute, filterRoute, namedRoute, provenancePkg, namePkg⟩
  }
  exact ⟨cert, commonUnary, filterUnary, namedUnary⟩

end BEDC.Derived.LowerSemicontinuousUp
