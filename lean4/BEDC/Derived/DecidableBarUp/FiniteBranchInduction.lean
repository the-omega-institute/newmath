import BEDC.Derived.DecidableBarUp

namespace BEDC.Derived.DecidableBarUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DecidableBarFiniteBranchInduction [AskSetup] [PackageSetup]
    {C S W R D H T P N streamWindow barWindow depthRead branchRead nameRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DecidableBarCarrier C S W R D H T P N →
      Cont C S streamWindow →
        Cont streamWindow W barWindow →
          Cont barWindow R depthRead →
            Cont depthRead D branchRead →
              Cont P N nameRead →
                PkgSig bundle nameRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row branchRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row C ∨ hsame row S ∨ hsame row W ∨ hsame row R ∨
                          hsame row D ∨ hsame row streamWindow ∨ hsame row barWindow ∨
                            hsame row depthRead ∨ hsame row branchRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont C S streamWindow ∧
                          Cont streamWindow W barWindow ∧ Cont barWindow R depthRead ∧
                            Cont depthRead D branchRead)
                      hsame ∧
                    UnaryHistory streamWindow ∧ UnaryHistory barWindow ∧
                      UnaryHistory depthRead ∧ UnaryHistory branchRead ∧
                        UnaryHistory nameRead := by
  -- BEDC touchpoint anchor: DecidableBarCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier streamRoute barRoute depthRoute branchRoute nameRoute _namePkg
  obtain
    ⟨unaryC, unaryS, unaryW, unaryR, unaryD, _unaryH, _unaryT, unaryP, unaryN,
      _sameH, _carrierStreamRoute, _carrierDepthRoute⟩ := carrier
  have streamUnary : UnaryHistory streamWindow :=
    unary_cont_closed unaryC unaryS streamRoute
  have barUnary : UnaryHistory barWindow :=
    unary_cont_closed streamUnary unaryW barRoute
  have depthUnary : UnaryHistory depthRead :=
    unary_cont_closed barUnary unaryR depthRoute
  have branchUnary : UnaryHistory branchRead :=
    unary_cont_closed depthUnary unaryD branchRoute
  have nameUnary : UnaryHistory nameRead :=
    unary_cont_closed unaryP unaryN nameRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row branchRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row C ∨ hsame row S ∨ hsame row W ∨ hsame row R ∨ hsame row D ∨
              hsame row streamWindow ∨ hsame row barWindow ∨ hsame row depthRead ∨
                hsame row branchRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont C S streamWindow ∧ Cont streamWindow W barWindow ∧
              Cont barWindow R depthRead ∧ Cont depthRead D branchRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro branchRead ⟨hsame_refl branchRead, branchUnary⟩
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
                      (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, streamRoute, barRoute, depthRoute, branchRoute⟩
  }
  exact ⟨cert, streamUnary, barUnary, depthUnary, branchUnary, nameUnary⟩

end BEDC.Derived.DecidableBarUp
