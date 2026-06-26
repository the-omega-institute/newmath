import BEDC.Derived.SturmRootIsolationUp.SignVariationHandoff
import BEDC.FKernel.NameCert

namespace BEDC.Derived.SturmRootIsolationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SturmRootIsolationCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {P I D V B W R S H C Q N branchRead replayRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont B H branchRead →
      Cont branchRead C replayRead →
        Cont replayRead S sealRead →
          PkgSig bundle Q pkg →
            PkgSig bundle N pkg →
              UnaryHistory B →
                UnaryHistory H →
                  UnaryHistory C →
                    UnaryHistory S →
                      SemanticNameCert
                          (fun row : BHist =>
                            (hsame row B ∨ hsame row S ∨ hsame row replayRead) ∧
                              UnaryHistory row)
                          (fun row : BHist =>
                            hsame row P ∨ hsame row I ∨ hsame row D ∨ hsame row V ∨
                              hsame row B ∨ hsame row W ∨ hsame row R ∨ hsame row S ∨
                                Cont B H branchRead ∨ Cont branchRead C replayRead ∨
                                  Cont replayRead S sealRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ PkgSig bundle Q pkg ∧
                              PkgSig bundle N pkg)
                          hsame ∧
                        UnaryHistory branchRead ∧ UnaryHistory replayRead ∧
                          UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: SturmRootIsolationUp BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro branchRoute replayRoute sealRoute qPkg nPkg branchUnary transportUnary replayUnary
    sealUnary
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed branchUnary transportUnary branchRoute
  have replayReadUnary : UnaryHistory replayRead :=
    unary_cont_closed branchReadUnary replayUnary replayRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed replayReadUnary sealUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row B ∨ hsame row S ∨ hsame row replayRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row P ∨ hsame row I ∨ hsame row D ∨ hsame row V ∨ hsame row B ∨
              hsame row W ∨ hsame row R ∨ hsame row S ∨ Cont B H branchRead ∨
                Cont branchRead C replayRead ∨ Cont replayRead S sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle Q pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro B ⟨Or.inl (hsame_refl B), branchUnary⟩
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
        constructor
        · cases source.left with
          | inl sameB =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameB)
          | inr rest =>
              cases rest with
              | inl sameS =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameS))
              | inr sameReplay =>
                  exact Or.inr
                    (Or.inr (hsame_trans (hsame_symm sameRows) sameReplay))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row _source
      right
      right
      right
      right
      right
      right
      right
      right
      left
      exact branchRoute
    ledger_sound := by
      intro _row source
      exact ⟨source.right, qPkg, nPkg⟩
  }
  exact ⟨cert, branchReadUnary, replayReadUnary, sealReadUnary⟩

end BEDC.Derived.SturmRootIsolationUp
