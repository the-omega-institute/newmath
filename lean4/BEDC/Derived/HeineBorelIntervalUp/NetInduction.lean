import BEDC.Derived.HeineBorelIntervalUp.TasteGate

namespace BEDC.Derived.HeineBorelIntervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def HeineBorelIntervalFiniteNetInductionRoute [AskSetup] [PackageSetup]
    (x : HeineBorelIntervalUp) (coverageRead inductionRead : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory PkgSig
  match x with
  | HeineBorelIntervalUp.mk _A _B _K _M Z F _T _S _R _E _Q C P N =>
      UnaryHistory Z ∧ UnaryHistory F ∧ UnaryHistory C ∧ UnaryHistory P ∧
        UnaryHistory N ∧ Cont coverageRead Z inductionRead ∧
          Cont F C inductionRead ∧ Cont C P N ∧ PkgSig bundle inductionRead pkg

theorem HeineBorelIntervalNetInduction [AskSetup] [PackageSetup]
    (x : HeineBorelIntervalUp) {net mesh coverageRead inductionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HeineBorelIntervalCoverageRoute x net mesh coverageRead bundle pkg →
      HeineBorelIntervalFiniteNetInductionRoute x coverageRead inductionRead bundle pkg →
        SemanticNameCert
            (fun row : BHist => hsame row inductionRead ∧ UnaryHistory row)
            (fun row : BHist => hsame row coverageRead ∨ hsame row inductionRead)
            (fun row : BHist =>
              UnaryHistory row ∧
                HeineBorelIntervalFiniteNetInductionRoute
                  x coverageRead inductionRead bundle pkg)
            hsame ∧
          UnaryHistory inductionRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg hsame SemanticNameCert UnaryHistory
  intro coverageRoute inductionRoute
  have coverageResult :
      SemanticNameCert
          (fun row : BHist => hsame row coverageRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row net ∨ hsame row mesh ∨ hsame row coverageRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont net mesh coverageRead ∧
              PkgSig bundle coverageRead pkg)
          hsame ∧
        UnaryHistory coverageRead :=
    HeineBorelIntervalNetCoverage x coverageRoute
  have coverageUnary : UnaryHistory coverageRead := coverageResult.right
  cases x with
  | mk A B K M Z F T S R E Q C P N =>
      obtain ⟨zUnary, _fUnary, _cUnary, _pUnary, _nUnary,
        coverageInduction, _finiteReplay, _packageReplay, _inductionPkg⟩ :=
        inductionRoute
      have routeHere :
          HeineBorelIntervalFiniteNetInductionRoute
            (HeineBorelIntervalUp.mk A B K M Z F T S R E Q C P N)
            coverageRead inductionRead bundle pkg :=
        ⟨zUnary, _fUnary, _cUnary, _pUnary, _nUnary, coverageInduction,
          _finiteReplay, _packageReplay, _inductionPkg⟩
      have inductionUnary : UnaryHistory inductionRead :=
        unary_cont_closed coverageUnary zUnary coverageInduction
      have cert :
          SemanticNameCert
              (fun row : BHist => hsame row inductionRead ∧ UnaryHistory row)
              (fun row : BHist => hsame row coverageRead ∨ hsame row inductionRead)
              (fun row : BHist =>
                UnaryHistory row ∧
                  HeineBorelIntervalFiniteNetInductionRoute
                    (HeineBorelIntervalUp.mk A B K M Z F T S R E Q C P N)
                    coverageRead inductionRead bundle pkg)
              hsame := {
        core := {
          carrier_inhabited := Exists.intro inductionRead
            ⟨hsame_refl inductionRead, inductionUnary⟩
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
          exact Or.inr source.left
        ledger_sound := by
          intro _row source
          exact ⟨source.right, routeHere⟩
      }
      exact ⟨cert, inductionUnary⟩

end BEDC.Derived.HeineBorelIntervalUp
