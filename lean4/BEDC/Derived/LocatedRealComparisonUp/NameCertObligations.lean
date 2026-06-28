import BEDC.Derived.LocatedRealComparisonUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LocatedRealComparisonUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def LocatedRealComparisonCarrier [AskSetup] [PackageSetup]
    (L0 L1 W R0 R1 D0 D1 B A H C P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory L0 ∧
    UnaryHistory L1 ∧
      UnaryHistory W ∧
        UnaryHistory R0 ∧
          UnaryHistory R1 ∧
            UnaryHistory D0 ∧
              UnaryHistory D1 ∧
                UnaryHistory B ∧
                  UnaryHistory A ∧
                    UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
                      UnaryHistory N ∧ PkgSig bundle P pkg

theorem LocatedRealComparisonCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {L0 L1 W R0 R1 D0 D1 B A H C P N obligationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedRealComparisonCarrier L0 L1 W R0 R1 D0 D1 B A H C P N bundle pkg →
      Cont C N obligationRead →
        PkgSig bundle obligationRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row obligationRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row L0 ∨ hsame row L1 ∨ hsame row W ∨ hsame row R0 ∨
                  hsame row R1 ∨ hsame row D0 ∨ hsame row D1 ∨ hsame row B ∨
                    hsame row A ∨ hsame row obligationRead)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle obligationRead pkg)
              hsame ∧
            UnaryHistory obligationRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont SemanticNameCert UnaryHistory
  intro carrier replayRoute obligationPkg
  have cUnary : UnaryHistory C :=
    carrier.right.right.right.right.right.right.right.right.right.right.left
  have nUnary : UnaryHistory N :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right.left
  have pPkg : PkgSig bundle P pkg :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right.right
  have obligationUnary : UnaryHistory obligationRead :=
    unary_cont_closed cUnary nUnary replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row obligationRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row L0 ∨ hsame row L1 ∨ hsame row W ∨ hsame row R0 ∨
              hsame row R1 ∨ hsame row D0 ∨ hsame row D1 ∨ hsame row B ∨
                hsame row A ∨ hsame row obligationRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle obligationRead pkg)
          hsame := by
    refine
      { core :=
          { carrier_inhabited := ?_
            equiv_refl := ?_
            equiv_symm := ?_
            equiv_trans := ?_
            carrier_respects_equiv := ?_ }
        pattern_sound := ?_
        ledger_sound := ?_ }
    · exact ⟨obligationRead, hsame_refl obligationRead, obligationUnary⟩
    · intro row _source
      exact hsame_refl row
    · intro _row _other sameRows
      exact hsame_symm sameRows
    · intro _row _middle _other sameLeft sameRight
      exact hsame_trans sameLeft sameRight
    · intro _row _other sameRows source
      exact
        ⟨hsame_trans (hsame_symm sameRows) source.left,
          unary_transport source.right sameRows⟩
    · intro _row source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))))
    · intro _row source
      exact ⟨source.right, pPkg, obligationPkg⟩
  exact ⟨cert, obligationUnary⟩

end BEDC.Derived.LocatedRealComparisonUp
