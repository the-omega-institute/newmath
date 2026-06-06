import BEDC.Derived.SequentialClosureUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.SequentialClosureUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SequentialClosureCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {T M S Q L U W R A H C P N requestRead windowRead rationalRead sealRead replayRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    sequentialClosureFields (SequentialClosureUp.mk T M S Q L U W R A H C P N) =
        [T, M, S, Q, L, U, W, R, A, H, C, P, N] →
      UnaryHistory T →
      UnaryHistory U →
      UnaryHistory W →
      UnaryHistory R →
      UnaryHistory A →
      UnaryHistory C →
      Cont T U requestRead →
      Cont requestRead W windowRead →
      Cont windowRead R rationalRead →
      Cont rationalRead A sealRead →
      Cont sealRead C replayRead →
      PkgSig bundle P pkg →
      PkgSig bundle N pkg →
      SemanticNameCert
          (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row T ∨ hsame row M ∨ hsame row S ∨ hsame row Q ∨ hsame row L ∨
              hsame row U ∨ hsame row W ∨ hsame row R ∨ hsame row A ∨ hsame row H ∨
                hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row replayRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont T U requestRead ∧ Cont requestRead W windowRead ∧
              Cont windowRead R rationalRead ∧ Cont rationalRead A sealRead ∧
                Cont sealRead C replayRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame ∧
        UnaryHistory requestRead ∧ UnaryHistory windowRead ∧ UnaryHistory rationalRead ∧
          UnaryHistory sealRead ∧ UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro _fields tUnary uUnary wUnary rUnary aUnary cUnary tU requestW windowR rationalA
    sealC pPkg nPkg
  have requestUnary : UnaryHistory requestRead :=
    unary_cont_closed tUnary uUnary tU
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed requestUnary wUnary requestW
  have rationalUnary : UnaryHistory rationalRead :=
    unary_cont_closed windowUnary rUnary windowR
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed rationalUnary aUnary rationalA
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed sealUnary cUnary sealC
  have sourceAtReplay : hsame replayRead replayRead ∧ UnaryHistory replayRead :=
    And.intro (hsame_refl replayRead) replayUnary
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row T ∨ hsame row M ∨ hsame row S ∨ hsame row Q ∨ hsame row L ∨
              hsame row U ∨ hsame row W ∨ hsame row R ∨ hsame row A ∨ hsame row H ∨
                hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row replayRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont T U requestRead ∧ Cont requestRead W windowRead ∧
              Cont windowRead R rationalRead ∧ Cont rationalRead A sealRead ∧
                Cont sealRead C replayRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro replayRead sourceAtReplay
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
          And.intro
            (hsame_trans (hsame_symm sameRows) source.left)
            (unary_transport source.right sameRows)
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, tU, requestW, windowR, rationalA, sealC, pPkg, nPkg⟩
  }
  exact
    ⟨cert, requestUnary, windowUnary, rationalUnary, sealUnary, replayUnary⟩

end BEDC.Derived.SequentialClosureUp
