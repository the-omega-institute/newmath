import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MetaCICConfluenceDiamondLedgerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def MetaCICConfluenceDiamondLedgerCarrier [AskSetup] [PackageSetup]
    (T R J B O X H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory T ∧
    UnaryHistory R ∧
      UnaryHistory J ∧
        UnaryHistory B ∧
          UnaryHistory O ∧
            UnaryHistory X ∧
              UnaryHistory H ∧
                UnaryHistory C ∧
                  UnaryHistory P ∧
                    UnaryHistory N ∧
                      Cont T R J ∧
                        Cont J B O ∧
                          Cont O X C ∧ PkgSig bundle P pkg

theorem MetaCICConfluenceDiamondLedgerNameCertObligations [AskSetup] [PackageSetup]
    {T R J B O X H C P N handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICConfluenceDiamondLedgerCarrier T R J B O X H C P N bundle pkg →
      Cont X C handoffRead →
        PkgSig bundle handoffRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
              (fun row : BHist => hsame row handoffRead ∧ Cont X C handoffRead)
              (fun row : BHist => hsame row handoffRead ∧ PkgSig bundle handoffRead pkg)
              hsame ∧
            UnaryHistory T ∧
              UnaryHistory R ∧
                UnaryHistory J ∧
                  UnaryHistory B ∧
                    UnaryHistory O ∧
                      UnaryHistory X ∧
                        UnaryHistory H ∧
                          UnaryHistory C ∧
                            UnaryHistory P ∧
                              UnaryHistory N ∧
                                UnaryHistory handoffRead ∧
                                  Cont T R J ∧
                                    Cont J B O ∧
                                      Cont O X C ∧
                                        Cont X C handoffRead ∧
                                          PkgSig bundle P pkg ∧
                                            PkgSig bundle handoffRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier handoffRoute handoffPkg
  obtain ⟨tUnary, rUnary, jUnary, bUnary, oUnary, xUnary, hUnary, cUnary, pUnary,
    nUnary, typedResidualLocalJoin, joinBudgetObstruction, obstructionHandoffReplay,
    provenancePkg⟩ := carrier
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed xUnary cUnary handoffRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row handoffRead ∧ Cont X C handoffRead)
          (fun row : BHist => hsame row handoffRead ∧ PkgSig bundle handoffRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro handoffRead ⟨hsame_refl handoffRead, handoffUnary⟩
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
      exact ⟨source.left, handoffRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, handoffPkg⟩
  }
  exact
    ⟨cert, tUnary, rUnary, jUnary, bUnary, oUnary, xUnary, hUnary, cUnary, pUnary,
      nUnary, handoffUnary, typedResidualLocalJoin, joinBudgetObstruction,
      obstructionHandoffReplay, handoffRoute, provenancePkg, handoffPkg⟩

end BEDC.Derived.MetaCICConfluenceDiamondLedgerUp
