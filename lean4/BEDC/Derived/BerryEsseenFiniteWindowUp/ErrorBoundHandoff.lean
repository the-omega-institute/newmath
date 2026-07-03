import BEDC.Derived.BerryEsseenFiniteWindowUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BerryEsseenFiniteWindowUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BerryEsseenFiniteWindowErrorBoundHandoff [AskSetup] [PackageSetup]
    {C L D R E G H K P N clRead distributionRead regseqRead realRead gaussianRead
      transportRead replayRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory C → UnaryHistory L → UnaryHistory D → UnaryHistory R →
      UnaryHistory E → UnaryHistory G → UnaryHistory H → UnaryHistory K →
        UnaryHistory P → UnaryHistory N →
          Cont C L clRead →
            Cont clRead D distributionRead →
              Cont distributionRead R regseqRead →
                Cont regseqRead E realRead →
                  Cont realRead G gaussianRead →
                    Cont gaussianRead H transportRead →
                      Cont transportRead K replayRead →
                        Cont replayRead P namedRead →
                          PkgSig bundle P pkg →
                            PkgSig bundle N pkg →
                              SemanticNameCert
                                  (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row C ∨ hsame row L ∨ hsame row D ∨
                                      hsame row R ∨ hsame row E ∨ hsame row G ∨
                                        hsame row H ∨ hsame row K ∨ hsame row P ∨
                                          hsame row N ∨ hsame row namedRead)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ Cont C L clRead ∧
                                      Cont clRead D distributionRead ∧
                                        Cont distributionRead R regseqRead ∧
                                          Cont regseqRead E realRead ∧
                                            Cont realRead G gaussianRead ∧
                                              Cont gaussianRead H transportRead ∧
                                                Cont transportRead K replayRead ∧
                                                  Cont replayRead P namedRead ∧
                                                    PkgSig bundle P pkg ∧
                                                      PkgSig bundle N pkg)
                                  hsame ∧
                                UnaryHistory clRead ∧ UnaryHistory distributionRead ∧
                                  UnaryHistory regseqRead ∧ UnaryHistory realRead ∧
                                    UnaryHistory gaussianRead ∧ UnaryHistory transportRead ∧
                                      UnaryHistory replayRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig SemanticNameCert hsame UnaryHistory
  intro cUnary lUnary dUnary rUnary eUnary gUnary hUnary kUnary pUnary _nUnary
  intro clRoute distributionRoute regseqRoute realRoute gaussianRoute transportRoute replayRoute
  intro namedRoute pPkg nPkg
  have clUnary : UnaryHistory clRead :=
    unary_cont_closed cUnary lUnary clRoute
  have distributionUnary : UnaryHistory distributionRead :=
    unary_cont_closed clUnary dUnary distributionRoute
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed distributionUnary rUnary regseqRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed regseqUnary eUnary realRoute
  have gaussianUnary : UnaryHistory gaussianRead :=
    unary_cont_closed realUnary gUnary gaussianRoute
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed gaussianUnary hUnary transportRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed transportUnary kUnary replayRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed replayUnary pUnary namedRoute
  have sourceAtNamed :
      (fun row : BHist => hsame row namedRead ∧ UnaryHistory row) namedRead := by
    exact ⟨hsame_refl namedRead, namedUnary⟩
  have core :
      NameCert (fun row : BHist => hsame row namedRead ∧ UnaryHistory row) hsame := by
    exact {
      carrier_inhabited := Exists.intro namedRead sourceAtNamed
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
        intro _row other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row C ∨ hsame row L ∨ hsame row D ∨ hsame row R ∨
            hsame row E ∨ hsame row G ∨ hsame row H ∨ hsame row K ∨
              hsame row P ∨ hsame row N ∨ hsame row namedRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont C L clRead ∧ Cont clRead D distributionRead ∧
            Cont distributionRead R regseqRead ∧ Cont regseqRead E realRead ∧
              Cont realRead G gaussianRead ∧ Cont gaussianRead H transportRead ∧
                Cont transportRead K replayRead ∧ Cont replayRead P namedRead ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
        hsame := by
    exact {
      core := core
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr source.left)))))))))
      ledger_sound := by
        intro _row source
        exact
          ⟨source.right, clRoute, distributionRoute, regseqRoute, realRoute,
            gaussianRoute, transportRoute, replayRoute, namedRoute, pPkg, nPkg⟩
    }
  exact
    ⟨cert, clUnary, distributionUnary, regseqUnary, realUnary, gaussianUnary,
      transportUnary, replayUnary, namedUnary⟩

end BEDC.Derived.BerryEsseenFiniteWindowUp
