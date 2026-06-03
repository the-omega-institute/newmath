import BEDC.Derived.RegularCauchySeparationUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchySeparationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchySeparationCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {L R W D M E H C P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory L →
      UnaryHistory R →
        UnaryHistory W →
          UnaryHistory D →
            UnaryHistory M →
              UnaryHistory E →
                UnaryHistory H →
                  UnaryHistory C →
                    UnaryHistory P →
                      UnaryHistory N →
                        PkgSig bundle P pkg →
                          PkgSig bundle N pkg →
                            SemanticNameCert
                                  (fun row : BHist => hsame row N ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row L ∨ hsame row R ∨ hsame row W ∨
                                      hsame row D ∨ hsame row M ∨ hsame row E ∨
                                        hsame row H ∨ hsame row C ∨ hsame row P ∨
                                          hsame row N)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ PkgSig bundle P pkg ∧
                                      PkgSig bundle N pkg)
                                  hsame ∧
                                UnaryHistory L ∧ UnaryHistory R ∧ UnaryHistory W ∧
                                  UnaryHistory D ∧ UnaryHistory M ∧ UnaryHistory E ∧
                                    PkgSig bundle P pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame SemanticNameCert UnaryHistory
  intro lUnary rUnary wUnary dUnary mUnary eUnary _hUnary _cUnary pUnary nUnary pPkg
    nPkg
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row N ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row L ∨ hsame row R ∨ hsame row W ∨ hsame row D ∨
              hsame row M ∨ hsame row E ∨ hsame row H ∨ hsame row C ∨
                hsame row P ∨ hsame row N)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro N ⟨hsame_refl N, nUnary⟩
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
      right
      right
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, pPkg, nPkg⟩
  }
  exact
    ⟨cert, lUnary, rUnary, wUnary, dUnary, mUnary, eUnary, pPkg, nPkg⟩

end BEDC.Derived.RegularCauchySeparationUp
