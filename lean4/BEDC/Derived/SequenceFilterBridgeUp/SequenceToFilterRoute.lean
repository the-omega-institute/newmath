import BEDC.Derived.SequenceFilterBridgeUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SequenceFilterBridgeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SequenceFilterBridgeSequenceToFilterRoute [AskSetup] [PackageSetup]
    {S F Q T R E H C P N sequenceWindow filterRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory S →
      UnaryHistory T →
        UnaryHistory R →
          UnaryHistory F →
            UnaryHistory Q →
              Cont S T sequenceWindow →
                Cont sequenceWindow R filterRead →
                  Cont filterRead F completionRead →
                    PkgSig bundle P pkg →
                      PkgSig bundle N pkg →
                        SemanticNameCert
                          (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row S ∨ hsame row T ∨ hsame row R ∨ hsame row F ∨
                              hsame row Q ∨ hsame row completionRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont S T sequenceWindow ∧
                              Cont sequenceWindow R filterRead ∧
                                Cont filterRead F completionRead ∧
                                  PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                          hsame ∧
                          UnaryHistory sequenceWindow ∧ UnaryHistory filterRead ∧
                            UnaryHistory completionRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro sUnary tUnary rUnary fUnary _qUnary sequenceRoute filterRoute completionRoute
    packageP packageN
  have sequenceUnary : UnaryHistory sequenceWindow :=
    unary_cont_closed sUnary tUnary sequenceRoute
  have filterUnary : UnaryHistory filterRead :=
    unary_cont_closed sequenceUnary rUnary filterRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed filterUnary fUnary completionRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row S ∨ hsame row T ∨ hsame row R ∨ hsame row F ∨ hsame row Q ∨
            hsame row completionRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont S T sequenceWindow ∧ Cont sequenceWindow R filterRead ∧
            Cont filterRead F completionRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro completionRead ⟨hsame_refl completionRead, completionUnary⟩
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
      exact
        ⟨source.right, sequenceRoute, filterRoute, completionRoute, packageP, packageN⟩
  }
  exact ⟨cert, sequenceUnary, filterUnary, completionUnary⟩

end BEDC.Derived.SequenceFilterBridgeUp
