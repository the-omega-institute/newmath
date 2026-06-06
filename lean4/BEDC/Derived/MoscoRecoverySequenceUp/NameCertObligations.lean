import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MoscoRecoverySequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MoscoRecoverySequenceCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {X F W A G Q E M H C P N recoveryWindow valueWindow realSeal completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory X ->
      UnaryHistory F ->
        UnaryHistory W ->
          UnaryHistory A ->
            UnaryHistory G ->
              UnaryHistory Q ->
                UnaryHistory E ->
                  UnaryHistory M ->
                    UnaryHistory N ->
                      Cont A G recoveryWindow ->
                        Cont recoveryWindow Q valueWindow ->
                          Cont valueWindow E realSeal ->
                            Cont realSeal M completionRead ->
                              PkgSig bundle P pkg ->
                                PkgSig bundle N pkg ->
                                  SemanticNameCert
                                      (fun row : BHist => hsame row N ∧ UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row X ∨ hsame row F ∨ hsame row W ∨
                                          hsame row A ∨ hsame row G ∨ hsame row Q ∨
                                            hsame row E ∨ hsame row M ∨ hsame row H ∨
                                              hsame row C ∨ hsame row P ∨ hsame row N ∨
                                                hsame row completionRead)
                                      (fun row : BHist =>
                                        UnaryHistory row ∧ Cont A G recoveryWindow ∧
                                          Cont recoveryWindow Q valueWindow ∧
                                            Cont valueWindow E realSeal ∧
                                              Cont realSeal M completionRead ∧
                                                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                                      hsame ∧
                                    UnaryHistory recoveryWindow ∧ UnaryHistory valueWindow ∧
                                      UnaryHistory realSeal ∧ UnaryHistory completionRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert ProbeBundle Pkg PkgSig UnaryHistory
  intro _unaryX _unaryF _unaryW unaryA unaryG unaryQ unaryE unaryM unaryN recoveryRoute
    valueRoute realRoute completionRoute provenancePkg localNamePkg
  have recoveryUnary : UnaryHistory recoveryWindow :=
    unary_cont_closed unaryA unaryG recoveryRoute
  have valueUnary : UnaryHistory valueWindow :=
    unary_cont_closed recoveryUnary unaryQ valueRoute
  have realUnary : UnaryHistory realSeal :=
    unary_cont_closed valueUnary unaryE realRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed realUnary unaryM completionRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row N ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row F ∨ hsame row W ∨ hsame row A ∨ hsame row G ∨
              hsame row Q ∨ hsame row E ∨ hsame row M ∨ hsame row H ∨ hsame row C ∨
                hsame row P ∨ hsame row N ∨ hsame row completionRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont A G recoveryWindow ∧
              Cont recoveryWindow Q valueWindow ∧ Cont valueWindow E realSeal ∧
                Cont realSeal M completionRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro N ⟨hsame_refl N, unaryN⟩
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
      right
      right
      left
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, recoveryRoute, valueRoute, realRoute, completionRoute, provenancePkg,
          localNamePkg⟩
  }
  exact ⟨cert, recoveryUnary, valueUnary, realUnary, completionUnary⟩

end BEDC.Derived.MoscoRecoverySequenceUp
