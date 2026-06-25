import BEDC.Derived.MetaCICParallelDiamondWitnessUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MetaCICParallelDiamondWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def MetaCICParallelDiamondWitnessCarrier [AskSetup] [PackageSetup]
    (T L R S J B A O H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  UnaryHistory T ∧ UnaryHistory L ∧ UnaryHistory R ∧ UnaryHistory S ∧
    UnaryHistory J ∧ UnaryHistory B ∧ UnaryHistory A ∧ UnaryHistory O ∧
      UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
        PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem MetaCICParallelDiamondWitnessHandoff [AskSetup] [PackageSetup]
    {T L R S J B A O H C P N peakRead joinRead handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICParallelDiamondWitnessCarrier T L R S J B A O H C P N bundle pkg ->
      Cont L R peakRead ->
        Cont peakRead S joinRead ->
          Cont joinRead C handoffRead ->
            PkgSig bundle handoffRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row T ∨ hsame row L ∨ hsame row R ∨ hsame row S ∨
                      hsame row J ∨ hsame row B ∨ hsame row A ∨ hsame row O ∨
                        hsame row handoffRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont L R peakRead ∧
                      Cont peakRead S joinRead ∧ Cont joinRead C handoffRead ∧
                        PkgSig bundle handoffRead pkg)
                  hsame ∧
                UnaryHistory peakRead ∧ UnaryHistory joinRead ∧
                  UnaryHistory handoffRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier peakRoute joinRoute handoffRoute handoffPkg
  obtain ⟨_tUnary, lUnary, rUnary, sUnary, _jUnary, _bUnary, _aUnary, _oUnary,
    _hUnary, cUnary, _pUnary, _nUnary, _provenancePkg, _namePkg⟩ := carrier
  have peakUnary : UnaryHistory peakRead :=
    unary_cont_closed lUnary rUnary peakRoute
  have joinUnary : UnaryHistory joinRead :=
    unary_cont_closed peakUnary sUnary joinRoute
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed joinUnary cUnary handoffRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row T ∨ hsame row L ∨ hsame row R ∨ hsame row S ∨ hsame row J ∨
              hsame row B ∨ hsame row A ∨ hsame row O ∨ hsame row handoffRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont L R peakRead ∧ Cont peakRead S joinRead ∧
              Cont joinRead C handoffRead ∧ PkgSig bundle handoffRead pkg)
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, peakRoute, joinRoute, handoffRoute, handoffPkg⟩
  }
  exact ⟨cert, peakUnary, joinUnary, handoffUnary⟩

end BEDC.Derived.MetaCICParallelDiamondWitnessUp
