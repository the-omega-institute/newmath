import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SequentialCompletenessCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def SequentialCompletenessCriterionCarrier [AskSetup] [PackageSetup]
    (S C R M W G E H T P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  UnaryHistory S ∧ UnaryHistory C ∧ UnaryHistory R ∧ UnaryHistory M ∧
    UnaryHistory W ∧ UnaryHistory G ∧ UnaryHistory E ∧ UnaryHistory H ∧
      UnaryHistory T ∧ UnaryHistory P ∧ UnaryHistory N ∧ Cont S C W ∧
        Cont W G E ∧ Cont R M E ∧ hsame H T ∧ PkgSig bundle P pkg

theorem SequentialCompletenessCriterionCarrier_namecert_obligations
    [AskSetup] [PackageSetup]
    {S C R M W G E H T P N : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SequentialCompletenessCriterionCarrier S C R M W G E H T P N bundle pkg →
      SemanticNameCert
        (fun row : BHist =>
          SequentialCompletenessCriterionCarrier S C R M W G E H T P N bundle pkg ∧
            hsame row N)
        (fun row : BHist =>
          hsame row N ∧ Cont S C W ∧ Cont W G E ∧ Cont R M E)
        (fun row : BHist => hsame row N ∧ PkgSig bundle P pkg)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier
  have carrierWitness :
      SequentialCompletenessCriterionCarrier S C R M W G E H T P N bundle pkg :=
    carrier
  obtain ⟨_SUnary, _CUnary, _RUnary, _MUnary, _WUnary, _GUnary, _EUnary,
    _HUnary, _TUnary, _PUnary, _NUnary, sequenceWindow, windowSeal,
    realMetricSeal, _transportSame, provenancePkg⟩ := carrier
  exact {
    core := {
      carrier_inhabited := Exists.intro N ⟨carrierWitness, hsame_refl N⟩
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
        exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact ⟨source.right, sequenceWindow, windowSeal, realMetricSeal⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg⟩
  }

end BEDC.Derived.SequentialCompletenessCriterionUp
