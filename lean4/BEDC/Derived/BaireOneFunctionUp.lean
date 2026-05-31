import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BaireOneFunctionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BaireOneFunctionCarrier [AskSetup] [PackageSetup]
    (X F S Q R L H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  UnaryHistory X ∧ UnaryHistory F ∧ UnaryHistory S ∧ UnaryHistory Q ∧
    UnaryHistory R ∧ UnaryHistory L ∧ UnaryHistory H ∧ UnaryHistory C ∧
      UnaryHistory P ∧ UnaryHistory N ∧ Cont X F S ∧ Cont S Q R ∧
        Cont R L H ∧ Cont H C P ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem BaireOneFunctionCarrier_namecert_obligation_surface [AskSetup] [PackageSetup]
    {X F S Q R L H C P N endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireOneFunctionCarrier X F S Q R L H C P N bundle pkg →
      Cont S Q endpoint →
        PkgSig bundle endpoint pkg →
          SemanticNameCert
              (fun row : BHist =>
                hsame row endpoint ∧
                  BaireOneFunctionCarrier X F S Q R L H C P N bundle pkg)
              (fun row : BHist =>
                hsame row X ∨ hsame row F ∨ hsame row S ∨ hsame row Q ∨
                  hsame row R ∨ hsame row L ∨ hsame row H ∨ hsame row C ∨
                    hsame row P ∨ hsame row N ∨ hsame row endpoint)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle endpoint pkg)
              hsame ∧
            UnaryHistory endpoint := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier scheduleReadbackEndpoint endpointPkg
  have carrierWhole := carrier
  obtain ⟨_sourceUnary, _approximantsUnary, scheduleUnary, readbackUnary, _realUnary,
    _handoffUnary, _transportUnary, _continuationUnary, _provenanceUnary, _nameUnary,
    _sourceApproxSchedule, _scheduleReadbackReal, _realHandoffTransport,
    _transportContinuationProvenance, provenancePkg, _namePkg⟩ := carrier
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed scheduleUnary readbackUnary scheduleReadbackEndpoint
  have sourceEndpoint :
      (fun row : BHist =>
        hsame row endpoint ∧
          BaireOneFunctionCarrier X F S Q R L H C P N bundle pkg) endpoint := by
    exact ⟨hsame_refl endpoint, carrierWhole⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row endpoint ∧
              BaireOneFunctionCarrier X F S Q R L H C P N bundle pkg)
          (fun row : BHist =>
            hsame row X ∨ hsame row F ∨ hsame row S ∨ hsame row Q ∨ hsame row R ∨
              hsame row L ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row N ∨ hsame row endpoint)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle endpoint pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint sourceEndpoint
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
        exact ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr (Or.inr (Or.inr source.left)))))))))
    ledger_sound := by
      intro row source
      exact
        ⟨unary_transport endpointUnary (hsame_symm source.left), provenancePkg,
          endpointPkg⟩
  }
  exact ⟨cert, endpointUnary⟩

theorem BaireOneFunctionCarrier_pointwise_limit_ledger [AskSetup] [PackageSetup]
    {X F S Q R L H C P N : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireOneFunctionCarrier X F S Q R L H C P N bundle pkg ->
      SemanticNameCert
          (fun row : BHist => hsame row R ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row F ∨ hsame row S ∨ hsame row Q ∨ hsame row R)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle P pkg ∧ Cont S Q R)
          hsame ∧
        UnaryHistory R ∧ Cont S Q R := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle SemanticNameCert hsame UnaryHistory
  intro carrier
  obtain ⟨_sourceUnary, _approximantsUnary, scheduleUnary, readbackUnary, _realUnary,
    _handoffUnary, _transportUnary, _continuationUnary, _provenanceUnary, _nameUnary,
    _sourceApproxSchedule, scheduleReadbackReal, _realHandoffTransport,
    _transportContinuationProvenance, provenancePkg, _namePkg⟩ := carrier
  have realUnary : UnaryHistory R :=
    unary_cont_closed scheduleUnary readbackUnary scheduleReadbackReal
  have sourceReal :
      (fun row : BHist => hsame row R ∧ UnaryHistory row) R := by
    exact ⟨hsame_refl R, realUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row R ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row F ∨ hsame row S ∨ hsame row Q ∨ hsame row R)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle P pkg ∧ Cont S Q R)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro R sourceReal
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, scheduleReadbackReal⟩
  }
  exact ⟨cert, realUnary, scheduleReadbackReal⟩

end BEDC.Derived.BaireOneFunctionUp
