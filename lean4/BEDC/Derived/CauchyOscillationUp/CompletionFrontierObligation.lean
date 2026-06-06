import BEDC.Derived.CauchyOscillationUp

namespace BEDC.Derived.CauchyOscillationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyOscillationCarrier_completion_frontier_obligation [AskSetup] [PackageSetup]
    {W M Q T S H C P N frontierRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyOscillationCarrier W M Q T S H C P N bundle pkg ->
      Cont W M frontierRead ->
        Cont frontierRead Q T ->
          Cont T S sealRead ->
            PkgSig bundle sealRead pkg ->
              UnaryHistory frontierRead ∧ UnaryHistory sealRead ∧ Cont W M frontierRead ∧
                Cont frontierRead Q T ∧ Cont T S sealRead ∧ PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: CauchyOscillationCarrier BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier frontierRoute frontierTolerance sealRoute sealPkg
  obtain ⟨wUnary, mUnary, qUnary, _tUnary, sUnary, _hUnary, _cUnary, _pUnary, _nUnary,
    _carrierWMQ, _carrierMQT, _carrierTS, _carrierCN, _carrierPkg⟩ := carrier
  have frontierUnary : UnaryHistory frontierRead :=
    unary_cont_closed wUnary mUnary frontierRoute
  have tUnaryFromFrontier : UnaryHistory T :=
    unary_cont_closed frontierUnary qUnary frontierTolerance
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed tUnaryFromFrontier sUnary sealRoute
  exact
    ⟨frontierUnary, sealUnary, frontierRoute, frontierTolerance, sealRoute, sealPkg⟩

theorem CauchyOscillationCompletionFrontierObligation [AskSetup] [PackageSetup]
    {W M Q T S H C P N : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyOscillationCarrier W M Q T S H C P N bundle pkg ->
      SemanticNameCert
            (fun row : BHist =>
              hsame row P ∧ CauchyOscillationCarrier W M Q T S H C P N bundle pkg)
            (fun row : BHist =>
              hsame row W ∨ hsame row M ∨ hsame row Q ∨ hsame row T ∨
                hsame row S ∨ hsame row P)
            (fun row : BHist =>
              hsame row P ∧ Cont W M Q ∧ Cont M Q T ∧ Cont T S C ∧
                PkgSig bundle P pkg)
            hsame ∧
        UnaryHistory W ∧ UnaryHistory M ∧ UnaryHistory Q ∧ UnaryHistory T ∧
          UnaryHistory S ∧ Cont W M Q ∧ Cont M Q T ∧ Cont T S C ∧
            PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: CauchyOscillationCarrier BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro carrier
  have carrierRows :
      CauchyOscillationCarrier W M Q T S H C P N bundle pkg :=
    carrier
  obtain ⟨wUnary, mUnary, qUnary, tUnary, sUnary, _hUnary, _cUnary, _pUnary, _nUnary,
    tailModulus, modulusTolerance, ledgerSeal, _routesNameCert, provenancePkg⟩ := carrier
  have sourceP :
      (fun row : BHist =>
        hsame row P ∧ CauchyOscillationCarrier W M Q T S H C P N bundle pkg) P := by
    exact ⟨hsame_refl P, carrierRows⟩
  have core :
      NameCert
        (fun row : BHist =>
          hsame row P ∧ CauchyOscillationCarrier W M Q T S H C P N bundle pkg)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro P sourceP
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
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row P ∧ CauchyOscillationCarrier W M Q T S H C P N bundle pkg)
          (fun row : BHist =>
            hsame row W ∨ hsame row M ∨ hsame row Q ∨ hsame row T ∨
              hsame row S ∨ hsame row P)
          (fun row : BHist =>
            hsame row P ∧ Cont W M Q ∧ Cont M Q T ∧ Cont T S C ∧
              PkgSig bundle P pkg)
          hsame := by
    exact {
      core := core
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
      ledger_sound := by
        intro _row source
        exact ⟨source.left, tailModulus, modulusTolerance, ledgerSeal, provenancePkg⟩
    }
  exact
    ⟨cert, wUnary, mUnary, qUnary, tUnary, sUnary, tailModulus, modulusTolerance,
      ledgerSeal, provenancePkg⟩

theorem CauchyOscillationCompletionSourceExhaustion [AskSetup] [PackageSetup]
    {W M Q T S H C P N sourceRead sealRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyOscillationCarrier W M Q T S H C P N bundle pkg -> Cont W M sourceRead ->
      Cont sourceRead Q sealRead -> Cont sealRead S completionRead ->
        PkgSig bundle completionRead pkg -> SemanticNameCert
          (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row W ∨ hsame row M ∨ hsame row Q ∨ hsame row T ∨ hsame row S ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row sourceRead ∨ hsame row sealRead ∨ hsame row completionRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W M sourceRead ∧ Cont sourceRead Q sealRead ∧
              Cont sealRead S completionRead ∧ PkgSig bundle completionRead pkg)
          hsame ∧ UnaryHistory sourceRead ∧ UnaryHistory sealRead ∧
            UnaryHistory completionRead := by
  -- BEDC touchpoint anchor: CauchyOscillationCarrier BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro carrier sourceRoute sealRoute completionRoute completionPkg
  obtain ⟨wUnary, mUnary, qUnary, _tUnary, sUnary, _hUnary, _cUnary, _pUnary,
    _nUnary, _tailModulusTolerance, _modulusToleranceLedger, _ledgerSeal,
    _routesNameCert, _carrierPkg⟩ := carrier
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed wUnary mUnary sourceRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed sourceUnary qUnary sealRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed sealUnary sUnary completionRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row W ∨ hsame row M ∨ hsame row Q ∨ hsame row T ∨ hsame row S ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row sourceRead ∨ hsame row sealRead ∨ hsame row completionRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W M sourceRead ∧ Cont sourceRead Q sealRead ∧
              Cont sealRead S completionRead ∧ PkgSig bundle completionRead pkg)
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr source.left))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, sourceRoute, sealRoute, completionRoute, completionPkg⟩
  }
  exact ⟨cert, sourceUnary, sealUnary, completionUnary⟩

end BEDC.Derived.CauchyOscillationUp
