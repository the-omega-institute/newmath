import BEDC.Derived.PseudometricUp

namespace BEDC.Derived.PseudometricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PseudometricCarrier_separated_completion_source [AskSetup] [PackageSetup]
    {point distance dyadic stream readback sealRow zeroRow transport replay localName
      reflectionRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PseudometricCarrier point distance dyadic stream readback sealRow zeroRow transport
        replay localName bundle pkg →
      Cont zeroRow transport reflectionRead →
        Cont reflectionRead replay completionRead →
          PkgSig bundle completionRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row point ∨ hsame row distance ∨ hsame row dyadic ∨
                    hsame row stream ∨ hsame row readback ∨ hsame row sealRow ∨
                      hsame row zeroRow ∨ hsame row reflectionRead ∨
                        hsame row completionRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle localName pkg ∧
                    PkgSig bundle completionRead pkg)
                hsame ∧
              UnaryHistory reflectionRead ∧ UnaryHistory completionRead ∧
                Cont stream readback dyadic ∧ Cont dyadic sealRow zeroRow ∧
                  PkgSig bundle localName pkg ∧ PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: PseudometricCarrier BHist ProbeBundle Pkg Cont SemanticNameCert
  intro carrier reflectionRoute completionRoute completionPkg
  obtain ⟨_pointUnary, _distanceUnary, _dyadicUnary, streamUnary, readbackUnary,
    sealUnary, zeroUnary, transportUnary, replayUnary, _localNameUnary,
    streamReadbackDyadic, dyadicSealZero, _localNameZero, localNamePkg⟩ := carrier
  have reflectionUnary : UnaryHistory reflectionRead :=
    unary_cont_closed zeroUnary transportUnary reflectionRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed reflectionUnary replayUnary completionRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row point ∨ hsame row distance ∨ hsame row dyadic ∨
              hsame row stream ∨ hsame row readback ∨ hsame row sealRow ∨
                hsame row zeroRow ∨ hsame row reflectionRead ∨ hsame row completionRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle localName pkg ∧
              PkgSig bundle completionRead pkg)
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
      exact ⟨source.right, localNamePkg, completionPkg⟩
  }
  exact
    ⟨cert, reflectionUnary, completionUnary, streamReadbackDyadic, dyadicSealZero,
      localNamePkg, completionPkg⟩

end BEDC.Derived.PseudometricUp
