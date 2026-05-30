import BEDC.Derived.PseudometricUp
import BEDC.FKernel.Cont

namespace BEDC.Derived.PseudometricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PseudometricCarrier_zero_distance_completion_route [AskSetup] [PackageSetup]
    {point distance dyadic stream readback sealRow zeroRow transport replay localName zeroRead
      completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PseudometricCarrier point distance dyadic stream readback sealRow zeroRow transport replay
        localName bundle pkg ->
      Cont zeroRow transport zeroRead ->
        Cont zeroRead replay completionRead ->
          PkgSig bundle completionRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row zeroRow ∨ hsame row zeroRead ∨ hsame row completionRead)
                (fun row : BHist => UnaryHistory row ∧ PkgSig bundle completionRead pkg)
                hsame ∧
              UnaryHistory zeroRead ∧ UnaryHistory completionRead ∧
                Cont stream readback dyadic ∧ Cont dyadic sealRow zeroRow ∧
                  Cont zeroRow transport zeroRead ∧ Cont zeroRead replay completionRead ∧
                    PkgSig bundle localName pkg ∧ PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: PseudometricCarrier BHist Cont ProbeBundle PkgSig SemanticNameCert
  intro carrier zeroTransportRead readCompletion completionPkg
  obtain ⟨_pointUnary, _distanceUnary, _dyadicUnary, streamUnary, _readbackUnary,
    _sealUnary, zeroUnary, transportUnary, replayUnary, _localNameUnary,
    streamReadbackDyadic, dyadicSealZero, _localNameZero, localNamePkg⟩ := carrier
  have zeroReadUnary : UnaryHistory zeroRead :=
    unary_cont_closed zeroUnary transportUnary zeroTransportRead
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed zeroReadUnary replayUnary readCompletion
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row zeroRow ∨ hsame row zeroRead ∨ hsame row completionRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle completionRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro completionRead ⟨hsame_refl completionRead, completionReadUnary⟩
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
      exact Or.inr (Or.inr source.left)
    ledger_sound := by
      intro _row source
      exact ⟨source.right, completionPkg⟩
  }
  exact
    ⟨cert, zeroReadUnary, completionReadUnary, streamReadbackDyadic, dyadicSealZero,
      zeroTransportRead, readCompletion, localNamePkg, completionPkg⟩

end BEDC.Derived.PseudometricUp
