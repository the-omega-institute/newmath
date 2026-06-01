import BEDC.Derived.PseudometricUp

namespace BEDC.Derived.PseudometricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PseudometricCarrier_zero_distance_source_reflection [AskSetup] [PackageSetup]
    {point distance dyadic stream readback sealRow zeroRow transport replay localName
      zeroBoundaryRead ledgerRead preseparatedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PseudometricCarrier point distance dyadic stream readback sealRow zeroRow transport
        replay localName bundle pkg →
      Cont zeroRow transport zeroBoundaryRead →
        Cont zeroBoundaryRead replay ledgerRead →
          Cont ledgerRead readback preseparatedRead →
            PkgSig bundle zeroBoundaryRead pkg →
              PkgSig bundle ledgerRead pkg →
                PkgSig bundle preseparatedRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row preseparatedRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row zeroBoundaryRead ∨ hsame row ledgerRead ∨
                          hsame row preseparatedRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ PkgSig bundle preseparatedRead pkg ∧
                          PkgSig bundle localName pkg)
                      hsame ∧
                    UnaryHistory zeroBoundaryRead ∧ UnaryHistory ledgerRead ∧
                      UnaryHistory preseparatedRead ∧ Cont stream readback dyadic ∧
                        Cont dyadic sealRow zeroRow := by
  -- BEDC touchpoint anchor: PseudometricCarrier BHist ProbeBundle Pkg Cont SemanticNameCert
  intro carrier zeroBoundaryRoute ledgerRoute preseparatedRoute _zeroBoundaryPkg
  intro _ledgerPkg preseparatedPkg
  obtain ⟨_pointUnary, _distanceUnary, _dyadicUnary, streamUnary, readbackUnary,
    sealUnary, zeroUnary, transportUnary, replayUnary, _localNameUnary, streamReadbackDyadic,
    dyadicSealZero, _localNameZero, localNamePkg⟩ := carrier
  have zeroBoundaryUnary : UnaryHistory zeroBoundaryRead :=
    unary_cont_closed zeroUnary transportUnary zeroBoundaryRoute
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed zeroBoundaryUnary replayUnary ledgerRoute
  have preseparatedUnary : UnaryHistory preseparatedRead :=
    unary_cont_closed ledgerUnary readbackUnary preseparatedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row preseparatedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row zeroBoundaryRead ∨ hsame row ledgerRead ∨
              hsame row preseparatedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle preseparatedRead pkg ∧
              PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro preseparatedRead ⟨hsame_refl preseparatedRead, preseparatedUnary⟩
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
      exact ⟨source.right, preseparatedPkg, localNamePkg⟩
  }
  exact
    ⟨cert, zeroBoundaryUnary, ledgerUnary, preseparatedUnary, streamReadbackDyadic,
      dyadicSealZero⟩

end BEDC.Derived.PseudometricUp
