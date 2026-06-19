import BEDC.Derived.MetaCICBetaAuditUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MetaCICBetaAuditUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICBetaAuditReductionConversionBoundary [AskSetup] [PackageSetup]
    {S V T F O H C P N reductionRead conversionRead rigidityRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory S →
      UnaryHistory V →
        UnaryHistory T →
          UnaryHistory F →
            Cont S T reductionRead →
              Cont V T conversionRead →
                Cont conversionRead F rigidityRead →
                  PkgSig bundle P pkg →
                    PkgSig bundle N pkg →
                      SemanticNameCert
                          (fun row : BHist => hsame row rigidityRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row S ∨ hsame row V ∨ hsame row T ∨ hsame row F ∨
                              hsame row O ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                                hsame row N ∨ hsame row rigidityRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont S T reductionRead ∧
                              Cont V T conversionRead ∧
                                Cont conversionRead F rigidityRead ∧
                                  PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                          hsame ∧
                        UnaryHistory reductionRead ∧ UnaryHistory conversionRead ∧
                          UnaryHistory rigidityRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro sUnary vUnary tUnary fUnary reductionRoute conversionRoute rigidityRoute
    provenancePkg namePkg
  have reductionUnary : UnaryHistory reductionRead :=
    unary_cont_closed sUnary tUnary reductionRoute
  have conversionUnary : UnaryHistory conversionRead :=
    unary_cont_closed vUnary tUnary conversionRoute
  have rigidityUnary : UnaryHistory rigidityRead :=
    unary_cont_closed conversionUnary fUnary rigidityRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row rigidityRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row V ∨ hsame row T ∨ hsame row F ∨ hsame row O ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row rigidityRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S T reductionRead ∧ Cont V T conversionRead ∧
              Cont conversionRead F rigidityRead ∧ PkgSig bundle P pkg ∧
                PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro rigidityRead ⟨hsame_refl rigidityRead, rigidityUnary⟩
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
      exact
        ⟨source.right, reductionRoute, conversionRoute, rigidityRoute, provenancePkg,
          namePkg⟩
  }
  exact ⟨cert, reductionUnary, conversionUnary, rigidityUnary⟩

end BEDC.Derived.MetaCICBetaAuditUp
