import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ImplicitFunctionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ImplicitFunctionCarrier [AskSetup] [PackageSetup]
    (equation base derivative linear matrix picard graph sealRow transport replay provenance
      localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory equation ∧ UnaryHistory base ∧ UnaryHistory derivative ∧
    UnaryHistory linear ∧ UnaryHistory matrix ∧ UnaryHistory picard ∧ UnaryHistory graph ∧
      UnaryHistory sealRow ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
        UnaryHistory provenance ∧ UnaryHistory localName ∧ Cont equation base derivative ∧
          Cont derivative linear matrix ∧ Cont matrix picard graph ∧
            Cont transport replay provenance ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle localName pkg

theorem ImplicitFunctionRootEquationCarrier [AskSetup] [PackageSetup]
    {equation base derivative linear matrix picard graph sealRow transport replay provenance
      localName graphRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ImplicitFunctionCarrier equation base derivative linear matrix picard graph sealRow transport
        replay provenance localName bundle pkg →
      Cont picard graph graphRead →
        PkgSig bundle graphRead pkg →
          UnaryHistory equation ∧ UnaryHistory base ∧ UnaryHistory derivative ∧
            UnaryHistory linear ∧ UnaryHistory matrix ∧ UnaryHistory picard ∧
              UnaryHistory graph ∧ UnaryHistory sealRow ∧ UnaryHistory graphRead ∧
                Cont equation base derivative ∧ Cont derivative linear matrix ∧
                  Cont matrix picard graph ∧ Cont picard graph graphRead ∧
                    PkgSig bundle localName pkg ∧ PkgSig bundle graphRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier picardGraphRead graphReadPkg
  obtain
    ⟨equationUnary, baseUnary, derivativeUnary, linearUnary, matrixUnary, picardUnary,
      graphUnary, sealUnary, _transportUnary, _replayUnary, _provenanceUnary,
      _localNameUnary, equationBaseDerivative, derivativeLinearMatrix, matrixPicardGraph,
      _transportReplayProvenance, _provenancePkg, localNamePkg⟩ := carrier
  have graphReadUnary : UnaryHistory graphRead :=
    unary_cont_closed picardUnary graphUnary picardGraphRead
  exact
    ⟨equationUnary, baseUnary, derivativeUnary, linearUnary, matrixUnary, picardUnary,
      graphUnary, sealUnary, graphReadUnary, equationBaseDerivative, derivativeLinearMatrix,
      matrixPicardGraph, picardGraphRead, localNamePkg, graphReadPkg⟩

theorem ImplicitFunctionLinearizationPicardRoute [AskSetup] [PackageSetup]
    {equation base derivative linear matrix picard graph sealRow transport replay provenance
      localName graphRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ImplicitFunctionCarrier equation base derivative linear matrix picard graph sealRow transport
        replay provenance localName bundle pkg →
      Cont picard graph graphRead →
        Cont graphRead sealRow sealRead →
          PkgSig bundle sealRead pkg →
            UnaryHistory derivative ∧ UnaryHistory linear ∧ UnaryHistory matrix ∧
              UnaryHistory picard ∧ UnaryHistory graph ∧ UnaryHistory graphRead ∧
                UnaryHistory sealRead ∧ Cont derivative linear matrix ∧
                  Cont matrix picard graph ∧ Cont picard graph graphRead ∧
                    Cont graphRead sealRow sealRead ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier picardGraphRead graphSealRead sealReadPkg
  obtain
    ⟨_equationUnary, _baseUnary, derivativeUnary, linearUnary, matrixUnary, picardUnary,
      graphUnary, sealUnary, _transportUnary, _replayUnary, _provenanceUnary,
      _localNameUnary, _equationBaseDerivative, derivativeLinearMatrix, matrixPicardGraph,
      _transportReplayProvenance, provenancePkg, _localNamePkg⟩ := carrier
  have graphReadUnary : UnaryHistory graphRead :=
    unary_cont_closed picardUnary graphUnary picardGraphRead
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed graphReadUnary sealUnary graphSealRead
  exact
    ⟨derivativeUnary, linearUnary, matrixUnary, picardUnary, graphUnary, graphReadUnary,
      sealReadUnary, derivativeLinearMatrix, matrixPicardGraph, picardGraphRead,
      graphSealRead, provenancePkg, sealReadPkg⟩

theorem ImplicitFunctionCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {equation base derivative linear matrix picard graph sealRow transport replay provenance
      localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ImplicitFunctionCarrier equation base derivative linear matrix picard graph sealRow transport
        replay provenance localName bundle pkg →
      SemanticNameCert
          (fun row : BHist => hsame row localName ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row equation ∨ hsame row derivative ∨ hsame row picard ∨
              hsame row graph ∨ hsame row sealRow ∨ hsame row localName)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame ∧
        UnaryHistory equation ∧ UnaryHistory derivative ∧ UnaryHistory graph ∧
          PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont SemanticNameCert hsame
  intro carrier
  obtain
    ⟨equationUnary, _baseUnary, derivativeUnary, _linearUnary, _matrixUnary, picardUnary,
      graphUnary, sealUnary, _transportUnary, _replayUnary, _provenanceUnary,
      localNameUnary, _equationBaseDerivative, _derivativeLinearMatrix, _matrixPicardGraph,
      _transportReplayProvenance, provenancePkg, localNamePkg⟩ := carrier
  have sourceLocalName :
      (fun row : BHist => hsame row localName ∧ UnaryHistory row) localName := by
    exact And.intro (hsame_refl localName) localNameUnary
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row localName ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row equation ∨ hsame row derivative ∨ hsame row picard ∨
              hsame row graph ∨ hsame row sealRow ∨ hsame row localName)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro localName sourceLocalName
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
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, equationUnary, derivativeUnary, graphUnary, provenancePkg, localNamePkg⟩

end BEDC.Derived.ImplicitFunctionUp
