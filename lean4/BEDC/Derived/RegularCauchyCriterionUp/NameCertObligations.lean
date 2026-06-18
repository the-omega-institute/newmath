import BEDC.Derived.RegularCauchyCriterionUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyCriterionCarrier_tail_transport [AskSetup] [PackageSetup]
    (K : RegularCauchyCriterionUp)
    {S R M D Q V A H C P N streamRead criterionRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    regularCauchyCriterionFields K = [S, R, M, D, Q, V, A, H, C, P, N] →
      UnaryHistory S →
        UnaryHistory R →
          UnaryHistory M →
            UnaryHistory D →
              UnaryHistory Q →
                UnaryHistory V →
                  UnaryHistory A →
                    Cont S R streamRead →
                      Cont M D criterionRead →
                        Cont Q V realRead →
                          PkgSig bundle P pkg →
                            UnaryHistory streamRead ∧ UnaryHistory criterionRead ∧
                              UnaryHistory realRead ∧ Cont S R streamRead ∧
                                Cont M D criterionRead ∧ Cont Q V realRead ∧
                                  PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory ProbeBundle
  intro fieldRows streamUnary readbackUnary modulusUnary dyadicUnary criterionUnary
    convergenceUnary _realBoundaryUnary streamRoute criterionRoute realRoute provenancePkg
  cases K with
  | mk _stream _readback _modulus _dyadic _criterion _convergence _realBoundary
      _transport _replay _provenance _localName =>
      change
        [_stream, _readback, _modulus, _dyadic, _criterion, _convergence, _realBoundary,
          _transport, _replay, _provenance, _localName] =
          [S, R, M, D, Q, V, A, H, C, P, N] at fieldRows
      have streamReadUnary : UnaryHistory streamRead :=
        unary_cont_closed streamUnary readbackUnary streamRoute
      have criterionReadUnary : UnaryHistory criterionRead :=
        unary_cont_closed modulusUnary dyadicUnary criterionRoute
      have realReadUnary : UnaryHistory realRead :=
        unary_cont_closed criterionUnary convergenceUnary realRoute
      exact
        ⟨streamReadUnary, criterionReadUnary, realReadUnary, streamRoute, criterionRoute,
          realRoute, provenancePkg⟩

def RegularCauchyCriterionRouteCarrier [AskSetup] [PackageSetup]
    (stream readback modulus dyadic criterion convergence realBoundary transport replay provenance
      localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory PkgSig
  UnaryHistory stream ∧ UnaryHistory readback ∧ UnaryHistory modulus ∧
    UnaryHistory dyadic ∧ UnaryHistory criterion ∧ UnaryHistory convergence ∧
      UnaryHistory realBoundary ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
        UnaryHistory provenance ∧ UnaryHistory localName ∧ PkgSig bundle provenance pkg ∧
          PkgSig bundle localName pkg

theorem RegularCauchyCriterionCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {stream readback modulus dyadic criterion convergence realBoundary transport replay provenance
      localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyCriterionRouteCarrier stream readback modulus dyadic criterion convergence
        realBoundary transport replay provenance localName bundle pkg →
      SemanticNameCert
          (fun row : BHist => hsame row localName ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row stream ∨ hsame row readback ∨ hsame row modulus ∨
              hsame row dyadic ∨ hsame row criterion ∨ hsame row convergence ∨
                hsame row realBoundary ∨ hsame row localName)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame ∧
        PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory PkgSig hsame SemanticNameCert
  intro carrier
  obtain ⟨_streamUnary, _readbackUnary, _modulusUnary, _dyadicUnary, _criterionUnary,
    _convergenceUnary, _realBoundaryUnary, _transportUnary, _replayUnary, _provenanceUnary,
    localNameUnary, provenancePkg, localNamePkg⟩ := carrier
  have localSource :
      (fun row : BHist => hsame row localName ∧ UnaryHistory row) localName := by
    exact ⟨hsame_refl localName, localNameUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row localName ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row stream ∨ hsame row readback ∨ hsame row modulus ∨
              hsame row dyadic ∨ hsame row criterion ∨ hsame row convergence ∨
                hsame row realBoundary ∨ hsame row localName)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro localName localSource
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, provenancePkg, localNamePkg⟩

end BEDC.Derived.RegularCauchyCriterionUp
