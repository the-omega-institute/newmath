import BEDC.Derived.BishopRegularCauchyCompletionUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.BishopRegularCauchyCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BishopRegularCauchyCompletionFiniteWindowInduction [AskSetup] [PackageSetup]
    {endpoint stream regular dyadic window transport replay provenance localName windowRead
      sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BishopRegularCauchyCompletionCarrier endpoint stream regular dyadic window transport replay
        provenance localName bundle pkg →
      Cont stream window windowRead →
        Cont windowRead endpoint sealRead →
          PkgSig bundle sealRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row stream ∨ hsame row regular ∨ hsame row dyadic ∨
                    hsame row window ∨ hsame row sealRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont stream window windowRead ∧
                    Cont windowRead endpoint sealRead ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle sealRead pkg)
                hsame ∧
              UnaryHistory windowRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BishopRegularCauchyCompletionCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier streamWindow windowEndpoint sealPkg
  obtain ⟨endpointUnary, streamUnary, _regularUnary, _dyadicUnary, windowUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary, provenancePkg,
    _localNamePkg⟩ := carrier
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed streamUnary windowUnary streamWindow
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed windowReadUnary endpointUnary windowEndpoint
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row stream ∨ hsame row regular ∨ hsame row dyadic ∨
              hsame row window ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont stream window windowRead ∧
              Cont windowRead endpoint sealRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealReadUnary⟩
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
      exact ⟨source.right, streamWindow, windowEndpoint, provenancePkg, sealPkg⟩
  }
  exact ⟨cert, windowReadUnary, sealReadUnary⟩

end BEDC.Derived.BishopRegularCauchyCompletionUp
